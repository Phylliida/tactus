//! Client for the persistent Lean driver (`driver/TactusDriver.lean`).
//!
//! One driver process holds an `importModules` environment (~1s to
//! build) and elaborates each module file against a fresh branch of it
//! (~ms) — versus ~2s per file for a fresh `lean` process. See
//! DESIGN-lean-driver.md for the measured numbers and the olean/Link
//! trust argument.
//!
//! Shape: a global pool of clients (drivers hold snapshots in-process,
//! so clients are shared, not per-thread). `prime_for_crate` — called
//! once per crate before the per-fn worker pool — builds all stmt
//! oleans through one driver, then establishes the WIDE snapshot
//! (defs + every stmt module) on `workers` drivers in parallel. Per-fn
//! checks then route through `try_check`: a file whose header imports
//! are a subset of a client's snapshot modules elaborates as a branch;
//! anything else returns `None` and the caller uses the ordinary
//! process-per-file path. Any driver failure (spawn, protocol, crash)
//! permanently disables routing for the run — correctness never
//! depends on the driver, only speed.
//!
//! Gate: OPT-IN via `TACTUS_DRIVER=1`. Measured on current crates the
//! driver is a large CPU win (-60..85%) but wall-neutral-to-negative
//! (tactus-core -3s; gt +26s — its snapshots import the 107-part defs
//! closure, and its per-fn lean mass is small). Wall-bound daily gates
//! keep the process path; CPU-bound contexts (thermals, shared boxes,
//! low-core machines where CPU IS wall) opt in.

use std::collections::HashMap;
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Mutex, OnceLock};

use crate::lean_process::{LeanDiagnostic, LeanPos, LeanResult};

const DRIVER_SOURCE: &str = include_str!("../driver/TactusDriver.lean");

static DISABLED: AtomicBool = AtomicBool::new(false);

fn env_enabled() -> bool {
    match std::env::var("TACTUS_DRIVER") {
        Ok(v) => v == "1" || v.eq_ignore_ascii_case("on"),
        Err(_) => false,
    }
}

pub fn enabled() -> bool {
    static ENV: OnceLock<bool> = OnceLock::new();
    *ENV.get_or_init(env_enabled) && !DISABLED.load(Ordering::Relaxed)
}

/// Disable driver routing for the rest of the run (after a fault).
/// The fault itself was already handled by falling back; this just
/// stops us from re-trying a broken driver on every file.
fn disable(reason: &str) {
    if !DISABLED.swap(true, Ordering::Relaxed) {
        eprintln!("tactus: lean driver disabled for this run ({reason}); \
                   falling back to process-per-file");
    }
}

/// Write the embedded driver source into the cache, content-addressed
/// so a rebuilt verus with a changed driver never reuses a stale file.
fn driver_script_path() -> Result<PathBuf, String> {
    static PATH: OnceLock<Result<PathBuf, String>> = OnceLock::new();
    PATH.get_or_init(|| {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        DRIVER_SOURCE.hash(&mut h);
        let dir = crate::prelude::cache_root()
            .join(format!("driver-{:016x}", h.finish()));
        let path = dir.join("TactusDriver.lean");
        if !path.exists() {
            std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
            let tmp = dir.join(format!("TactusDriver.lean.tmp.{}", std::process::id()));
            std::fs::write(&tmp, DRIVER_SOURCE).map_err(|e| e.to_string())?;
            let _ = std::fs::rename(&tmp, &path);
        }
        Ok(path)
    }).clone()
}

struct DriverClient {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    /// Established snapshots: key → module set.
    snapshots: HashMap<String, Vec<String>>,
    /// The LEAN_PATH this driver was spawned with (snapshots resolve
    /// imports against it; a different path needs a different driver).
    lean_path: String,
}

impl Drop for DriverClient {
    fn drop(&mut self) {
        let _ = self.stdin.write_all(b"{\"op\":\"exit\"}\n");
        let _ = self.stdin.flush();
        let _ = self.child.wait();
    }
}

impl DriverClient {
    fn spawn(lean_path: &str) -> Result<DriverClient, String> {
        let script = driver_script_path()?;
        let mut child = Command::new("lean")
            .arg("--run")
            .arg(&script)
            .env("LEAN_PATH", lean_path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("failed to spawn lean driver: {e}"))?;
        let stdin = child.stdin.take().expect("piped stdin");
        let mut stdout = BufReader::new(child.stdout.take().expect("piped stdout"));
        let mut ready = String::new();
        stdout.read_line(&mut ready).map_err(|e| format!("driver handshake: {e}"))?;
        if !ready.contains("\"ready\":true") {
            let _ = child.kill();
            return Err(format!("driver handshake failed: {}", ready.trim()));
        }
        Ok(DriverClient {
            child, stdin, stdout,
            snapshots: HashMap::new(),
            lean_path: lean_path.to_string(),
        })
    }

    fn request(&mut self, req: &serde_json::Value) -> Result<serde_json::Value, String> {
        let line = serde_json::to_string(req).map_err(|e| e.to_string())?;
        self.stdin.write_all(line.as_bytes()).map_err(|e| format!("driver write: {e}"))?;
        self.stdin.write_all(b"\n").map_err(|e| format!("driver write: {e}"))?;
        self.stdin.flush().map_err(|e| format!("driver flush: {e}"))?;
        let mut reply = String::new();
        self.stdout.read_line(&mut reply).map_err(|e| format!("driver read: {e}"))?;
        if reply.trim().is_empty() {
            return Err("driver closed its stdout".to_string());
        }
        let v: serde_json::Value =
            serde_json::from_str(reply.trim()).map_err(|e| format!("driver reply: {e}"))?;
        if let Some(f) = v.get("fatal").and_then(|f| f.as_str()) {
            return Err(format!("driver fatal: {f}"));
        }
        Ok(v)
    }

    fn snapshot(&mut self, key: &str, modules: &[String]) -> Result<(), String> {
        let v = self.request(&serde_json::json!({
            "op": "snapshot", "key": key, "modules": modules,
        }))?;
        if v.get("ok").and_then(|b| b.as_bool()) != Some(true) {
            return Err("driver snapshot failed".to_string());
        }
        self.snapshots.insert(key.to_string(), modules.to_vec());
        Ok(())
    }

    /// Key of the SMALLEST established snapshot whose module set ⊇
    /// `imports` (ties broken by key). Smallest matters for olean
    /// writes: `writeModule` records the snapshot's modules as the
    /// olean's imports, so a stmt file elaborated against the wide
    /// snapshot would record an import of ITSELF. Minimal-set choice
    /// keeps stmt oleans on the base snapshot; it is also
    /// deterministic where plain map iteration would not be.
    fn covering_snapshot(&self, imports: &[String]) -> Option<&str> {
        self.snapshots.iter()
            .filter(|(_, mods)| imports.iter().all(|i| mods.contains(i)))
            .min_by_key(|(k, mods)| (mods.len(), k.as_str()))
            .map(|(k, _)| k.as_str())
    }

    fn check(
        &mut self,
        snapshot: &str,
        file: &Path,
        module: &str,
        olean: Option<&Path>,
    ) -> Result<LeanResult, String> {
        let mut req = serde_json::json!({
            "op": "check", "snapshot": snapshot,
            "file": file.to_string_lossy(), "module": module,
        });
        if let Some(o) = olean {
            req["olean"] = serde_json::Value::String(o.to_string_lossy().into_owned());
        }
        let v = self.request(&req)?;
        let ok = v.get("ok").and_then(|b| b.as_bool()).unwrap_or(false);
        let diagnostics: Vec<LeanDiagnostic> = v.get("diags")
            .and_then(|d| d.as_array())
            .map(|ds| ds.iter().filter_map(diag_from_json).collect())
            .unwrap_or_default();
        Ok(LeanResult { success: ok, diagnostics })
    }
}

fn diag_from_json(d: &serde_json::Value) -> Option<LeanDiagnostic> {
    Some(LeanDiagnostic {
        severity: d.get("sev")?.as_str()?.to_string(),
        pos: Some(LeanPos {
            line: d.get("line")?.as_u64()? as usize,
            column: d.get("col")?.as_u64()? as usize,
        }),
        end_pos: None,
        data: d.get("msg")?.as_str()?.to_string(),
    })
}

/// The global client pool. Clients are checked out for the duration of
/// one `check` call, so `workers` clients support `workers`-way
/// parallelism without holding a lock across an elaboration.
static POOL: Mutex<Vec<DriverClient>> = Mutex::new(Vec::new());

fn checkout(lean_path: &str, imports: &[String]) -> Option<DriverClient> {
    let mut pool = POOL.lock().unwrap();
    let idx = pool.iter().position(|c| {
        c.lean_path == lean_path && c.covering_snapshot(imports).is_some()
    })?;
    Some(pool.swap_remove(idx))
}

fn checkin(client: DriverClient) {
    POOL.lock().unwrap().push(client);
}

/// Parse the leading `import X` lines of an emitted module file.
fn header_imports(file: &Path) -> Option<Vec<String>> {
    let src = std::fs::read_to_string(file).ok()?;
    let mut imports = Vec::new();
    for line in src.lines() {
        let t = line.trim();
        if let Some(m) = t.strip_prefix("import ") {
            imports.push(m.trim().to_string());
        } else if t.is_empty() || t.starts_with("--") {
            continue;
        } else {
            break;
        }
    }
    Some(imports)
}

/// Spawn `workers` drivers on `lean_path` and establish the base
/// snapshot (`base_modules`) on each. Returns false (and disables
/// routing) on any failure. Boots run concurrently — the ~1.5s
/// process + script-compile cost overlaps instead of serializing.
pub fn spawn_pool(lean_path: &str, workers: usize, base_modules: &[String]) -> bool {
    if !enabled() {
        return false;
    }
    let spawned: Vec<Result<DriverClient, String>> = std::thread::scope(|scope| {
        (0..workers.max(1))
            .map(|_| scope.spawn(|| {
                let mut c = DriverClient::spawn(lean_path)?;
                c.snapshot("base", base_modules)?;
                Ok(c)
            }))
            .collect::<Vec<_>>()
            .into_iter()
            .map(|h| h.join().unwrap_or_else(|_| Err("driver spawn panicked".into())))
            .collect()
    });
    let mut clients = Vec::new();
    for s in spawned {
        match s {
            Ok(c) => clients.push(c),
            Err(e) => {
                disable(&e);
                return false;
            }
        }
    }
    let mut pool = POOL.lock().unwrap();
    pool.clear();
    pool.extend(clients);
    true
}

/// Establish `key` → `modules` on every pooled driver, in parallel.
/// Any failure disables routing (partially-primed pools would give
/// some checks the fast path and silently starve the rest).
pub fn add_snapshot_all(key: &str, modules: &[String]) {
    if !enabled() {
        return;
    }
    let mut clients: Vec<DriverClient> = std::mem::take(&mut *POOL.lock().unwrap());
    let results: Vec<Result<(), String>> = std::thread::scope(|scope| {
        clients.iter_mut()
            .map(|c| scope.spawn(move || c.snapshot(key, modules)))
            .collect::<Vec<_>>()
            .into_iter()
            .map(|h| h.join().unwrap_or_else(|_| Err("driver thread panicked".into())))
            .collect()
    });
    if let Some(Err(e)) = results.into_iter().find(|r| r.is_err()) {
        disable(&e);
        return;
    }
    POOL.lock().unwrap().extend(clients);
}

/// Route one module check through the driver pool if possible.
/// `None` means "not routable" — caller runs the ordinary process.
/// `Some(Err(_))` is a driver fault: routing is disabled and the
/// caller ALSO falls back (the error is advisory).
pub fn try_check(
    dir: &Path,
    module: &str,
    produce_olean: bool,
    lean_path_merged: &str,
) -> Option<LeanResult> {
    if !enabled() {
        return None;
    }
    let file = dir.join(format!("{module}.lean"));
    let imports = header_imports(&file)?;
    if imports.is_empty() {
        return None;
    }
    let mut client = checkout(lean_path_merged, &imports)?;
    let snap = client.covering_snapshot(&imports)?.to_string();
    let olean = produce_olean.then(|| dir.join(format!("{module}.olean")));
    match client.check(&snap, &file, module, olean.as_deref()) {
        Ok(r) => {
            checkin(client);
            Some(r)
        }
        Err(e) => {
            // Client is in an unknown state: drop it (kills the
            // process) rather than returning it to the pool.
            drop(client);
            disable(&e);
            None
        }
    }
}

/// Tear down the pool (end of run). Drop sends `exit` to each driver.
pub fn shutdown() {
    POOL.lock().unwrap().clear();
}
