//! tactus-lsp — warm persistent goal server for Tactus (see ../SERVER.md).
//!
//! Turns the proven `server-spike/goal_at_cursor.py` bridge into a real,
//! persistent server: it spawns ONE `lean --server`, keeps it hot (each `.lean`
//! is opened/elaborated at most once), and answers repeated `.rs`-cursor → Lean
//! -goal queries. The win over the per-query Python bridge: the first query to a
//! file pays the open/elaboration cost; every subsequent query is a single
//! plainGoal round-trip — interactive speed, no rustc, no re-spawn.
//!
//! Built on the `--emit-lean` sidecar (`sourcemap.json`). Proof fns today;
//! exec fns (coarser `span_marks`) are a later pass.
//!
//! Modes:
//!   tactus-lsp goal  <sourcemap.json> <file.rs> <line> <col>   # one-shot
//!   tactus-lsp serve <sourcemap.json> <file.rs>                # persistent;
//!         reads `<line> <col>` queries (0-indexed, LSP) from stdin, one per
//!         line, and prints the goal + timing — demonstrating warm = fast.
//!
//! LEAN_PATH resolves from $LEAN_PATH, else `lake env printenv LEAN_PATH` in
//! $TACTUS_LEAN_PROJECT (or ../lean-project relative to CWD).

use std::collections::HashMap;
use std::io::{BufRead, BufReader, Read, Write};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{channel, Receiver};
use std::time::{Duration, Instant};

use serde::Deserialize;
use serde_json::{json, Value};

// ---------------------------------------------------------------------------
// Sidecar schema (mirrors `lean_verify::sourcemap`, the `--emit-lean` output).
// ---------------------------------------------------------------------------

#[derive(Deserialize)]
struct Sidecar {
    #[allow(dead_code)]
    crate_name: String,
    fns: Vec<SidecarFn>,
}

#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum SidecarFn {
    Proof {
        name: String,
        lean_file: String,
        rs_tactic_byte_range: [usize; 2],
        lean_tactic_start_line: usize,
        #[allow(dead_code)]
        lean_tactic_line_count: usize,
    },
    Exec {
        #[allow(dead_code)]
        name: String,
        #[allow(dead_code)]
        lean_file: String,
        #[allow(dead_code)]
        span_marks: Vec<Value>,
    },
}

// ---------------------------------------------------------------------------
// A `lean --server` client kept warm: spawn once, open files lazily, query.
// ---------------------------------------------------------------------------

/// In-memory mirror of an open `.lean`: its current lines + LSP version. The
/// splice fast path edits `lines`, bumps `version`, and `didChange`s — so a
/// `.rs` tactic edit re-elaborates live without rustc and without re-`didOpen`.
struct FileState {
    version: i64,
    lines: Vec<String>,
}

struct LeanServer {
    child: Child,
    stdin: ChildStdin,
    rx: Receiver<Value>,
    next_id: i64,
    files: HashMap<String, FileState>,
}

impl LeanServer {
    fn spawn(lean_path: &str) -> std::io::Result<LeanServer> {
        let mut child = Command::new("lean")
            .arg("--server")
            .env("LEAN_PATH", lean_path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()?;
        let stdin = child.stdin.take().unwrap();
        let stdout = child.stdout.take().unwrap();
        let (tx, rx) = channel::<Value>();
        // Reader thread: parse Content-Length-framed JSON-RPC, forward each
        // message (responses + notifications) to the channel.
        std::thread::spawn(move || {
            let mut reader = BufReader::new(stdout);
            loop {
                let mut content_length = 0usize;
                loop {
                    let mut line = String::new();
                    match reader.read_line(&mut line) {
                        Ok(0) | Err(_) => return,
                        Ok(_) => {}
                    }
                    let line = line.trim_end();
                    if line.is_empty() {
                        break;
                    }
                    if let Some(v) = line.strip_prefix("Content-Length:") {
                        content_length = v.trim().parse().unwrap_or(0);
                    }
                }
                let mut buf = vec![0u8; content_length];
                if reader.read_exact(&mut buf).is_err() {
                    return;
                }
                match serde_json::from_slice::<Value>(&buf) {
                    Ok(v) => {
                        if tx.send(v).is_err() {
                            return;
                        }
                    }
                    Err(_) => {}
                }
            }
        });
        Ok(LeanServer { child, stdin, rx, next_id: 1, files: HashMap::new() })
    }

    fn send(&mut self, msg: &Value) {
        let body = serde_json::to_vec(msg).unwrap();
        let _ = self
            .stdin
            .write_all(format!("Content-Length: {}\r\n\r\n", body.len()).as_bytes());
        let _ = self.stdin.write_all(&body);
        let _ = self.stdin.flush();
    }

    fn notify(&mut self, method: &str, params: Value) {
        self.send(&json!({"jsonrpc": "2.0", "method": method, "params": params}));
    }

    /// Send a request, drain messages until its response arrives (dropping
    /// interleaved notifications). Returns None on timeout.
    fn request(&mut self, method: &str, params: Value, timeout: Duration) -> Option<Value> {
        let id = self.next_id;
        self.next_id += 1;
        self.send(&json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params}));
        let deadline = Instant::now() + timeout;
        loop {
            let remaining = deadline.checked_duration_since(Instant::now())?;
            match self.rx.recv_timeout(remaining) {
                Ok(v) => {
                    if v.get("id").and_then(|i| i.as_i64()) == Some(id) {
                        return Some(v);
                    }
                }
                Err(_) => return None,
            }
        }
    }

    fn initialize(&mut self, root_uri: &str) {
        self.request(
            "initialize",
            json!({
                "processId": std::process::id(),
                "rootUri": root_uri,
                "capabilities": {},
                "initializationOptions": {},
            }),
            Duration::from_secs(30),
        );
        self.notify("initialized", json!({}));
    }

    /// Open a `.lean` and block until it is fully elaborated. Idempotent —
    /// a file already open returns immediately (the warmth).
    fn ensure_open(&mut self, path: &str) -> std::io::Result<()> {
        if self.files.contains_key(path) {
            return Ok(());
        }
        let text = std::fs::read_to_string(path)?;
        let uri = file_uri(path);
        self.notify(
            "textDocument/didOpen",
            json!({"textDocument": {"uri": uri, "languageId": "lean", "version": 1, "text": text}}),
        );
        self.wait_processed(Duration::from_secs(180));
        self.files.insert(
            path.to_string(),
            FileState { version: 1, lines: text.split('\n').map(|s| s.to_string()).collect() },
        );
        Ok(())
    }

    fn is_open(&self, path: &str) -> bool {
        self.files.contains_key(path)
    }

    /// Replace the open `.lean`'s text and `didChange` it. No-op (returns false)
    /// if the text is unchanged. We do NOT wait for re-elaboration here: a
    /// subsequent `$/lean/plainGoal` against the new document version blocks
    /// until that position is elaborated, so the query itself is the barrier.
    fn did_change(&mut self, path: &str, new_lines: Vec<String>) -> bool {
        let Some(fs) = self.files.get_mut(path) else {
            return false;
        };
        if fs.lines == new_lines {
            return false;
        }
        fs.version += 1;
        fs.lines = new_lines;
        let version = fs.version;
        let text = fs.lines.join("\n");
        let uri = file_uri(path);
        self.notify(
            "textDocument/didChange",
            json!({
                "textDocument": {"uri": uri, "version": version},
                "contentChanges": [{"text": text}],
            }),
        );
        true
    }

    /// Wait until `lean --server` has finished (re)elaborating the file.
    ///
    /// Two completion signals, whichever fires first — because `$/lean/fileProgress`
    /// is very chatty (its `processing` set bounces around and, especially after a
    /// `didChange`, often never cleanly reports empty before more workspace churn):
    ///   1. a `fileProgress` with empty `processing` after a non-empty one (clean idle), or
    ///   2. **quiescence** — once activity has started, no message at all for `QUIET`.
    fn wait_processed(&mut self, timeout: Duration) {
        use std::sync::mpsc::RecvTimeoutError;
        const QUIET: Duration = Duration::from_millis(500);
        let deadline = Instant::now() + timeout;
        let mut saw = false;
        loop {
            let remaining = match deadline.checked_duration_since(Instant::now()) {
                Some(r) => r.min(QUIET),
                None => return,
            };
            match self.rx.recv_timeout(remaining) {
                Ok(v) => {
                    if v.get("method").and_then(|m| m.as_str()) == Some("$/lean/fileProgress") {
                        match v.pointer("/params/processing").and_then(|p| p.as_array()) {
                            Some(a) if !a.is_empty() => saw = true,
                            Some(_) if saw => return,
                            _ => {}
                        }
                    }
                }
                // No message for QUIET: if elaboration has started and gone quiet,
                // it has settled. (If nothing has started yet, keep waiting.)
                Err(RecvTimeoutError::Timeout) => {
                    if saw {
                        return;
                    }
                }
                Err(RecvTimeoutError::Disconnected) => return,
            }
        }
    }

    fn plain_goal(&mut self, path: &str, line: usize, col: usize) -> Option<String> {
        let uri = file_uri(path);
        // 60s ceiling: plainGoal blocks until this position is elaborated, so an
        // edit to a slow tactic re-elaborates before the goal returns (like the
        // real Lean infoview). This IS the barrier — no separate wait needed.
        let resp = self.request(
            "$/lean/plainGoal",
            json!({"textDocument": {"uri": uri}, "position": {"line": line, "character": col}}),
            Duration::from_secs(60),
        )?;
        resp.pointer("/result/rendered")
            .and_then(|r| r.as_str())
            .map(|s| s.to_string())
    }

    /// The splice fast path: replace `lean_file`'s tactic body (the lines from
    /// `lean_start` up to the `end <ns>` boundary) with the live `.rs` body
    /// (dedented + re-indented to match `--emit-lean`), `didChange`, then query
    /// the goal at the `.lean` line whose text matches `cursor_text`
    /// (content-anchored — robust to the body growing/shrinking). Returns
    /// `(goal, lean_line, lean_col)`.
    fn splice_and_query(
        &mut self,
        lean_file: &str,
        lean_start: usize,
        raw_body: &str,
        cursor_text: &str,
    ) -> (Option<String>, usize, usize) {
        if self.ensure_open(lean_file).is_err() {
            return (None, 0, 0);
        }
        let cur = self.files[lean_file].lines.clone();
        let lean_start = lean_start.min(cur.len());
        let suffix_start = (lean_start..cur.len())
            .find(|&i| cur[i].trim_start().starts_with("end "))
            .unwrap_or(cur.len());
        let new_body = transform_body(raw_body);
        let mut new_lines: Vec<String> = cur[..lean_start].to_vec();
        new_lines.extend(new_body.iter().cloned());
        new_lines.extend(cur[suffix_start..].iter().cloned());
        self.did_change(lean_file, new_lines);

        // Content-anchor the query to the cursor's line inside the new body.
        let body_end = (lean_start + new_body.len()).min(self.files[lean_file].lines.len());
        let target = cursor_text.trim();
        let updated = &self.files[lean_file].lines;
        let qline = (lean_start..body_end)
            .find(|&i| updated[i].trim() == target && !target.is_empty())
            .unwrap_or(lean_start);
        let qcol = updated
            .get(qline)
            .map(|l| l.len() - l.trim_start().len())
            .unwrap_or(0);
        let goal = self.plain_goal(lean_file, qline, qcol);
        (goal, qline, qcol)
    }

    fn shutdown(&mut self) {
        self.request("shutdown", Value::Null, Duration::from_secs(3));
        self.notify("exit", Value::Null);
        let _ = self.child.kill();
    }
}

// ---------------------------------------------------------------------------
// Position mapping (content-anchored; proof fns).
// ---------------------------------------------------------------------------

fn byte_offset_of(rs: &str, line: usize, col: usize) -> usize {
    let mut off = 0usize;
    for (i, l) in rs.split('\n').enumerate() {
        if i == line {
            return off + col.min(l.len());
        }
        off += l.len() + 1;
    }
    off
}

fn line_of_byte(rs: &str, byte: usize) -> usize {
    rs.as_bytes()[..byte.min(rs.len())]
        .iter()
        .filter(|&&b| b == b'\n')
        .count()
}

/// Transform a raw `.rs` tactic body (the text between `by {` and `}`) into the
/// `.lean` body lines — mirroring `--emit-lean`: dedent by the common leading
/// whitespace, strip leading/trailing blank lines, re-indent each line by 2
/// spaces (`render_by_block`). So a spliced edit matches what a re-emit would
/// have produced.
fn transform_body(raw: &str) -> Vec<String> {
    let lines: Vec<&str> = raw.split('\n').collect();
    let indent = lines
        .iter()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.len() - l.trim_start().len())
        .min()
        .unwrap_or(0);
    let dedented: Vec<String> = lines
        .iter()
        .map(|l| {
            if l.trim().is_empty() {
                String::new()
            } else {
                l.chars().skip(indent).collect()
            }
        })
        .collect();
    let start = dedented.iter().position(|l| !l.trim().is_empty()).unwrap_or(0);
    let end = dedented
        .iter()
        .rposition(|l| !l.trim().is_empty())
        .map(|i| i + 1)
        .unwrap_or(start);
    dedented[start..end.max(start)]
        .iter()
        .map(|l| if l.is_empty() { String::new() } else { format!("  {}", l) })
        .collect()
}

/// For a proof fn, find the constant delta D such that lean_line = rs_line + D,
/// by matching `lean_tactic_start_line`'s text to the `.rs` body line (the body
/// is copied verbatim line-for-line). Robust to leading blanks / dedent.
fn line_delta(rs: &str, s: usize, e: usize, lean_start: usize, lean_text: &str) -> Option<isize> {
    let lean_lines: Vec<&str> = lean_text.split('\n').collect();
    let anchor = lean_lines.get(lean_start)?.trim();
    if anchor.is_empty() {
        return None;
    }
    let first = line_of_byte(rs, s);
    let last = line_of_byte(rs, e.saturating_sub(1).max(s));
    let rs_lines: Vec<&str> = rs.split('\n').collect();
    for rl in first..=last.min(rs_lines.len().saturating_sub(1)) {
        if rs_lines[rl].trim() == anchor {
            return Some(lean_start as isize - rl as isize);
        }
    }
    None
}

/// Resolve a `.rs` cursor to the `.lean` (file, line, col) for the proof fn
/// whose tactic block contains it. Column = the `.lean` tactic line's first
/// non-space col (plainGoal "state here").
fn resolve_cursor<'a>(
    sidecar: &'a Sidecar,
    rs: &str,
    line: usize,
    col: usize,
) -> Result<(&'a str, &'a str, usize, usize), String> {
    let cursor = byte_offset_of(rs, line, col);
    for f in &sidecar.fns {
        if let SidecarFn::Proof { name, lean_file, rs_tactic_byte_range: [s, e], lean_tactic_start_line, .. } = f {
            if cursor >= *s && cursor < *e {
                let lean_text = std::fs::read_to_string(lean_file)
                    .map_err(|err| format!("cannot read {}: {}", lean_file, err))?;
                let delta = line_delta(rs, *s, *e, *lean_tactic_start_line, &lean_text)
                    .ok_or("could not anchor the .rs↔.lean line map")?;
                let lean_line = (line as isize + delta).max(0) as usize;
                let lcol = lean_text
                    .split('\n')
                    .nth(lean_line)
                    .map(|l| l.len() - l.trim_start().len())
                    .unwrap_or(0);
                return Ok((name.as_str(), lean_file.as_str(), lean_line, lcol));
            }
        }
    }
    Err(format!(
        "cursor {}:{} (byte {}) is not inside any proof fn tactic block",
        line, col, cursor
    ))
}

// ---------------------------------------------------------------------------
// Helpers + main.
// ---------------------------------------------------------------------------

/// Print one compact JSON object and flush — the machine interface the VS Code
/// extension reads (one object per line over the server's stdout pipe).
fn emit_json(v: &Value) {
    println!("{}", v);
    let _ = std::io::stdout().flush();
}

fn file_uri(path: &str) -> String {
    let abs = std::fs::canonicalize(path)
        .map(|p| p.to_string_lossy().into_owned())
        .unwrap_or_else(|_| path.to_string());
    format!("file://{}", abs)
}

fn resolve_lean_path() -> String {
    if let Ok(p) = std::env::var("LEAN_PATH") {
        if !p.is_empty() {
            return p;
        }
    }
    let proj = std::env::var("TACTUS_LEAN_PROJECT").unwrap_or_else(|_| "../lean-project".into());
    let out = Command::new("lake")
        .args(["env", "printenv", "LEAN_PATH"])
        .current_dir(&proj)
        .output()
        .unwrap_or_else(|e| {
            eprintln!("failed to run `lake env printenv LEAN_PATH` in {}: {}", proj, e);
            std::process::exit(1);
        });
    let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if s.is_empty() {
        eprintln!("LEAN_PATH empty; set $LEAN_PATH or $TACTUS_LEAN_PROJECT");
        std::process::exit(1);
    }
    s
}

fn load(sidecar_path: &str, rs_path: &str) -> (Sidecar, String) {
    let sidecar: Sidecar = serde_json::from_str(
        &std::fs::read_to_string(sidecar_path).expect("read sidecar"),
    )
    .expect("parse sidecar");
    let rs = std::fs::read_to_string(rs_path).expect("read .rs");
    (sidecar, rs)
}

fn root_uri_for(lean_file: &str) -> String {
    let dir = std::path::Path::new(lean_file)
        .parent()
        .map(|p| p.to_string_lossy().into_owned())
        .unwrap_or_else(|| ".".into());
    file_uri(&dir)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(|s| s.as_str()) {
        Some("goal") if args.len() == 6 => {
            let (sidecar, rs) = load(&args[2], &args[3]);
            let line: usize = args[4].parse().expect("line");
            let col: usize = args[5].parse().expect("col");
            let (name, lean_file, lline, lcol) = match resolve_cursor(&sidecar, &rs, line, col) {
                Ok(t) => t,
                Err(e) => {
                    eprintln!("{}", e);
                    std::process::exit(1);
                }
            };
            let mut srv = LeanServer::spawn(&resolve_lean_path()).expect("spawn lean --server");
            srv.initialize(&root_uri_for(lean_file));
            srv.ensure_open(lean_file).expect("open .lean");
            let goal = srv.plain_goal(lean_file, lline, lcol);
            srv.shutdown();
            eprintln!("(fn {}, {}:{}:{})", name, lean_file, lline, lcol);
            println!("{}", goal.unwrap_or_else(|| "(no goal)".into()));
        }
        Some("serve") if args.len() == 5 && args[2] == "--json" => serve(&args[3], &args[4], true),
        Some("serve") if args.len() == 4 => serve(&args[2], &args[3], false),
        _ => {
            eprintln!(
                "usage:\n  tactus-lsp goal  <sourcemap.json> <file.rs> <line> <col>\n  \
                 tactus-lsp serve [--json] <sourcemap.json> <file.rs>\n      \
                 (then `<line> <col>` per stdin line; --json emits one JSON object per query)"
            );
            std::process::exit(2);
        }
    }
}

/// Persistent mode: keep `lean --server` warm; answer `<line> <col>` queries
/// from stdin. The first query to a given `.lean` pays the open/elaboration
/// cost; subsequent queries (same file) are a single plainGoal round-trip.
///
/// `json = true` emits one JSON object per query on stdout (the machine
/// interface the VS Code extension consumes) — banners stay on stderr.
fn serve(sidecar_path: &str, rs_path: &str, json: bool) {
    let (sidecar, rs) = load(sidecar_path, rs_path);
    // root for initialize: parent of the first fn's .lean (no lakefile there →
    // LEAN_PATH resolves Mathlib, as the de-risk spike proved).
    let any_lean = sidecar.fns.iter().find_map(|f| match f {
        SidecarFn::Proof { lean_file, .. } => Some(lean_file.clone()),
        _ => None,
    });
    let mut srv = LeanServer::spawn(&resolve_lean_path()).expect("spawn lean --server");
    if let Some(lf) = &any_lean {
        srv.initialize(&root_uri_for(lf));
    }
    eprintln!("tactus-lsp: warm. Enter `<line> <col>` (0-indexed) per line; Ctrl-D to quit.");

    let stdin = std::io::stdin();
    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }

        // `--json`: a JSON object — a splice command `{fn, body, cursor}` (the
        // live-edit fast path) or a plain query `{line, col}` (snapshot).
        if json && trimmed.starts_with('{') {
            let cmd: Value = match serde_json::from_str(trimmed) {
                Ok(v) => v,
                Err(e) => {
                    emit_json(&json!({"error": format!("bad JSON: {}", e)}));
                    continue;
                }
            };
            if let (Some(fname), Some(body)) = (
                cmd.get("fn").and_then(|v| v.as_str()),
                cmd.get("body").and_then(|v| v.as_str()),
            ) {
                let cursor_text = cmd.get("cursor").and_then(|v| v.as_str()).unwrap_or("");
                let info = sidecar.fns.iter().find_map(|f| match f {
                    SidecarFn::Proof { name, lean_file, lean_tactic_start_line, .. }
                        if name == fname =>
                    {
                        Some((lean_file.clone(), *lean_tactic_start_line))
                    }
                    _ => None,
                });
                let Some((lean_file, lean_start)) = info else {
                    emit_json(&json!({"fn": fname, "error": "no such proof fn in sidecar"}));
                    continue;
                };
                let t = Instant::now();
                let warm = srv.is_open(&lean_file);
                let (goal, qline, qcol) =
                    srv.splice_and_query(&lean_file, lean_start, body, cursor_text);
                emit_json(&json!({
                    "fn": fname, "lean_file": lean_file, "lean_line": qline, "lean_col": qcol,
                    "warm": warm, "ms": t.elapsed().as_millis() as u64, "goal": goal,
                }));
                continue;
            }
            if let (Some(l), Some(c)) = (
                cmd.get("line").and_then(|v| v.as_u64()),
                cmd.get("col").and_then(|v| v.as_u64()),
            ) {
                handle_plain(&mut srv, &sidecar, &rs, l as usize, c as usize, true);
                continue;
            }
            emit_json(&json!({"error": "expected {fn,body,cursor} or {line,col}"}));
            continue;
        }

        // Plain `<line> <col>` text protocol (human mode, or `--json` fallback).
        let parts: Vec<&str> = trimmed.split_whitespace().collect();
        let parsed = if parts.len() == 2 {
            match (parts[0].parse::<usize>(), parts[1].parse::<usize>()) {
                (Ok(a), Ok(b)) => Some((a, b)),
                _ => None,
            }
        } else {
            None
        };
        let (rl, rc) = match parsed {
            Some(p) => p,
            None => {
                if json {
                    emit_json(&json!({"error": "expected `<line> <col>` (two integers)"}));
                } else {
                    println!("? expected `<line> <col>`");
                }
                continue;
            }
        };
        handle_plain(&mut srv, &sidecar, &rs, rl, rc, json);
    }
    srv.shutdown();
}

/// Snapshot cursor query (no splice): map `(rl, rc)` via the original sidecar
/// + `.rs`, open the `.lean`, and report the goal (JSON or human form).
fn handle_plain(srv: &mut LeanServer, sidecar: &Sidecar, rs: &str, rl: usize, rc: usize, json: bool) {
    match resolve_cursor(sidecar, rs, rl, rc) {
        Ok((name, lean_file, lline, lcol)) => {
            let t = Instant::now();
            let warm = srv.is_open(lean_file);
            if let Err(e) = srv.ensure_open(lean_file) {
                if json {
                    emit_json(&json!({"line": rl, "col": rc, "error": format!("open failed: {}", e)}));
                } else {
                    println!("! open failed: {}", e);
                }
                return;
            }
            let goal = srv.plain_goal(lean_file, lline, lcol);
            let ms = t.elapsed().as_millis() as u64;
            if json {
                emit_json(&json!({
                    "line": rl, "col": rc, "fn": name,
                    "lean_file": lean_file, "lean_line": lline, "lean_col": lcol,
                    "warm": warm, "ms": ms, "goal": goal,
                }));
            } else {
                println!(
                    "--- .rs {}:{} → {} ({}:{}:{})  [{}, {} ms] ---",
                    rl,
                    rc,
                    name,
                    std::path::Path::new(lean_file).file_name().unwrap().to_string_lossy(),
                    lline,
                    lcol,
                    if warm { "warm" } else { "cold-open" },
                    ms
                );
                println!("{}", goal.unwrap_or_else(|| "(no goal)".into()));
            }
        }
        Err(e) => {
            if json {
                emit_json(&json!({"line": rl, "col": rc, "error": e}));
            } else {
                println!("! {}", e);
            }
        }
    }
}
