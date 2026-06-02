# Tactus Server — feasibility findings + implementation plan

**Goal.** A "Tactus server" that gives the Lean-server / VS Code infoview
experience — inline proof **goal state** at the cursor, live diagnostics — but
operating directly on Tactus `.rs` source (the `proof fn … by { … }` blocks and
`#[verifier::tactus_auto]` exec fns), instead of on `.lean` files.

**Status (2026-06-02).** Investigated against the live codebase. **Verdict:
doable**, and more tractable than it sounds — because Tactus already generates
real per-fn `.lean` files and already has most of the source-mapping machinery.
Every load-bearing claim below is verified with a `file:line` citation. No code
written yet; this is the plan + the evidence to start from.

---

## The core insight

You do **not** reimplement goal-state computation. Goal states come from Lean's
elaborator/kernel, and Tactus already emits real `.lean` that Lean can
elaborate. So the Tactus server is a **proxy / translator**, not a new prover
frontend:

```
.rs editor  ⟷  (codegen + position map)  ⟷  lean --server  ⟷  Lean kernel
```

And for **proof fns specifically the position map is nearly free**: Tactus copies
the `by { }` tactic body **verbatim, line-for-line** into the generated theorem.
So a cursor in a `.rs` tactic block maps to a `.lean` position by **adding a
constant** (`lean_tactic_start_line`). Editing tactics in a `.rs` block is —
modulo that offset — editing the proof body of a `.lean` theorem.

---

## Verdict table (every claim verified)

| Claim | Evidence (`source/lean_verify/src` unless noted) | Status |
|---|---|---|
| Codegen is cleanly separable from running Lean | `check_proof_fn` writes `rendered.text` + builds `LeanSourceMap` at `generate.rs:947–958`, **before** `lean_process::check_lean_file` at `generate.rs:974`. The Lean run + diagnostic-mapping tail is `generate.rs:972–1012`. | ✅ emit-only path already exists in-place |
| Tactic body is verbatim; cursor↔lean is a constant offset | `tactic_start_line = rendered.landmarks.tactic_starts.first()` (`generate.rs:951`); `tactic_line_count = tactic_body.lines().count()` (`generate.rs:952`); `LeanSourceMap::find_tactic_line` returns `lean_line - tactic_start_line` (`to_lean_fn.rs:~120`) — the inverse is `tactic_start_line + rs_offset`. | ✅ |
| `tactic_body` == literal `.rs` block text | `read_tactic_from_source(path, start, end)` reads the `by { }` block over its `tactic_span` byte range (`verifier.rs:1760`; span captured as `attributes.rs:1214 tactic_span: Option<(usize,usize)>`). | ✅ |
| Tactic edits do **not** invalidate VIR | the tactic text is read from source **at codegen time** (`verifier.rs:1760`), never baked into `vir_krate` — `check_proof_fn` takes `vir_krate` + a separate `tactic_text: &str` (`generate.rs:894`). | ✅ → no rustc rerun for tactic-only edits |
| `lean --server` + goal RPC exist (toolchain v4.25.0) | `lean --help` → `--server`; `"$/lean/plainGoal"` registered at `…/src/lean/Lean/Server/FileWorker/RequestHandling.lean:558`; interactive `"$/lean/rpc/call"` at `…/Server/Rpc/RequestHandling.lean:74`. | ✅ |
| Per-fn, self-contained `.lean` at a known path | `lean_file_path = lean_out_root()/{crate}/{fn}.lean` (`generate.rs:44`); root = `$TACTUS_LEAN_OUT` → `$CARGO_TARGET_DIR/tactus-lean` → `./target/tactus-lean` (`generate.rs:26–38`); prelude inlined via `Command::Raw(TACTUS_PRELUDE)` so each file is standalone (modulo Mathlib imports). | ✅ |
| `.lean → .rs` diagnostics already done | `lean_process::format_error(d, &source_map)` maps Lean diagnostics to `.rs` (`generate.rs:986`); exec fns use `SpanMarkLandmark { line, loc, kind }` (`lean_pp.rs:128`) emitted as `/- @rust:LOC -/` comments. | ✅ (reuse) |

**Two gaps, both minor:**
- **No emit-only CLI** — codegen is reachable only via the full verify path
  (`verifier.rs:1794` calls `check_proof_fn`). Need to add a verifier flag.
- **No verus-analyzer in the workspace** (only `verus-field-extension` /
  `verus-quadratic-extension`, unrelated math crates). Irrelevant for the
  infoview — it needs only cursor position (from the editor) + tactic-block
  ranges (from codegen). Rust-side IDE features (go-to-def, etc.) are a separate,
  later concern; the user's stock rust-analyzer would choke on the `verus!` macro
  anyway.

---

## Recommended architecture

**Do not build a full Rust LSP for the MVP.** The Rust-only smarts (codegen + the
position map) become **data** — a sidecar JSON — and orchestration stays thin:

```
VS Code ext (TS) ──run──► `tactus emit file.rs` ──► per-fn .lean + sourcemap.json
       │                       (Verus front-end; NO Lean run)
       ├── spawn/manage ──► lean --server   (existing Lean LSP = goal engine)
       └── on cursor ──► map via sourcemap.json → $/lean/plainGoal → infoview webview
```

Lean does all goal computation (free). Tactus produces `.lean` + the map. The
extension does arithmetic + RPC. Promote to a dedicated `tactus-lsp` Rust binary
later only if the mapping logic outgrows the sidecar.

---

## Components (precise)

### 1. `tactus emit <file.rs>` — codegen-only mode + sidecar
- Add `--emit-lean` (or similar) to `rust_verify::config` (`rust_verify/src/config.rs`).
- In `verifier.rs`'s per-fn loop (around `:1794`), branch to `emit_*` that runs
  everything up to `write_lean_file` and **skips** `check_lean_file`.
- Refactor `lean_verify::check_proof_fn` to split out
  `emit_proof_fn(vir_krate, proof_fn, tactic_text, …) -> (lean_text, LeanSourceMap)`
  from the Lean-run tail. **The split is already clean**: emit = `generate.rs:908–958`,
  run = `generate.rs:972–1012`. Same for `check_exec_fn`.
- Serialize a `sourcemap.json` (Tactus already computes all of it):
  ```json
  { "crate": "t",
    "fns": [
      { "name": "double_nonneg", "kind": "proof",
        "lean_file": ".../t/double_nonneg.lean",
        "rs_tactic_byte_range": [s, e],
        "lean_tactic_start_line": 433, "lean_tactic_line_count": 2,
        "lean_indent_delta": 2 },
      { "name": "use_vec", "kind": "exec",
        "lean_file": ".../t/use_vec.lean",
        "span_marks": [ {"lean_line": 470, "rs_loc": "f.rs:25:36", "kind": "LoopInvariant"} ] }
    ] }
  ```
- New code is just: the flag, the emit/run split, and serializing the map.
  ~95% of the verifier is reused.

### 2. Lean-server bridge (in the extension)
- Spawn `lean --server` with `LEAN_PATH` = the cached lake-project path — the same
  env the batch path uses (see `lean_process.rs` and the test harness's
  `cached_lean_path_for_lake_project`).
- `textDocument/didOpen` the generated `.lean`.
- Goals: `$/lean/plainGoal` with `{ textDocument, position }` → plain-text goal.
  (Phase 2: `$/lean/rpc/call` → `getInteractiveGoals` for rich/structured goals.)

### 3. Position map
- **Proof fn:** cursor line `L` in the `.rs` block → `.lean` line
  `lean_tactic_start_line + (L − rs_block_start_line)`, column `+ lean_indent_delta`.
  (`LeanSourceMap::find_tactic_line` is exactly this in reverse — already in-tree.)
- **Exec fn:** find the `span_marks` entry whose `rs_loc` is nearest at/before the
  cursor → its `lean_line`. Coarser (obligation granularity) but free from
  existing data.

### 4. Incremental model
On each edit, check whether it's entirely inside a known `rs_tactic_byte_range`:
- **tactic-only:** splice the new text into the `.lean` at the recorded location
  (it's verbatim) and send `didChange` to `lean --server` → **live, Lean-speed,
  no rustc**. (The whole point: tactic text never touches VIR.)
- **signature/structural:** re-run `tactus emit` (rustc front-end, ~1–3 s) on save
  → refresh `.lean` + sidecar.

### 5. VS Code extension
- Register `.rs` files in a Tactus mode; an infoview webview (fork the Lean4
  extension's, or a minimal panel) showing `plainGoal` at cursor.
- Diagnostics come straight from `tactus emit`/`check` output, already `.rs`-mapped.

---

## Phasing + rough effort

- **Phase 0 — ~2–4 days. ~80% of value, almost no new code.**
  `tactus emit --watch` + an extension command "open the generated `.lean` for the
  fn at cursor, refresh on save." User runs the **existing** Lean4 infoview on it,
  correlating position manually. Validates the whole idea immediately.
- **Phase 1 — ~2–3 weeks. The headline: live proof-fn infoview.**
  Lean-server bridge, `plainGoal` proxy via the sidecar map, the tactic-only
  splice fast path, the infoview panel.
- **Phase 2 — ~3–4 weeks.**
  Exec-fn obligation goals (via `span_marks`), hover (rendered Lean / spec for an
  expression), diagnostics polish, optional promotion to a `tactus-lsp` Rust binary.

---

## De-risk first (a ~1–2 day Phase-1 spike, before committing to the build)

Three unknowns — the only places this could surprise us:

1. **Does `lean --server` resolve Mathlib for an out-of-Lake `.lean` with
   `LEAN_PATH` set?** *The critical one.* Batch `lean --json` does (that's how
   Tactus checks today), but the server's per-file worker path is slightly
   different. **Spike:** spawn `lean --server`, `didOpen` one of the `.lean` files
   Tactus already generated (e.g. under `source/target/debug/test_inputs/…/tactus-lean/…`
   or `source/target/tactus-lean/…`), send `$/lean/plainGoal` at a position inside
   the tactic body, confirm a goal comes back. **If this returns a real goal, the
   whole project is green** — everything else is plumbing over existing infra.
2. **`plainGoal` cursor convention** — does it return the goal *before* the tactic
   at the position (the "state here" semantics users expect)? Confirm.
3. **`lean_indent_delta`** — `to_lean_fn::render_by_block` re-indents tactic bodies
   by 2 spaces (for the `by` block). Confirm the exact transform so column mapping
   is right (it may differ between standalone proof fns and trait-method bodies).

---

## What exists vs what's new (summary)

**Exists / reusable (~50–60% of the plumbing):**
codegen to per-fn `.lean`; the verbatim-tactic offset (`LeanSourceMap::ProofFn`,
`tactic_start_line`); `.lean → .rs` diagnostics (`format_error`, `SpanMarkLandmark`,
`/- @rust:LOC -/`); Lean subprocess management (`lean_process.rs`); the managed Lake
project + `LEAN_PATH` resolution; the FileLoader original-vs-sanitized duality
(`file_loader.rs`, `ORIGINAL_CACHE`).

**New:**
the `tactus emit` flag + emit/run split + `sourcemap.json` (small); spawning &
proxying `lean --server` (`$/lean/plainGoal`); the cursor→position arithmetic
(tiny, data-driven from the sidecar); the tactic-only splice fast path; the VS
Code extension/infoview.

**Key files to know:**
`lean_verify/src/generate.rs` (`check_proof_fn` `:894`, `check_exec_fn`,
`krate_preamble`, `lean_file_path` `:44`); `lean_verify/src/to_lean_fn.rs`
(`LeanSourceMap` `:94`, `render_by_block`); `lean_verify/src/lean_process.rs`
(`check_lean_file`, `format_error`); `lean_verify/src/lean_pp.rs`
(`SpanMarkLandmark` `:128`); `rust_verify/src/verifier.rs` (`:1760` read-tactic,
`:1794` check_proof_fn call); `rust_verify/src/file_loader.rs` (FileLoader +
`ORIGINAL_CACHE`); `rust_verify/src/attributes.rs` (`tactic_span` `:1214`);
`rust_verify/src/config.rs` (where to add the flag).

---

*Investigation: 2026-06-02. All `file:line` references were live at that date —
verify against current code before relying on exact line numbers.*
