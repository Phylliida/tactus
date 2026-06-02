# Tactus Server — feasibility findings + implementation plan

**Goal.** A "Tactus server" that gives the Lean-server / VS Code infoview
experience — inline proof **goal state** at the cursor, live diagnostics — but
operating directly on Tactus `.rs` source (the `proof fn … by { … }` blocks and
`#[verifier::tactus_auto]` exec fns), instead of on `.lean` files.

**Status (2026-06-02).** Investigated against the live codebase. **Verdict:
doable**, and more tractable than it sounds — because Tactus already generates
real per-fn `.lean` files and already has most of the source-mapping machinery.
Every load-bearing claim below is verified with a `file:line` citation. **The
Phase-0 de-risk spike is now run and GREEN** (2026-06-02) — `lean --server`
resolves Mathlib for an out-of-Lake `.lean` via `LEAN_PATH` and returns a real
goal via `$/lean/plainGoal`. See `server-spike/` and § "De-risk first" below.
The plan below is otherwise plumbing over existing infra.

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

### 1. `tactus emit <file.rs>` — codegen-only mode + sidecar — ✅ LANDED 2026-06-02

`--emit-lean` runs codegen + writes the sidecar and **skips the Lean run** —
so it needs no Lean/Mathlib at all and is fast. Pinned by
`test_emit_lean_codegen_only` (e2e). What landed:

- **Flag** `--emit-lean` in `rust_verify::config` (5-site `bool` like `no_verify`),
  passed through the test harness allowlist.
- **emit/run split** (`lean_verify::generate`): `check_proof_fn` / `check_exec_fn`
  factored into `pub emit_proof_fn` / `emit_exec_fn` returning
  `Result<EmitOutput, CheckResult>` where `EmitOutput = { file_path, source_map,
  warnings }`; `check_*` = `emit_* + the lean-run tail`. (The split was as clean
  as predicted.)
- **verifier wiring**: at the per-fn loop's two Tactus branches, `if self.args.emit_lean`
  calls `emit_*`, pushes a `SidecarFn` (built from the `EmitOutput`'s `LeanSourceMap`
  + the `.rs` `tactic_span` byte range, which is in scope there), and `continue`s.
  Entries accumulate on `Verifier.tactus_sidecar`, merge across buckets (like
  `count_verified`), and write once at the tail of `verify_crate_inner` to
  `lean_verify::sourcemap_path(crate) = {lean_out_root}/{crate}/sourcemap.json`.
- **schema** (`lean_verify::sourcemap`, serde) — realized form (note `kind` is the
  serde tag, snake_case; `lean_indent_delta` is NOT emitted yet — see de-risk item 3):
  ```json
  { "crate_name": "test_crate",
    "fns": [
      { "kind": "proof", "name": "lemma_double_pos",
        "lean_file": ".../test_crate/lemma_double_pos.lean",
        "rs_tactic_byte_range": [446, 474],
        "lean_tactic_start_line": 435, "lean_tactic_line_count": 2 },
      { "kind": "exec", "name": "add_one",
        "lean_file": ".../test_crate/add_one.lean",
        "span_marks": [ { "lean_line": 438, "rs_loc": ".../test.rs:29:5", "kind": "assert" },
                        { "lean_line": 442, "rs_loc": ".../test.rs:27:13", "kind": "postcondition" } ] } ] }
  ```
- **Bonus fix the sidecar exposed**: the proof branch fired for *every* query op of
  a tactic proof fn (Body + recommends-check) — duplicating the sidecar entry AND
  re-running Lean per query op in normal mode. Gated it on `Body(Style::Normal)`
  (mirroring the exec branch), so a tactic proof fn is checked/emitted exactly once.
  Full e2e suite green (480/0), so the normal-mode change regressed nothing.

Remaining for Phase 1: `lean_indent_delta` (de-risk item 3 — column mapping), and
the extension/bridge that consumes this sidecar.

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

**✅ Confirmed (2026-06-02, `server-spike/livedit_probe.py`).** A `didChange`
into the open `.lean` re-elaborates incrementally from the changed command with
imports warm (no Mathlib reload) and no rustc: cheap tactic edits settle in
~0.5–0.6s with live diagnostics/goal; an expensive tactic (`nlinarith`) costs its
genuine proof-search time (~11s here), the same cost batch verification pays — i.e.
"Lean-speed" is the speed Lean elaborates *that* tactic, just like the VS Code
Lean4 infoview today. `plainGoal` stays correct across the edit cycle.

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

## De-risk first — ✅ RUN, GREEN (2026-06-02)

The spike is done. Driver + full result in `server-spike/` (`plaingoal_probe.py`,
`README.md`). Summary: drove `lean --server` over LSP/stdio against a real
Tactus-generated `.lean` (`fib_addition.lean` — imports `Mathlib.Tactic.Linarith`,
uses `linarith` + `nlinarith`), with rootUri = the file's own dir (no `lakefile.lean`
in any ancestor → the server can't discover a Lake project, so Mathlib must resolve
via `LEAN_PATH` from the env). Result: processed in ~16s with **0 error diagnostics**,
and `$/lean/plainGoal` returned the full proof state at the `nlinarith` line.

The three unknowns, resolved:

1. ✅ **RESOLVED (green) — the critical one.** `lean --server` resolves Mathlib for an
   out-of-Lake `.lean` with `LEAN_PATH` set. The per-file worker behaves like the batch
   `lean --json` path (same ~16s processing, 0 errors). Had it not resolved, we'd have
   seen `unknown import` / `unknown tactic nlinarith`. **A real goal came back, so the
   whole project is green** — everything else is plumbing over existing infra.
2. ✅ **RESOLVED — "state here" semantics, as hoped.** `$/lean/plainGoal` with the cursor
   at the *start* of a tactic returns the goal *before* that tactic; cursor *past* the
   tactic returns `no goals`. This is exactly the infoview convention users expect.
3. ⏳ **`lean_indent_delta`** (minor, Phase-1 detail, not a viability risk) —
   `to_lean_fn::render_by_block` re-indents tactic bodies by 2 spaces (for the `by`
   block). Confirm the exact transform so *column* mapping is right (it may differ
   between standalone proof fns and trait-method bodies). The spike used `.lean`-native
   line/char coordinates directly; the `.rs`→`.lean` column delta is the remaining piece
   to nail down when wiring the sidecar map.

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
