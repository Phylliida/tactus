# Tactus Server — feasibility, plan, and progress

**Goal.** A "Tactus server" that gives the Lean-server / VS Code infoview
experience — inline proof **goal state** at the cursor, live diagnostics — but
operating directly on Tactus `.rs` source (the `proof fn … by { … }` blocks and
`#[verifier::tactus_auto]` exec fns), instead of on `.lean` files.

> **At a glance (2026-06-02).** The server *core* is built and works end-to-end.
> De-risk: both unknowns GREEN. Built: `--emit-lean` codegen-only mode +
> `sourcemap.json` sidecar (component 1, landed, full e2e suite 480/0); the
> `.rs`-cursor → Lean-goal bridge (components 2+3, demonstrated); and **`tactus-lsp/`
> — a real warm persistent goal server** (Rust): keeps one `lean --server` hot and
> answers repeat cursor queries in **~2 ms** (vs ~2.6 s cold-open), the goal evolving
> line-to-line through a proof. No rustc at query time. And **`tactus-vscode/` — the
> VS Code infoview extension** (a thin client over `tactus-lsp`): written + `tsc`-clean,
> with an F5 launch config and a `get-test-artifacts.sh` that prints ready-to-paste
> settings. The **full stack now exists, end to end**; the only unrun piece is the
> extension's live rendering (no editor in the build env — first live run is a manual
> install+test). Remaining polish: exec-fn goals via `span_marks`, the tactic-only
> splice fast path, multi-file source mapping, and the precise `lean_indent_delta` column.

**Status (2026-06-02).** Investigated against the live codebase. **Verdict:
doable**, and more tractable than it sounds — because Tactus already generates
real per-fn `.lean` files and already has most of the source-mapping machinery.
Every load-bearing claim below is verified with a `file:line` citation. **The
Phase-0 de-risk spike is run and GREEN** (2026-06-02) — `lean --server` resolves
Mathlib for an out-of-Lake `.lean` via `LEAN_PATH` and returns a real goal via
`$/lean/plainGoal`. **Component 1 (`--emit-lean` + sidecar) is LANDED, and the
end-to-end bridge (components 2+3: `.rs` cursor → Lean goal) is DEMONSTRATED
WORKING** (`server-spike/goal_at_cursor.py`) — the goal even evolves line-to-line
as you move through a proof. See `server-spike/` and § "De-risk first" below.
What remains is mostly the editor frontend + productionizing the bridge.

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

**Two gaps that were flagged here — first is now closed:**
- ~~**No emit-only CLI**~~ — **CLOSED.** `--emit-lean` adds exactly this: codegen +
  sidecar with the Lean run skipped (component 1, landed). See § "Components → 1".
- **No verus-analyzer in the workspace** (only `verus-field-extension` /
  `verus-quadratic-extension`, unrelated math crates). Irrelevant for the
  infoview — it needs only cursor position (from the editor) + tactic-block
  ranges (from the sidecar). Rust-side IDE features (go-to-def, etc.) are a separate,
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

### 2. Lean-server bridge — ✅ DEMONSTRATED (`server-spike/goal_at_cursor.py`)
- Spawn `lean --server` with `LEAN_PATH` = the cached lake-project path — the same
  env the batch path uses (see `lean_process.rs` and the test harness's
  `cached_lean_path_for_lake_project`).
- `textDocument/didOpen` the generated `.lean`.
- Goals: `$/lean/plainGoal` with `{ textDocument, position }` → plain-text goal.
  (Phase 2: `$/lean/rpc/call` → `getInteractiveGoals` for rich/structured goals.)

The Python bridge does exactly this today (proof fns): `.rs` cursor → find the fn
whose tactic block contains it → map to a `.lean` position → `plainGoal` → goal,
no rustc. Productionizing = porting this to the extension (TS) or a `tactus-lsp`
Rust binary. The de-risk + bridge prove the wiring; this is a re-host, not new risk.

### 3. Position map — ✅ DEMONSTRATED (proof fns)
- **Proof fn:** the tactic body is copied **verbatim line-for-line**, so the map is a
  constant per-fn delta: `.lean line = .rs line + (lean_tactic_start_line − rs_anchor_line)`.
  `goal_at_cursor.py` derives the delta **content-anchored** (match `lean_tactic_start_line`'s
  text to the `.rs` body line) — robust to the leading-blank-after-`{` and the dedent.
  Confirmed: two `.rs` tactic lines of one proof mapped to consecutive `.lean` lines with
  the same delta, returning two *different* goals (the goal evolving through the proof).
  Column: querying at the `.lean` tactic line's first non-space column gives plainGoal's
  "state here" goal (what the infoview wants); precise `lean_indent_delta` (= Lean indent −
  `.rs` dedent) is the remaining refinement (de-risk item 3) for exact column placement.
  (`LeanSourceMap::find_tactic_line` is the same arithmetic in reverse — already in-tree.)
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

### 5. VS Code extension — ✅ WRITTEN (`tactus-vscode/`), pending live validation
- Activates on `.rs`; `Tactus: Show Goal` spawns `tactus-lsp serve --json` for the
  active file and opens an infoview webview beside it; `onDidChangeTextEditorSelection`
  → send `<line> <col>` → render the returned goal. Coalesces rapid moves (single
  in-flight, latest wins). Config: `serverPath` / `sidecarPath` (auto-discover) /
  `leanProject`. `tsc`-clean; F5 dev-host launch config; `example/get-test-artifacts.sh`
  prints ready-to-paste settings + cursor positions.
- **Not yet run in a live VS Code** (no editor in the build env) — but the whole data
  path it drives is validated: the release `tactus-lsp` + the exact fixture + the exact
  cursor lines return correct goals (cold ~2.7 s, warm ~2 ms, evolving through the proof).
- Diagnostics from `--emit-lean` / `check` output (already `.rs`-mapped) — a later add.

---

## Phasing + progress

The original three-phase plan is kept below with status. In practice we skipped
the Phase-0 "manual correlation" rung — the de-risk came back green fast enough
that going straight to the real codegen + bridge was the better bet, and it paid off.

- **Phase 0 — ✅ effectively SUPERSEDED.** The plan was `tactus emit --watch` + an
  extension command that opens the generated `.lean` and lets the user run the
  *existing* Lean4 infoview, correlating position by hand. We instead landed the real
  `--emit-lean` (component 1) and built the position-mapping bridge directly — so the
  "manual correlation" stepping-stone isn't needed. (`--watch` itself is still a nice
  ergonomic add for the eventual frontend; cheap.)
- **Phase 1 — ⏳ core BUILT, frontend remains.** The headline (a live proof-fn
  infoview) breaks into: the Lean-server bridge ✅; the `plainGoal` proxy via the
  sidecar map ✅ (goal evolves line-to-line); a **warm persistent server ✅ built**
  (`tactus-lsp/` — a real Rust binary, ~2 ms warm queries, not a per-query spike); the
  tactic-only splice fast path ✅ de-risked (`livedit_probe.py`: ~0.5s `didChange`, no
  rustc) but not yet wired into `tactus-lsp`; the **infoview panel itself — still to
  build**. So what's left of Phase 1 is the editor frontend: a VS Code extension (TS)
  + infoview webview that is a *thin client over `tactus-lsp`* (send cursor positions,
  render goals), best built where there's an editor to test in.
- **Phase 2 — remaining.** Exec-fn obligation goals (the sidecar already carries the
  `span_marks`; the bridge just doesn't consume them yet), hover (rendered Lean / spec
  for an expression), diagnostics polish, the precise `lean_indent_delta` column map,
  and promotion to the `tactus-lsp` Rust binary if the mapping outgrows the sidecar.

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

## What exists vs what's built vs what's left

**Exists / reusable (~50–60% of the plumbing — was here before this work):**
codegen to per-fn `.lean`; the verbatim-tactic offset (`LeanSourceMap::ProofFn`,
`tactic_start_line`); `.lean → .rs` diagnostics (`format_error`, `SpanMarkLandmark`,
`/- @rust:LOC -/`); Lean subprocess management (`lean_process.rs`); the managed Lake
project + `LEAN_PATH` resolution; the FileLoader original-vs-sanitized duality
(`file_loader.rs`, `ORIGINAL_CACHE`).

**Built / demonstrated (2026-06-02):**
the `--emit-lean` flag + emit/run split (`emit_proof_fn`/`emit_exec_fn`) +
`sourcemap.json` (`lean_verify::sourcemap`) — ✅ landed, in-tree; the `lean --server`
proxy + content-anchored cursor→position map — ✅ demonstrated in
`server-spike/goal_at_cursor.py`; **`tactus-lsp/` — a real warm persistent goal server**
(Rust, std + serde): keeps `lean --server` hot, ~2 ms warm queries — ✅ built; the
tactic-only splice fast path — ✅ de-risked in `server-spike/livedit_probe.py` (not yet
wired into `tactus-lsp`).

**Still to build:**
the editor frontend — a VS Code extension (TS) + infoview panel that is a *thin client
over `tactus-lsp`* (send cursor positions, render goals); the splice fast path wired into
`tactus-lsp` (`didChange` instead of re-`ensure_open` on tactic-only edits); exec-fn goal
lookup (consume the sidecar's `span_marks`); the precise `lean_indent_delta` column map;
diagnostics/hover polish. None carry new risk — the de-risk + bridge + server core proved
the wiring.

**Key files to know** (line numbers below are pre-implementation citations and have
since drifted — the `--emit-lean` work shifted the verifier loop and refactored
`generate.rs`; treat them as landmarks, not exact):
`lean_verify/src/generate.rs` (`emit_proof_fn` / `check_proof_fn`, `emit_exec_fn` /
`check_exec_fn`, `krate_preamble`, `lean_file_path`, `sourcemap_path`);
`lean_verify/src/sourcemap.rs` (**new** — `Sidecar` / `SidecarFn` serde schema);
`lean_verify/src/to_lean_fn.rs` (`LeanSourceMap`, `render_by_block`);
`lean_verify/src/lean_process.rs` (`check_lean_file`, `format_error`);
`lean_verify/src/lean_pp.rs` (`SpanMarkLandmark`); `rust_verify/src/verifier.rs`
(read-tactic, the two Tactus branches + `emit_lean` wiring, `Verifier.tactus_sidecar`,
the `Body(Style::Normal)` proof gate, sidecar write at `verify_crate_inner`'s tail);
`rust_verify/src/file_loader.rs` (FileLoader + `ORIGINAL_CACHE`);
`rust_verify/src/attributes.rs` (`tactic_span`); `rust_verify/src/config.rs`
(`emit_lean` flag). Plus **`server-spike/`** — `plaingoal_probe.py` (de-risk #1),
`livedit_probe.py` (de-risk #2), `goal_at_cursor.py` (the end-to-end bridge), `README.md`.

---

*Investigation + first implementation: 2026-06-02. The `file:line` citations were live
at investigation time but have drifted with the `--emit-lean` landing — verify against
current code before relying on exact line numbers.*
