# server-spike — Phase-0 de-risk for the Tactus server

See [`../SERVER.md`](../SERVER.md) for the full feasibility study + plan.
This directory holds the Phase-0 de-risk probe it called for, and the
result.

## The question

SERVER.md's plan rests on one load-bearing unknown:

> Does `lean --server` resolve Mathlib for an **out-of-Lake** `.lean` file
> with `LEAN_PATH` set, and return a real goal via `$/lean/plainGoal`?
>
> *"If this returns a real goal, the whole project is green — everything
> else is plumbing over existing infra."*

The batch path (`lean --json`, how Tactus checks today) resolves Mathlib
via `LEAN_PATH`; the server's per-file worker path is slightly different,
so it needed confirming directly.

## The result (2026-06-02, Lean 4.25.0): 🟢 GREEN

`plaingoal_probe.py` drives `lean --server` over LSP/stdio against a real
Tactus-generated `.lean` (`fib_addition.lean` — imports
`Mathlib.Tactic.Linarith`, uses `linarith` + `nlinarith`). rootUri is set
to the file's **own directory**, which has no `lakefile.lean` anywhere
above it, so the server cannot discover a Lake project by walking up — it
must fall back to `LEAN_PATH` from the environment. That is exactly the
deployment scenario the Tactus server would use.

Observed:

- **Mathlib resolved via `LEAN_PATH` alone.** File processed in ~16s
  (≈ the 15.5s batch time) with **0 error diagnostics**. Had Mathlib not
  resolved, we'd have seen `unknown import` / `unknown tactic nlinarith`.
- **`$/lean/plainGoal` returned a real, rich goal** at the `nlinarith`
  line — the full proof state (`m n : ℕ`, all the `have` hypotheses, the
  `⊢` goal). Exactly what an infoview renders.
- **Cursor convention ("state here") confirmed:** cursor at a tactic's
  start → goal **before** it; cursor past the tactic → `no goals`.

So SERVER.md de-risk items **1** (Mathlib-via-LEAN_PATH in the server) and
**2** (plainGoal cursor convention) are both resolved favorably. Item 3
(`lean_indent_delta` column mapping) is a minor detail for Phase 1, not a
viability risk.

## Running it

```bash
# Defaults to the fib_addition sample; self-resolves LEAN_PATH via
# `lake env printenv` in ../lean-project (or $TACTUS_LEAN_PROJECT).
python3 plaingoal_probe.py

# Any Tactus-generated .lean, with explicit 0-indexed LSP positions:
python3 plaingoal_probe.py path/to/file.lean 331:6 293:6
```

Requires `lean` / `lake` on PATH (Lean 4.25.0) and the Mathlib Lake project
built at `../lean-project`. If the default sample file is missing, generate
it by running the e2e suite, or pass any generated `.lean` path.

## Probe #2 — the live-edit fast path (`livedit_probe.py`): 🟢 GREEN

Tests SERVER.md's "tactic-only splice" model — the thing that makes the
infoview feel *live*: edit tactic text → `didChange` to `lean --server` →
diagnostics/goal update fast, **no rustc**. This probe talks only to
`lean --server` (never invokes rustc/Verus). It opens the file once, then
applies edits to the final `nlinarith` line and measures each round-trip:

| edit (didChange, no rustc) | latency | result |
|---|---|---|
| cold open (one-time Mathlib load) | ~15.8s | clean |
| break → bare `linarith` | **~0.56s** | live `ERROR: linarith failed` (with goal context) |
| → `sorry` | **~0.62s** | error gone, `declaration uses 'sorry'` warning |
| restore → `nlinarith [...]` | ~11.6s | clean |

Reading: the fast-path is real — edits re-elaborate **incrementally from the
changed command, imports stay warm (no 16s reload), no rustc**. The two
sub-second edits prove it. The ~11.6s restore is **not** the fast-path
failing — it's `nlinarith`'s genuine proof-search cost (the same cost batch
verification pays; the cold open spent most of its 16s right there). So
"Lean-speed" = *the speed Lean elaborates that tactic*: sub-second for cheap
tactics, seconds for an expensive nonlinear search — exactly how the VS Code
Lean4 infoview behaves today. `$/lean/plainGoal` still returned the correct
goal after the full edit cycle.

So SERVER.md's incremental model (component 4) is confirmed: tactic-only edits
are a live, Lean-speed, rustc-free `didChange`. Only signature/structural edits
need a `tactus emit` (rustc) re-run.

```bash
python3 livedit_probe.py
```

## The bridge — `.rs` cursor → Lean goal (`goal_at_cursor.py`): 🟢 WORKING

Not a de-risk probe — the actual **end-to-end Tactus-server core** (SERVER.md
components 2 + 3), built on the `--emit-lean` sidecar. Given a `sourcemap.json`,
a `.rs` file, and a cursor `(line, col)`, it: finds the proof fn whose tactic
block contains the cursor, maps the `.rs` line to a `.lean` line (content-anchored
to `lean_tactic_start_line` — the body is copied verbatim line-for-line, so it's a
constant per-fn delta), drives `lean --server` (`$/lean/plainGoal`), and returns
the goal. **No rustc at query time** — the sidecar + `.lean` came from `--emit-lean`.

```bash
# (sidecar, .rs, line, col)  — 0-indexed line/col (LSP convention)
python3 goal_at_cursor.py path/to/sourcemap.json path/to/file.rs 38 4
```

Demonstrated (2026-06-02) against a real `--emit-lean` crate — the goal evolves
line-to-line, exactly the infoview experience:

| `.rs` cursor | `.lean` (Δ +397) | goal |
|---|---|---|
| `unfold double`         | L435 | `⊢ double n > n` |
| `have h : n + n > n …`   | L436 | `⊢ n + n > n` (after `unfold`) |

Cursors outside any proof tactic block fail cleanly. Proof fns only for now —
exec fns use coarser `span_marks` (a later pass). Column-precise mapping
(`lean_indent_delta`) is a refinement; querying at the `.lean` tactic line's
first non-space column gives plainGoal's "state here" goal, which is what the
infoview wants.

To generate artifacts to point it at: run the e2e test with the temp dir kept —
`VERUS_KEEP_TEST_DIR=1 vargo test -p rust_verify_test --test tactus -- test_emit_lean_codegen_only`
— then look under `source/target/debug/test_inputs/*emit_lean*/` for `test.rs` and
`tactus-lean/test_crate/sourcemap.json`.
