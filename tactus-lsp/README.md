# tactus-lsp — warm persistent goal server for Tactus

The server *core* of the Tactus infoview (see [`../SERVER.md`](../SERVER.md)).
It turns the proven `server-spike/goal_at_cursor.py` bridge into a real,
persistent server: spawn **one** `lean --server`, keep it hot (each `.lean` is
opened/elaborated at most once), and answer repeated `.rs`-cursor → Lean-goal
queries. No rustc at query time — it reads the `--emit-lean` sidecar
(`sourcemap.json`) that `verus --emit-lean` already produced.

**The win — warm = interactive.** The per-query Python bridge spawns a fresh
`lean --server` every call. This keeps one warm: the first query to a file pays
the open/elaboration cost; every subsequent query is a single `$/lean/plainGoal`
round-trip.

```
--- .rs 38:4 → chain (chain.lean:435:2)  [cold-open, 2598 ms] ---
⊢ double n > n
--- .rs 39:4 → chain (chain.lean:436:2)  [warm, 2 ms] ---
⊢ n + n > n
--- .rs 40:4 → chain (chain.lean:437:2)  [warm, 2 ms] ---
h : n + n > n  ⊢ n + n > n
```

~2600 ms → **~2 ms** for warm repeat queries, and the goal evolves line-to-line
through the proof (note `h` entering the context at `exact h`).

## What it is / isn't

- **Is:** the language-agnostic server core — process management of `lean
  --server`, the `--emit-lean` sidecar reader, the content-anchored `.rs`↔`.lean`
  position map, and the `$/lean/plainGoal` proxy, kept warm.
- **Isn't (yet):** a full LSP server on its *own* front (it speaks a tiny line
  protocol, not LSP, to its caller) and an editor UI. The VS Code extension /
  infoview panel is a thin client over this — point it at the binary, send cursor
  positions, render the goals. That's the remaining frontend work (best built
  where there's an editor to test in). Proof fns only today; exec fns (the
  sidecar's coarser `span_marks`) are a later pass.

## Usage

```bash
cargo build --release

# one-shot (spawns lean, opens the file, one query, exits):
tactus-lsp goal  <sourcemap.json> <file.rs> <line> <col>

# persistent warm server (keeps lean hot; reads `<line> <col>` per stdin line):
tactus-lsp serve <sourcemap.json> <file.rs>
```

`line`/`col` are 0-indexed (LSP convention). `LEAN_PATH` resolves from
`$LEAN_PATH`, else `lake env printenv LEAN_PATH` in `$TACTUS_LEAN_PROJECT`
(or `../lean-project`).

### Getting a sidecar + `.rs` to point it at

```bash
cd ../source
PATH="../tools/vargo/target/release:$PATH" VERUS_KEEP_TEST_DIR=1 \
  vargo test -p rust_verify_test --test tactus -- test_emit_lean_codegen_only
# artifacts under target/debug/test_inputs/*emit_lean*/:  test.rs  and
#   tactus-lean/test_crate/sourcemap.json
```

Or run `verus --emit-lean` on any Tactus crate to produce
`{lean_out_root}/{crate}/sourcemap.json` + the per-fn `.lean` files.

## Design notes

- **No async runtime.** A reader thread parses Content-Length-framed JSON-RPC
  from `lean --server`'s stdout into a channel; the main thread correlates
  responses by id and drains `$/lean/fileProgress` to know when a file is
  elaborated. ~std-only (serde for JSON).
- **Position map** is content-anchored: the tactic body is copied verbatim
  line-for-line into the `.lean`, so matching `lean_tactic_start_line`'s text to
  the `.rs` body line pins a constant per-fn delta (robust to leading-blank /
  dedent). Column = the `.lean` tactic line's first non-space col, which is what
  plainGoal's "state here" wants; precise `lean_indent_delta` is a refinement.
- Standalone crate (not in the Verus `source/` workspace) so it stays
  independent of the vargo build.
