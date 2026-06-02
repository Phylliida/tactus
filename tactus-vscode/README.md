# Tactus Infoview (VS Code extension)

The editor face of the Tactus server (see [`../SERVER.md`](../SERVER.md)) — inline
**Lean goal state at the cursor** for Tactus `.rs` proofs. It's a *thin client*
over [`../tactus-lsp`](../tactus-lsp): on each cursor move it sends the position to
the warm `tactus-lsp` server and renders the returned goal in a panel. No rustc at
query time; after a file's first (cold) query, moves update in ~milliseconds.

Proof fns today (exec fns are a later pass in `tactus-lsp`). If you edit the `.rs`
*structurally* (anything but tactic text), re-run `verus --emit-lean` to refresh the
sidecar's byte ranges.

> **Status:** written + type-checked (`tsc` clean) but **not yet run in a live VS
> Code** by the author (no editor in the build env). First real run is the install
> + test below — please report what you see.

## Prerequisites

1. **`tactus-lsp` built** — `cd ../tactus-lsp && cargo build --release`.
2. **A sidecar + `.rs`** from `verus --emit-lean` (see *Quick test* for a ready one).
3. **`lean` / `lake` on PATH** and the Mathlib lake project at `../lean-project`
   (the same one the test suite uses). The server resolves `LEAN_PATH` from it.
4. **Node** (for building the extension): `node --version` ≥ 18.

## Build & launch (Extension Development Host)

```bash
cd tactus-vscode
npm install
npm run compile        # tsc → out/extension.js  (or `npm run watch` while editing)
```

Then open this `tactus-vscode/` folder in VS Code and press **F5** ("Run Tactus
Infoview Extension"). That opens a second VS Code window (the *Extension
Development Host*) with the extension loaded.

## Quick test (ready-made fixture)

In a terminal:

```bash
./example/get-test-artifacts.sh
```

It builds `tactus-lsp`, regenerates the `test_emit_lean_codegen_only` fixture (a
proof fn `lemma_double_pos`, a multi-step `chain`, an exec fn), and **prints the
exact settings + cursor positions to try.** Then, in the Extension Development Host:

1. **Open the printed `test.rs`** (File → Open File…).
2. **Settings (JSON)** — paste the three `tactus.*` values the script printed
   (`serverPath`, `sidecarPath`, `leanProject`).
3. Run **`Tactus: Show Goal (Infoview)`** (Cmd/Ctrl-Shift-P).
4. Move the cursor onto the proof tactic lines. Expected (editor line numbers):
   - line 21 `unfold double; omega` → `⊢ double x > x`
   - line 39 `unfold double` → `⊢ double n > n`
   - line 40 `have h : n + n > n …` → `⊢ n + n > n`
   - line 41 `exact h` → `h : n + n > n ⊢ n + n > n`

   The first query warms the file (~2.6 s); the rest update in ~ms. Cursors outside
   a proof tactic block show a muted "not inside any proof fn tactic block".

## Using it on your own crate

1. Produce a sidecar: run your normal Tactus verification with `--emit-lean` (e.g.
   `verus --emit-lean … yourfile.rs`, or via `cargo-verus` passing the flag). It
   writes `{lean_out_root}/{crate}/sourcemap.json` + the per-fn `.lean` files.
2. Settings: point `tactus.serverPath` at the `tactus-lsp` binary, set
   `tactus.leanProject` (or have `$LEAN_PATH` in your env). `tactus.sidecarPath` can
   be left empty to auto-discover `**/tactus-lean/*/sourcemap.json` in the workspace.
3. Open the `.rs`, run `Tactus: Show Goal`, move the cursor.

> **Single-file caveat:** the sidecar's byte ranges are per-fn but don't yet record
> *which* `.rs` file each fn came from, so the extension passes the active editor's
> file. That's exact for a single-file crate; multi-file support needs the sidecar
> to carry the source path per fn (a small follow-up).

## Settings

| Setting | Default | Meaning |
|---|---|---|
| `tactus.serverPath` | `tactus-lsp` | Path to the `tactus-lsp` binary (PATH or absolute). |
| `tactus.sidecarPath` | *(empty)* | `sourcemap.json` path; empty → auto-discover in the workspace. |
| `tactus.leanProject` | *(empty)* | Tactus lean-project dir → `TACTUS_LEAN_PROJECT`; empty → rely on `$LEAN_PATH`. |

## Commands

- **Tactus: Show Goal (Infoview)** — start the server for the active `.rs` + open the panel.
- **Tactus: Stop Infoview Server** — kill the server + close tracking.

## How it works

`tactus-lsp serve --json <sidecar> <rs>` is spawned once and kept warm. On each
`onDidChangeTextEditorSelection`, the extension writes `<line> <col>\n` (0-indexed)
to its stdin and reads one JSON line back (`{fn, lean_line, warm, ms, goal}` or
`{error}`), coalescing rapid moves to a single in-flight query (latest wins). The
panel renders the goal (the ```lean fences stripped). All the real work —
`lean --server` management, the `.rs`↔`.lean` position map — lives in `tactus-lsp`;
this extension is ~200 lines of glue + a webview.
