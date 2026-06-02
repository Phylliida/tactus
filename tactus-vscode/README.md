# Tactus Infoview (VS Code extension)

The editor face of the Tactus server (see [`../SERVER.md`](../SERVER.md)) — inline
**Lean goal state at the cursor** for Tactus `.rs` proofs. It's a *thin client*
over [`../tactus-lsp`](../tactus-lsp): on each cursor move it sends the position to
the warm `tactus-lsp` server and renders the returned goal in a panel. No rustc at
query time; after a file's first (cold) query, moves update in ~milliseconds.

It also updates **as you edit** the proof (see [Live editing](#live-editing)) and
shows Lean **errors** in red under the goal. Proof fns today (exec fns are a later
pass in `tactus-lsp`).

> **Status:** working — run live in VS Code (cursor-precise goals, live edits, errors).

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

## Quick test (ready-made fixture) — the exact steps

In a terminal, generate a ready-to-use fixture **and** the exact settings to paste:

```bash
cd tactus-vscode
./example/get-test-artifacts.sh
```

It builds `tactus-lsp` (release), regenerates the `test_emit_lean_codegen_only`
fixture (a proof fn `lemma_double_pos`, a multi-step `chain`, an exec fn), and
**prints the absolute `test.rs` path + a ready-to-paste settings block** (four
`tactus.*` values). Keep that output handy. Then, in the **Extension Development
Host** (the second VS Code window that F5 opened):

1. **Open the printed `test.rs`** — `File → Open File…`, paste its path.

2. **Open Settings (JSON)** — `Ctrl+Shift+P` → **`Preferences: Open User Settings
   (JSON)`**. Paste the four values the script printed **inside** the top-level
   `{ }` braces (commas between entries), then **save** (`Ctrl+S`). They look like:

   ```json
   {
     "tactus.serverPath":   "/…/tactus-lsp/target/release/tactus-lsp",
     "tactus.sidecarPath":  "/…/test_inputs/…/tactus-lean/test_crate/sourcemap.json",
     "tactus.toolchainBin": "/…/lean4-…/bin",
     "tactus.leanPath":     "/…/lean-project/.lake/…:/…:/…"
   }
   ```

   Use **User** settings (not Workspace — opening a single file may give no workspace
   folder). The `toolchainBin` + `leanPath` are not optional: GUI-launched VS Code
   usually lacks `lean`/`lake` on its PATH, so without them the server can't start
   (panel shows `tactus-lsp exited (1)`).

3. Run **`Tactus: Show Goal (Infoview)`** (`Ctrl+Shift+P`). A panel opens beside the editor.

4. **Move the cursor** onto the proof tactic lines (editor line numbers, from the script):
   - line 21 `unfold double; omega` → `⊢ double x > x`
   - line 39 `unfold double` → `⊢ double n > n`
   - line 40 `have h : n + n > n …` → `⊢ n + n > n`
   - line 41 `exact h` → `h : n + n > n ⊢ n + n > n`

   The first query warms the file (~2.6 s); the rest update in ~ms. It's **column-
   precise** (cursor before a tactic → goal before it; past `a;` or end-of-line →
   goal after). Cursors outside a proof tactic block show a muted "not inside a proof
   tactic block".

5. **Edit a tactic** and watch the goal follow (rename a hypothesis, insert a `have`).
   Break it (type a nonexistent tactic) and the Lean error appears in red under the
   goal; fix it and the error clears.

> **After you rebuild** the extension (`npm run compile`) or `tactus-lsp` (`cargo
> build --release`), **reload** the Extension Development Host: `Ctrl+Shift+P` →
> **`Developer: Reload Window`**, then re-run `Tactus: Show Goal`.

## Using it on your own crate

1. Produce a sidecar: run your normal Tactus verification with `--emit-lean` (e.g.
   `verus --emit-lean … yourfile.rs`, or via `cargo-verus` passing the flag). It
   writes `{lean_out_root}/{crate}/sourcemap.json` + the per-fn `.lean` files.
2. Settings (in the window where the extension runs):
   - `tactus.serverPath` → the `tactus-lsp` binary.
   - `tactus.toolchainBin` → `dirname $(which lean)` (so the server can spawn `lean`).
   - `tactus.leanPath` → `lake env printenv LEAN_PATH` run in your lean-project (so the
     server resolves Mathlib without needing `lake`). **Recommended over `leanProject`**,
     which needs `lake` on the spawned PATH.
   - `tactus.sidecarPath` → leave empty to auto-discover `**/tactus-lean/*/sourcemap.json`
     in the workspace, or set it explicitly.
3. Open the `.rs`, run `Tactus: Show Goal`, move/edit at the cursor.

> **Single-file caveat:** the sidecar's byte ranges are per-fn but don't yet record
> *which* `.rs` file each fn came from, so the extension passes the active editor's
> file. That's exact for a single-file crate; multi-file support needs the sidecar
> to carry the source path per fn (a small follow-up).

## Settings

| Setting | Default | Meaning |
|---|---|---|
| `tactus.serverPath` | `tactus-lsp` | Path to the `tactus-lsp` binary (PATH or absolute). |
| `tactus.sidecarPath` | *(empty)* | `sourcemap.json` path; empty → auto-discover in the workspace. |
| `tactus.toolchainBin` | *(empty)* | Dir containing `lean`/`lake`; prepended to the server's PATH so it can spawn `lean --server`. `dirname $(which lean)`. |
| `tactus.leanPath` | *(empty)* | The `LEAN_PATH` value, passed directly so the server doesn't need `lake`. `lake env printenv LEAN_PATH` in the lean-project. **Recommended.** |
| `tactus.leanProject` | *(empty)* | Lean-project dir → `TACTUS_LEAN_PROJECT` (the server runs `lake` itself); needs `lake` on PATH. Use `leanPath` instead if you can. |

## Troubleshooting

- **Panel shows `tactus-lsp exited (1)`** — the server couldn't resolve `LEAN_PATH`
  or find `lean`/`lake`. GUI-launched VS Code usually doesn't inherit your shell
  PATH. Fix: set **`tactus.leanPath`** (the value of `lake env printenv LEAN_PATH`)
  and **`tactus.toolchainBin`** (`dirname $(which lean)`). `get-test-artifacts.sh`
  prints both. Reloading: re-run `Tactus: Show Goal` after changing settings.
- **Check the Debug Console** of the *first* VS Code window (the one you pressed F5
  in) for `[tactus-lsp] …` stderr lines — they carry the server's own error text.
- **`(no goals)` or "not inside any proof fn tactic block"** — the cursor isn't in a
  proof `by { }` block, or you edited the `.rs` structurally and the sidecar's byte
  ranges drifted (re-run `--emit-lean`).

## Commands

- **Tactus: Show Goal (Infoview)** — start the server for the active `.rs` + open the panel.
- **Tactus: Stop Infoview Server** — kill the server + close tracking.

## Live editing

The goal updates as you **edit** the proof, not just as you move the cursor — in
~6–8 ms warm, no rustc. On each cursor move or text change, the extension parses
the live buffer for the cursor's `proof fn … by { … }` block and sends its current
tactic body to `tactus-lsp`, which splices it into the warm `.lean` and
re-elaborates (`didChange`). So you can rename a hypothesis, insert a `have`, etc.,
and watch the goal track it. (Because it parses the *live* buffer, it's robust to
`.rs` edits without re-running `--emit-lean` — only structural changes that move a
`proof fn` to a new file, or rename it, would need a re-emit.)

> After rebuilding the extension (`npm run compile`) or `tactus-lsp`, **reload** the
> Extension Development Host (`Developer: Reload Window`) and re-run `Tactus: Show Goal`.

## How it works

`tactus-lsp serve --json <sidecar> <rs>` is spawned once and kept warm. On each
cursor move or edit, the extension finds the cursor's tactic block in the live
buffer and writes `{"fn","body","cursor"}` to the server's stdin, reading one JSON
line back (`{fn, lean_line, warm, ms, goal}` or `{error}`), coalescing rapid events
to a single in-flight query (latest wins). The panel renders the goal (the ```lean
fences stripped). All the real work — `lean --server` management, the splice +
position map — lives in `tactus-lsp`; this extension is ~250 lines of glue + a webview.
