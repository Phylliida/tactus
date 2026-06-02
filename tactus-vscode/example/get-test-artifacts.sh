#!/usr/bin/env bash
# Produce a ready-to-test Tactus sidecar + .rs and print the exact extension
# settings to use. Regenerates the `test_emit_lean_codegen_only` e2e fixture
# (a proof fn `lemma_double_pos` + a multi-step `chain` + an exec fn) under a
# kept temp dir, then prints the absolute paths + a settings block to paste
# into the Extension Development Host.
set -euo pipefail

REPO="$(cd "$(dirname "$0")/../.." && pwd)"          # .../tactus
SRC="$REPO/source"

echo "Building tactus-lsp (release)…"
( cd "$REPO/tactus-lsp" && cargo build --release -q )

echo "Generating the --emit-lean fixture (keeps the temp dir)…"
( cd "$SRC" && PATH="../tools/vargo/target/release:$PATH" VERUS_KEEP_TEST_DIR=1 \
    vargo test -p rust_verify_test --test tactus -- test_emit_lean_codegen_only >/dev/null 2>&1 )

D="$(find "$SRC/target/debug/test_inputs" -type d -name '*emit_lean_codegen_only' | head -1)"
RS="$D/test.rs"
SIDECAR="$D/tactus-lean/test_crate/sourcemap.json"
BIN="$REPO/tactus-lsp/target/release/tactus-lsp"
LEANPROJ="$REPO/lean-project"

[ -f "$RS" ] && [ -f "$SIDECAR" ] && [ -x "$BIN" ] || { echo "ERROR: artifacts missing"; exit 1; }

# Resolve LEAN_PATH + the toolchain bin dir so VS Code (which often lacks the
# Lean toolchain on its PATH) can be configured to pass them directly.
LEANPATH="$(cd "$LEANPROJ" && lake env printenv LEAN_PATH 2>/dev/null)"
TOOLBIN="$(dirname "$(command -v lean)")"

cat <<EOF

========================================================================
Ready to test. In the Extension Development Host:

  1. File → Open File…           $RS
  2. Open Settings (JSON) and add:

  "tactus.serverPath":   "$BIN",
  "tactus.sidecarPath":  "$SIDECAR",
  "tactus.toolchainBin": "$TOOLBIN",
  "tactus.leanPath":     "$LEANPATH"

  (leanPath + toolchainBin matter because GUI-launched VS Code usually can't
   find lean/lake on its PATH; passing them directly avoids that.)

  3. Run command  "Tactus: Show Goal (Infoview)"
  4. Move the cursor onto the proof tactic lines, e.g. (1-indexed in the
     editor's status bar):
        line 21  "unfold double; omega"     → ⊢ double x > x
        line 39  "unfold double"            → ⊢ double n > n
        line 40  "have h : n + n > n …"      → ⊢ n + n > n
        line 41  "exact h"                  → h : n + n > n ⊢ n + n > n
     The first query warms the file (~2.6s); the rest update in ~ms.
========================================================================
EOF
