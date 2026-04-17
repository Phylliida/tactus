#!/usr/bin/env bash
# Set up the Tactus Lean project with precompiled Mathlib.
#
# Downloads pre-built .olean files (~2 GB) from Mathlib's CI cache.
# No compilation needed — takes ~2-5 minutes.
#
# Prerequisites: Lean 4 + lake on PATH
# Usage:
#   ./scripts/setup-mathlib.sh
#   nix-shell -p lean4 --run ./scripts/setup-mathlib.sh
#   TACTUS_LEAN_PROJECT=/custom/path ./scripts/setup-mathlib.sh

set -euo pipefail

# Detect Lean version
LEAN_RAW=$(lean --version 2>/dev/null | grep -oP 'version \K[^,]+' || echo "")
if [ -z "$LEAN_RAW" ]; then
    echo "Error: lean not found. Install via elan or nix-shell -p lean4." >&2
    exit 1
fi

# Match Mathlib tag to Lean version (e.g., Lean 4.25.0 → Mathlib v4.25.0)
MATHLIB_TAG="v${LEAN_RAW}"

# Default: tactus/lean-project/ (repo-local)
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
DEFAULT_DIR="$(cd "$SCRIPT_DIR/../../.." && pwd)/lean-project"
PROJECT_DIR="${TACTUS_LEAN_PROJECT:-$DEFAULT_DIR}"

echo "Lean version:    $LEAN_RAW"
echo "Mathlib tag:     $MATHLIB_TAG"
echo "Project dir:     $PROJECT_DIR"
echo

mkdir -p "$PROJECT_DIR"
echo "leanprover/lean4:v${LEAN_RAW}" > "$PROJECT_DIR/lean-toolchain"

cat > "$PROJECT_DIR/lakefile.lean" << EOF
import Lake
open Lake DSL

package tactus where
  leanOptions := #[⟨\`autoImplicit, false⟩]

@[default_target]
lean_lib TactusCheck where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "$MATHLIB_TAG"
EOF

echo "Downloading precompiled Mathlib oleans (~2 GB, no compilation)..."
cd "$PROJECT_DIR"
lake update
lake exe cache get

echo
echo "Done! Mathlib $MATHLIB_TAG ready at $PROJECT_DIR"
