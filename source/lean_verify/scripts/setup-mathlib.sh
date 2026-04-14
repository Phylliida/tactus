#!/usr/bin/env bash
# Set up the Tactus Lean project with precompiled Mathlib.
#
# This downloads pre-built Mathlib .olean files (~2 GB) from Mathlib's CI cache.
# No compilation needed — takes ~2-5 minutes on a decent connection.
#
# Prerequisites:
#   - Lean 4 (via `nix-shell -p lean4` or elan)
#   - lake (comes with Lean 4)
#
# Usage:
#   ./scripts/setup-mathlib.sh
#   # or with nix:
#   nix-shell -p lean4 --run ./scripts/setup-mathlib.sh

set -euo pipefail

# Detect system Lean version
LEAN_RAW_VERSION=$(lean --version 2>/dev/null | grep -oP 'version \K[^,]+' || echo "")
if [ -z "$LEAN_RAW_VERSION" ]; then
    echo "Error: lean not found on PATH. Install via elan or nix-shell -p lean4."
    exit 1
fi
LEAN_VERSION="leanprover/lean4:v${LEAN_RAW_VERSION}"

PROJECT_DIR="${TACTUS_PROJECT_DIR:-$HOME/.tactus/lean-project}"

echo "Setting up Tactus Lean project at $PROJECT_DIR"
echo "Lean version: $LEAN_VERSION"
echo

mkdir -p "$PROJECT_DIR"

# Pin Lean version to match system
echo "$LEAN_VERSION" > "$PROJECT_DIR/lean-toolchain"

# Write lakefile — uses Mathlib master (compatible with latest Lean)
cat > "$PROJECT_DIR/lakefile.lean" << 'EOF'
import Lake
open Lake DSL

package tactus where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib TactusCheck where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
EOF

# Download precompiled Mathlib oleans (no compilation)
echo "Downloading precompiled Mathlib oleans..."
echo "This downloads ~2 GB of pre-built files. No compilation needed."
echo
cd "$PROJECT_DIR"
lake update
lake exe cache get

echo
echo "Done! Mathlib is ready at $PROJECT_DIR"
echo "Tactus will automatically use this project for Mathlib tactics."
