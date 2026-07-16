#!/usr/bin/env bash
# W7 tgt-slice def/dt cert emit (board bootstrap-37).
#
# Emits `.defcert`/`.dtcert` files for the `symbol` module of tactus-group-theory
# — real corpus code, distinct from the bootstrap-fixture family — so the W7
# defs-layer bridge can be run over a genuine tgt slice.
#
# Uses the SAME fork verus binary tgt's check.sh uses (md5-identical to the
# tactus-bootstrap one carrying the W7 def-cert wire). --emit-lean skips the Lean
# goal discharge; we only want the cert emission. -V cache for speed.
set -uo pipefail
TGT="/home/bepis/prog/verus-cad/tactus-group-theory"
VERUS="/home/bepis/prog/verus-cad/tactus-bootstrap/source/target-verus/release/verus"
OUT="/home/bepis/prog/verus-cad/tactus-bootstrap/probe-w0/probe20_w7_tgtslice/out"
mkdir -p "$OUT"

echo "== W7 tgt-slice emit: module=symbol =="
echo "verus : $VERUS"
echo "out   : $OUT"
echo

TACTUS_LEAN_OUT="$OUT" "$VERUS" \
  --lean-backend -V cache --crate-type=lib \
  --emit-lean --lean-all-proofs --tactus-emit-cert \
  --verify-module symbol \
  "$TGT/src/lib.rs" 2>&1
rc=$?
echo
echo "[emit.sh] verus exit $rc"
echo "== emitted cert files =="
find "$OUT" -name '*.defcert.lean' -o -name '*.dtcert.lean' 2>/dev/null | sort
exit "$rc"
