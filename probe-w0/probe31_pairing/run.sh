#!/usr/bin/env bash
# bootstrap-58 FEASIBILITY probe — the invertible unbounded pairing the deferred
# Node-child decode needs, proven self-contained (no Mathlib, no wf, standard
# axioms only). Fuel-structural bit-interleaving: pair / unfst / unsnd + two
# round-trips + injectivity + the Int→Nat zig-zag seam. NO imports beyond Init,
# so it needs no oleans — just the Nix lean.
# Usage: probe-w0/probe31_pairing/run.sh    (LEAN=<lean> to override)
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_BIN="${LEAN:-$(command -v lean)}"
SRC="$HERE/pairing.lean"

echo "== bootstrap-58 feasibility probe — self-contained injective bit-interleave pairing =="
echo "lean : $LEAN_BIN"
echo

t0=$(date +%s%N)
"$LEAN_BIN" "$SRC"
rc=$?
t1=$(date +%s%N)
echo
echo "elapsed: $(( (t1 - t0) / 1000000 )) ms"
if [ $rc -eq 0 ]; then
  echo "PASS ✓ — pair/unfst/unsnd round-trip + pair_injective + unzz_zz, all [propext, Quot.sound] (no sorryAx, no Mathlib) (rc=0)"
else
  echo "FAIL ✗ — rc=$rc"
fi
exit $rc
