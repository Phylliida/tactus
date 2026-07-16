#!/usr/bin/env bash
# W2b mutation-kill runner (bootstrap-07).
#
# Regenerates Mutations.lean from the LIVE add_capped cert, then elaborates it.
# The file asserts, all by `decide`:
#   * baseline    goals_eq (ref_wp ctx sst) goals = 1   (unperturbed bridge closes)
#   * 5 mutations goals_eq (ref_wp ctx <sst'|goals'>)  = 0   (each single edit FLIPS)
# So a single `lean` elaboration with rc=0 proves: the bridge closes AND every
# one of the 5 perturbations is provably rejected. If ANY mutation failed to
# flip (still = 1), its `= 0 := by decide` example errors and rc != 0.
#
# This is the sensitivity half of W2b (DESIGN 2.4.2): green-on-everything proves
# nothing unless a mismatch is provably killed.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
CORE_OUT="$ROOT/tactus-core/out/lib"
PRELUDE="${TACTUS_PRELUDE:-$HOME/.cache/tactus/prelude-e81fbf9a86375c12}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
export LEAN_PATH="$CORE_OUT:$PRELUDE"

echo "== W2b mutation-kill runner =="
python3 "$HERE/gen.py" || exit 2

t0=$(date +%s%N)
"$LEAN_BIN" "$HERE/Mutations.lean"; rc=$?
t1=$(date +%s%N)
echo "elapsed: $(( (t1 - t0) / 1000000 ))ms   lean exit=$rc"
if [ $rc -eq 0 ]; then
  echo "MUTATION-KILL PASS ✓  (baseline closes; all 5 single-edit mutations provably flip 1->0)"
else
  echo "MUTATION-KILL FAIL ✗  (a mutation did NOT flip, or the baseline broke — see errors above)"
fi
exit $rc
