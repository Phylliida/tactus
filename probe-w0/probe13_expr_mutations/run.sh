#!/usr/bin/env bash
# W6e expression-level mutation-kill runner (bootstrap-24).
#
# Regenerates ExprMutations.lean from the LIVE fixture certs, then elaborates it.
# The file asserts, all by `decide`, for four coercion/poison mutation classes
# (cast / deref / field / HasType-width, one per fixture fn):
#   * baseline   goals_eq (ref_wp ctx sst) goals     = 1   (deep bridge closes)
#   * kill       goals_eq (ref_wp ctx sst) goals_mut = 0   (single GOAL-side
#                                                            coercion drop FLIPS)
# One `lean` elaboration with rc=0 proves every baseline closes AND every
# coercion drop is provably rejected — the systematic Friction-2 kill. If any
# mutation failed to flip (still = 1), its `= 0 := by decide` example errors
# and rc != 0.
#
# This is the expression-granularity sibling of probe10_mutations (which kills
# at the GoalList structure level). The point (task W6e + DESIGN-W6-stageB §6):
# the deep symmetric compare catches a structurally-wrong ExprData that a
# stage-A string/atom-id compare would silent-pass.
#
# Usage: probe-w0/probe13_expr_mutations/run.sh        (auto-locates everything)
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
CORE_OUT="$ROOT/tactus-core/out/lib"
# All prelude caches (slim-prelude work mints new hashes; the collapsed
# bare TactusDefs ships inside the prelude — glob them all, probe9-style).
PRELUDES="$(ls -d "$HOME"/.cache/tactus/prelude-* 2>/dev/null | tr '\n' ':')"
PRELUDE="${TACTUS_PRELUDE:-${PRELUDES%:}}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
export LEAN_PATH="$CORE_OUT:$PRELUDE"

echo "== W6e expression-level mutation-kill runner =="
echo "certs  : $ROOT/bootstrap-fixture/out/lib/cert"
echo "core   : $CORE_OUT"
echo "lean   : $LEAN_BIN"
python3 "$HERE/gen.py" || exit 2

t0=$(date +%s%N)
"$LEAN_BIN" "$HERE/ExprMutations.lean"; rc=$?
t1=$(date +%s%N)
echo "elapsed: $(( (t1 - t0) / 1000000 ))ms   lean exit=$rc"
if [ $rc -eq 0 ]; then
  echo "EXPR MUTATION-KILL PASS ✓  (5 baselines close + kills flip 1->0 [incl. P1 poison-channel + the A5-restored deref class])"
else
  echo "EXPR MUTATION-KILL FAIL ✗  (a mutation did NOT flip, a baseline broke, or the parked A5 tripwire fired — see errors above)"
fi
exit $rc
