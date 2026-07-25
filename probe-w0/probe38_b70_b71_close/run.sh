#!/usr/bin/env bash
# b70/b71 close-out runner (endgame A1). Regenerates B70B71Close.lean
# from the LIVE fixture certs, then elaborates it. One rc=0 run proves:
#   b71: use_clamped ∀-path bridge closes + 2 frame mutations flip
#   b70: vec_read precondition goal closes per-goal + req mutation flips
#        + the goal-1 stage-B honest-fail =0 tripwire holds (fires at A7)
# See gen.py docstring for the claim table.
#
# Usage: probe-w0/probe38_b70_b71_close/run.sh
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
CORE_OUT="$ROOT/tactus-core/out/lib"
# All prelude caches (probe9-style glob — the collapsed bare TactusDefs
# ships inside the prelude).
PRELUDES="$(ls -d "$HOME"/.cache/tactus/prelude-* 2>/dev/null | tr '\n' ':')"
PRELUDE="${TACTUS_PRELUDE:-${PRELUDES%:}}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
export LEAN_PATH="$CORE_OUT:$PRELUDE"

echo "== b70/b71 close-out runner (endgame A1) =="
echo "certs  : $ROOT/bootstrap-fixture/out/lib/cert"
echo "core   : $CORE_OUT"
echo "lean   : $LEAN_BIN"
python3 "$HERE/gen.py" || exit 2

t0=$(date +%s%N)
"$LEAN_BIN" "$HERE/B70B71Close.lean"; rc=$?
t1=$(date +%s%N)
echo "elapsed: $(( (t1 - t0) / 1000000 ))ms   lean exit=$rc"
if [ $rc -eq 0 ]; then
  echo "B70/B71 CLOSE-OUT PASS ✓  (∀-path close + 2 kills; vec_read goal-0 close + kill; A7 tripwire holds)"
else
  echo "B70/B71 CLOSE-OUT FAIL ✗  (a baseline broke, a kill did not flip, or the A7 tripwire fired — see errors above)"
fi
exit $rc
