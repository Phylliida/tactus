#!/usr/bin/env bash
# W5f v2 MATCH-decode probe runner (board bootstrap-56). Elaborates the standalone
# probe against tactus-core's REAL emitted defs (lib.render_exp / lib.render_arms /
# …), extending probe28 (W5f v2) by landing the FAITHFUL `Match` denotation — the
# flat-Int datatype-value-decode layer: two new SymEnv oracles (ctorTag/ctorField),
# `bindArm` (BinderIdList fold), `evalArms` (joins the eval/evalList mutual block),
# and `edenote`/`edenoteArms` (mutual). `eval`/`edenote` are now faithfully TOTAL
# over the FULL ExprData vocab — no sentinel. All probe28 facts carry over.
#
# Usage: probe-w0/probe29_w5f_v2_match/run.sh    (LEAN=<lean> to override)
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
CORE_OUT="$ROOT/tactus-core/out/lib"
PRELUDE="${TACTUS_PRELUDE:-$HOME/.cache/tactus/prelude-e81fbf9a86375c12}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
SRC="$HERE/w5f_v2_match_sem.lean"

export LEAN_PATH="$CORE_OUT:$PRELUDE"

echo "== W5f v2 MATCH-decode probe (faithful Match: ctorTag/ctorField decode + bindArm + evalArms/edenoteArms) =="
echo "core out : $CORE_OUT"
echo "prelude  : $PRELUDE"
echo "lean     : $LEAN_BIN"
echo

t0=$(date +%s%N)
"$LEAN_BIN" "$SRC"
rc=$?
t1=$(date +%s%N)
echo
echo "elapsed: $(( (t1 - t0) / 1000000 )) ms"
if [ $rc -eq 0 ]; then
  echo "PASS ✓ — faithful Match denotation lands; eval/edenote total over full vocab (rc=0)"
else
  echo "FAIL ✗ — rc=$rc"
fi
exit $rc
