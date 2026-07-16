#!/usr/bin/env bash
# W5f v2 GROUNDING probe — RUNGS 1+2+3 (board bootstrap-57). Grounds the leaf oracles
# fn/fnN (rung 1, CALL fragment), proj/FieldProj (rung 2, over the real emitted
# fixlib.Point record), and ctorTag/ctorField (rung 3, over the real emitted fixlib.Tree
# enum + fixlib.tree_head match) to REAL emitted defs. Imports (obstacle D solved by rename):
#   - tactus-core  TactusDefs_lib_exec        (lib.render_exp / lib.RawExp / …)
#   - probe29      w5f_v2_match_sem           (W5f.SymEnv / edenote / FACT 5,8,9,10,11,12)
#   - fixture      TactusDefs_fixlib_exec__root (fixlib.sq/g2 + fixlib.Point + fixlib.Tree, renamed cone)
#
# The probe29 + fixlib oleans are built once by this script if missing/stale.
# Usage: probe-w0/probe30_w5f_ground/run.sh    (LEAN=<lean> to override)
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
CORE_OUT="$ROOT/tactus-core/out/lib"
PRELUDE="${TACTUS_PRELUDE:-$HOME/.cache/tactus/prelude-e81fbf9a86375c12}"
PROBE29="$ROOT/probe-w0/probe29_w5f_v2_match"
FIXLIB="$HERE/fixlib"
LEAN_BIN="${LEAN:-$(command -v lean)}"
SRC="$HERE/ground.lean"

echo "== W5f v2 grounding probe — RUNGS 1+2+3 (fn/fnN, proj, ctorTag/ctorField pinned to emitter output) =="
echo "core out : $CORE_OUT"
echo "probe29  : $PROBE29"
echo "fixlib   : $FIXLIB"
echo "lean     : $LEAN_BIN"
echo

# 1. build the renamed fixture cone olean (obstacle D) if missing/stale.
if [ ! -f "$FIXLIB/TactusDefs_fixlib_exec__root.olean" ] \
   || [ "$FIXLIB/TactusDefs_fixlib_exec__root.lean" -nt "$FIXLIB/TactusDefs_fixlib_exec__root.olean" ]; then
  echo "-- building fixlib olean --"
  ( cd "$FIXLIB" && LEAN_PATH="$PRELUDE" "$LEAN_BIN" \
      -o TactusDefs_fixlib_exec__root.olean TactusDefs_fixlib_exec__root.lean ) || exit 2
fi

# 2. build probe29's machinery olean if missing/stale.
if [ ! -f "$PROBE29/w5f_v2_match_sem.olean" ] \
   || [ "$PROBE29/w5f_v2_match_sem.lean" -nt "$PROBE29/w5f_v2_match_sem.olean" ]; then
  echo "-- building probe29 (w5f_v2_match_sem) olean --"
  ( cd "$PROBE29" && LEAN_PATH="$CORE_OUT:$PRELUDE" "$LEAN_BIN" \
      -o w5f_v2_match_sem.olean w5f_v2_match_sem.lean ) || exit 2
fi

# 3. elaborate the grounding probe against all four sources.
export LEAN_PATH="$CORE_OUT:$PRELUDE:$PROBE29:$FIXLIB"
t0=$(date +%s%N)
"$LEAN_BIN" "$SRC"
rc=$?
t1=$(date +%s%N)
echo
echo "elapsed: $(( (t1 - t0) / 1000000 )) ms"
if [ $rc -eq 0 ]; then
  echo "PASS ✓ — RUNGS 1+2+3 land: fn/fnN → fixlib.sq/g2 (rfl); proj → fixlib.Point.x/.y (base-2^64 encoding thm, omega); ctorTag/ctorField → fixlib.Tree/tree_head (parity encoding thm, omega) (rc=0)"
else
  echo "FAIL ✗ — rc=$rc"
fi
exit $rc
