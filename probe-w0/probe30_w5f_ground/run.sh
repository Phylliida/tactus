#!/usr/bin/env bash
# W5f v2 GROUNDING probe — RUNG 1 (board bootstrap-57). Grounds the CALL-fragment
# leaf oracles fn/fnN to REAL emitted defs. Imports (obstacle D solved by rename):
#   - tactus-core  TactusDefs_lib_exec        (lib.render_exp / lib.RawExp / …)
#   - probe29      w5f_v2_match_sem           (W5f.SymEnv / edenote / FACT 5,8)
#   - fixture      TactusDefs_fixlib_exec__root (fixlib.sq / fixlib.g2, renamed cone)
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

echo "== W5f v2 grounding probe — RUNG 1 (fn/fnN pinned to renamed emitter output) =="
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
  echo "PASS ✓ — RUNG 1 lands: fn/fnN grounded to fixlib.sq/fixlib.g2, hfn/hfnN by rfl (rc=0)"
else
  echo "FAIL ✗ — rc=$rc"
fi
exit $rc
