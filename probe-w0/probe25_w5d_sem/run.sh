#!/usr/bin/env bash
# W5d soundness probe runner (board bootstrap-52). Elaborates the standalone
# probe against tactus-core's REAL emitted defs (lib.wp_stm / lib.frame_after /
# lib.frame_append / lib.close_e / lib.render_exp / lib.seed_frame), so the
# prophecy-soundness theorem it proves is over the genuine emitted reference WP,
# not a re-inlined copy.
#
# A single `lean` elaboration with rc=0 proves: (1) the full W5c core carries
# over (wp_stm_sound iff, TOTAL over StmData, arbitrary frame telescope); (2)
# PROPHECY (`&mut`, the ∀-final-value model) is faithfully realized — the
# reference WP for `resolve; assert P(*x)` reduces EXACTLY to `∀ x_fut,
# resolve(x_fut) → P(x_fut)` (prophecy_sound); (3) the resolve pin is placed
# temporally-correctly (resolve BEFORE gates the obligation, resolve AFTER does
# not — prophecy_swapped_sound), discharging the placement worry. Leaf
# interpretation (hp/he/lv) fully opaque (valuation-parametric).
#
# Usage: probe-w0/probe25_w5d_sem/run.sh          (LEAN=<lean> to override)
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
CORE_OUT="$ROOT/tactus-core/out/lib"
PRELUDE="${TACTUS_PRELUDE:-$HOME/.cache/tactus/prelude-e81fbf9a86375c12}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
SRC="$HERE/w5d_sem.lean"

export LEAN_PATH="$CORE_OUT:$PRELUDE"

echo "== W5d reference-WP soundness probe (&mut / prophecy: ∀-final-value + resolve) =="
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
  echo "PASS ✓ — reference WP is sound for &mut/prophecy (∀-final-value model) (rc=0)"
else
  echo "FAIL ✗ — rc=$rc"
fi
exit $rc
