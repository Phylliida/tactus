#!/usr/bin/env bash
# W5b soundness probe runner (board bootstrap-50). Elaborates the standalone
# probe against tactus-core's REAL emitted defs (lib.wp_stm / lib.frame_after /
# lib.close_e / lib.close_each_e / lib.ret_frame / lib.frame_append /
# lib.goals_append / lib.diverges / lib.is_skip / lib.render_exp /
# lib.seed_frame), so the soundness theorem it proves is over the genuine
# emitted reference WP, not a re-inlined copy.
#
# A single `lean` elaboration with rc=0 proves the reference WP is SOUND on the
# fragment {Skip, Assume, Assert, Assign, Seq, If, Call, Ret, DeadEnd} over an
# ARBITRARY frame telescope, leaf interpretation (hp/he/lv) fully opaque
# (valuation-parametric). Extends probe22's {Skip,Assume,Assert,Seq,If}.
#
# Usage: probe-w0/probe23_w5b_sem/run.sh          (LEAN=<lean> to override)
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
CORE_OUT="$ROOT/tactus-core/out/lib"
PRELUDE="${TACTUS_PRELUDE:-$HOME/.cache/tactus/prelude-e81fbf9a86375c12}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
SRC="$HERE/w5b_sem.lean"

export LEAN_PATH="$CORE_OUT:$PRELUDE"

echo "== W5b reference-WP soundness probe (Call/Ret/DeadEnd + live If fall-through) =="
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
  echo "PASS ✓ — reference WP is sound on {Skip,Assume,Assert,Assign,Seq,If,Call,Ret,DeadEnd} (rc=0)"
else
  echo "FAIL ✗ — rc=$rc"
fi
exit $rc
