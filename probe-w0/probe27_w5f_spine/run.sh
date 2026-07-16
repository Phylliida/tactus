#!/usr/bin/env bash
# W5f soundness probe runner (board bootstrap-53). Elaborates the standalone
# probe against tactus-core's REAL emitted defs (lib.wp_stm / lib.frame_after /
# lib.frame_append / lib.close_e / lib.render_exp / lib.seed_frame), so the
# closure-soundness theorems it proves are over the genuine emitted reference WP,
# not a re-inlined copy.
#
# A single `lean` elaboration with rc=0 proves: (1) the full W5c core carries
# over (wp_stm_sound iff, TOTAL over StmData, arbitrary frame telescope); (2)
# CLOSURES need NO new StmData arm — a closure IS `Seq (DeadEnd body) (Assume
# external_spec)`; closure creation reduces EXACTLY to the body obligation under
# the enclosing frame (closure_creation_sound); (3) the DeadEnd ISOLATES the
# body's assumptions from the continuation (closure_deadend_isolates leaves the
# continuation UNGATED, vs seq_assume_gates which gates it), and the trailing
# Assume FORWARDS the external contract (closure_forwards_contract). Leaf
# interpretation (hp/he/lv) fully opaque (valuation-parametric).
#
# Usage: probe-w0/probe26_w5f_sem/run.sh          (LEAN=<lean> to override)
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
CORE_OUT="$ROOT/tactus-core/out/lib"
PRELUDE="${TACTUS_PRELUDE:-$HOME/.cache/tactus/prelude-e81fbf9a86375c12}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
SRC="$HERE/w5f_sem.lean"

export LEAN_PATH="$CORE_OUT:$PRELUDE"

echo "== W5f reference-WP soundness probe (adequacy spine: Val-level holds → user-facing Props) =="
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
  echo "PASS ✓ — adequacy spine: Val-level holds lifts to user-facing Props (rc=0)"
else
  echo "FAIL ✗ — rc=$rc"
fi
exit $rc
