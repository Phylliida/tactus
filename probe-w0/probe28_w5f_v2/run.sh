#!/usr/bin/env bash
# W5f v2 soundness probe runner (board bootstrap-55). Elaborates the standalone
# probe against tactus-core's REAL emitted defs (lib.wp_stm / lib.frame_after /
# lib.render_exp / …), extending probe27 (W5f v1) by WIDENING the concrete leaf
# denotation `eval`/`edenote` to the W7 body fragment: App/AppN (grounded via a
# SymEnv fn-literal pinned to real Lean spec fns), Forall/Exists (genuine
# binders), Ite (decidable value condition). Match is scoped (flat-Int decode
# follow-on). The v1 Val-level core (wp_stm_sound iff, TOTAL over StmData) and
# the four v1 adequacy facts carry over untouched.
#
# Usage: probe-w0/probe28_w5f_v2/run.sh          (LEAN=<lean> to override)
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
CORE_OUT="$ROOT/tactus-core/out/lib"
PRELUDE="${TACTUS_PRELUDE:-$HOME/.cache/tactus/prelude-e81fbf9a86375c12}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
SRC="$HERE/w5f_v2_sem.lean"

export LEAN_PATH="$CORE_OUT:$PRELUDE"

echo "== W5f v2 probe (adequacy spine widened to the W7 body fragment: App/AppN/Forall/Exists/Ite) =="
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
  echo "PASS ✓ — adequacy spine widened to the W7 body fragment (rc=0)"
else
  echo "FAIL ✗ — rc=$rc"
fi
exit $rc
