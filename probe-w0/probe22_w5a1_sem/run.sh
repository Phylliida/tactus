#!/usr/bin/env bash
# W5a-1 soundness probe runner (board bootstrap-49). Elaborates the standalone
# probe against tactus-core's REAL emitted defs (lib.wp_stm / lib.frame_after /
# lib.close_e / lib.frame_append / lib.goals_append / lib.diverges / lib.is_skip
# / lib.render_exp / lib.seed_frame), so the soundness theorem it proves is over
# the genuine emitted reference WP, not a re-inlined copy.
#
# The file's own `theorem`s ARE the probe: a single `lean` elaboration with rc=0
# proves that the reference WP is SOUND on the branching fragment
# {Skip, Assume, Assert, Seq, If} over an ARBITRARY frame telescope (FBind/∀,
# FHyp/→, FLet/let) — every emitted goal true ⟹ under the frame's binders every
# assert's obligation holds, with the leaf interpretation (hp/he/lv) fully opaque
# (valuation-parametric). Lifts probe21's isHypFrame-restricted W5a-0.
#
# Usage: probe-w0/probe22_w5a1_sem/run.sh          (LEAN=<lean> to override)
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
CORE_OUT="$ROOT/tactus-core/out/lib"
PRELUDE="${TACTUS_PRELUDE:-$HOME/.cache/tactus/prelude-e81fbf9a86375c12}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
SRC="$HERE/w5a1_sem.lean"

export LEAN_PATH="$CORE_OUT:$PRELUDE"

echo "== W5a-1 reference-WP soundness probe (Skip/Assume/Assert/Seq/If + ∀-params) =="
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
  echo "PASS ✓ — reference WP is sound on {Skip,Assume,Assert,Seq,If} + ∀-params (rc=0)"
else
  echo "FAIL ✗ — rc=$rc"
fi
exit $rc
