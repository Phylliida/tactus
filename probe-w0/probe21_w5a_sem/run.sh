#!/usr/bin/env bash
# W5a-0 soundness probe runner (board bootstrap-49). Elaborates the standalone
# probe against tactus-core's REAL emitted defs (lib.wp_stm / lib.frame_after /
# lib.close_e / lib.goals_append / lib.render_exp), so the soundness theorem it
# proves is over the genuine emitted reference WP, not a re-inlined copy.
#
# The file's own `theorem`s ARE the probe: a single `lean` elaboration with rc=0
# proves that the reference WP is SOUND on the straight-line fragment
# {Skip, Assume, Assert, Seq} — every emitted goal true ⟹ every assert's
# obligation holds under its accumulated hypothesis context, with the leaf
# interpretation (hp/he) fully opaque (valuation-parametric).
#
# Usage: probe-w0/probe21_w5a_sem/run.sh          (LEAN=<lean> to override)
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
CORE_OUT="$ROOT/tactus-core/out/lib"
PRELUDE="${TACTUS_PRELUDE:-$HOME/.cache/tactus/prelude-e81fbf9a86375c12}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
SRC="$HERE/w5a_sem.lean"

export LEAN_PATH="$CORE_OUT:$PRELUDE"

echo "== W5a-0 reference-WP soundness probe =="
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
  echo "PASS ✓ — reference WP is sound on the straight-line fragment (rc=0)"
else
  echo "FAIL ✗ — rc=$rc"
fi
exit $rc
