#!/usr/bin/env bash
# probe35 — wf-preservation archetype (board bootstrap-73, final rung to 67/67).
# Hand-written preservation lemmas against the CURRENT tactus-core emission:
#   frame_append_wf — structural recursion through Box.deref (rec_1 territory)
#   ret_frame_wf    — non-recursive composition (the wp_stm_sound demand site)
# PASS = elaborates rc=0, no sorryAx, axiom-FREE (defeq iota carries all).
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
CORE="$ROOT/tactus-core"
PRELUDES="$(ls -d "$HOME"/.cache/tactus/prelude-* 2>/dev/null | tr '\n' ':')"
LP="$CORE/out/lib:$CORE/out/lib/pkg:${PRELUDES%:}"

echo "== probe35 wf-preservation archetype =="
out=$(LEAN_PATH="$LP" lean "$HERE/closed.lean" 2>&1)
rc=$?
echo "$out"
if [ $rc -eq 0 ] && ! echo "$out" | grep -q sorryAx; then
  echo "=> PASS"
else
  echo "=> FAIL"
fi
