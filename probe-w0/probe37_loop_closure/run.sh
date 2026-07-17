#!/usr/bin/env bash
# probe37 — THE LOOP CLOSURE (board bootstrap-66, after bootstrap-73).
# The adequacy spine consumes the AUTHORED, kernel-checked
# lib.ref_wp_sound_closed (Link module) — the hand soundness induction is
# gone. PASS = elaborates rc=0, no sorryAx, closures recorded.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
CORE="$ROOT/tactus-core"
PRELUDES="$(ls -d "$HOME"/.cache/tactus/prelude-* 2>/dev/null | tr '\n' ':')"
LP="$CORE/out/lib:$CORE/out/lib/pkg:$HERE:${PRELUDES%:}"

echo "== probe37 loop closure =="
# The Link module ships as .lean only (the gate elaborates it in-memory);
# build its olean once here so the spine can import it.
if [ ! -f "$HERE/TactusLink_lib_exec.olean" ] || \
   [ "$CORE/out/lib/pkg/TactusLink_lib_exec.lean" -nt "$HERE/TactusLink_lib_exec.olean" ]; then
  echo "-- building Link olean"
  cp "$CORE/out/lib/pkg/TactusLink_lib_exec.lean" "$HERE/TactusLink_lib_exec.lean"
  LEAN_PATH="$LP" lean "$HERE/TactusLink_lib_exec.lean" \
    -o "$HERE/TactusLink_lib_exec.olean" || exit 1
fi
out=$(LEAN_PATH="$LP" lean "$HERE/loop_closure_sem.lean" 2>&1)
rc=$?
echo "$out"
if [ $rc -eq 0 ] && ! echo "$out" | grep -q sorryAx; then
  echo "=> PASS: the loop is closed — adequacy spine over the authored theorem"
else
  echo "=> FAIL"
fi
exit $rc
