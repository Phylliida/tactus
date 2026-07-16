#!/usr/bin/env bash
# probe34 — Link-discharge L0 (board bootstrap-73, DESIGN-link-discharge.md §7).
# Hand-written discharge terms against the CURRENT tactus-core emission:
# the shapes the Link generator will emit. Regenerate tactus-core's out/lib
# first if stale (tactus-core/lib.rs header has the command).
# PASS = closed.lean elaborates with core-only axiom closures.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
CORE="$ROOT/tactus-core"
PRELUDES="$(ls -d "$HOME"/.cache/tactus/prelude-* 2>/dev/null | tr '\n' ':')"
LP="$CORE/out/lib:$CORE/out/lib/pkg:${PRELUDES%:}"

echo "== probe34 Link-discharge L0 =="
out=$(LEAN_PATH="$LP" lean "$HERE/closed.lean" 2>&1)
rc=$?
echo "$out"
echo
if [ $rc -eq 0 ] && ! echo "$out" | grep -q sorryAx; then
  echo "=> PASS: theorem-keyword fix synthesis + positional weave discharge +"
  echo "   termination-VC consumption all validated (shapes frozen for L1/L2)."
  exit 0
else
  echo "=> FAIL (rc=$rc): the frozen discharge shapes regressed, or the"
  echo "   emission drifted (VC theorem names carry line numbers — re-pin"
  echo "   them from tactus-core/out/lib/pkg after tactus-core edits)."
  exit 1
fi
