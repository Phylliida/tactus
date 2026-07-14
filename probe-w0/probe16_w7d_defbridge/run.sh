#!/usr/bin/env bash
# W7d defs-layer bridge runner (board bootstrap-32).
#
# Elaborates probe16 against the REAL emitted tactus-core oleans
# (`tactus-core/out/lib`) + the tactus prelude — the same LEAN_PATH probe9 uses.
# The probe file's `example`s ARE the bridge: def_eq/dt_eq positives close (= 1),
# mutation negatives reject (= 0). rc=0 ⇒ every example elaborated as classified
# (so the real transcriber TEXT closes the LANDED render_def/def_eq, non-vacuously).
#
# Usage: probe-w0/probe16_w7d_defbridge/run.sh   (LEAN=<lean> / TACTUS_PRELUDE=<dir> to override)
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CORE_OUT="$ROOT/tactus-core/out/lib"
PRELUDE="${TACTUS_PRELUDE:-$HOME/.cache/tactus/prelude-e81fbf9a86375c12}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
SRC="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/probe16_w7d_defbridge.lean"

export LEAN_PATH="$CORE_OUT:$PRELUDE"

echo "== W7d defs-layer bridge probe =="
echo "core out : $CORE_OUT"
echo "prelude  : $PRELUDE"
echo "lean     : $LEAN_BIN"
echo "src      : $SRC"
echo

t0=$(date +%s%N); "$LEAN_BIN" "$SRC"; rc=$?; t1=$(date +%s%N)
echo "--- probe rc=$rc  wall=$(( (t1 - t0) / 1000000 ))ms ---"

# non-vacuity meta-check (expected to FAIL): the CORRECT def is not `= 0`.
# If `decide` accepted the false `def_eq … = 0` on a correct pair, the negatives
# would be rubber-stamped rather than testing genuine inequality.
META="$(mktemp --suffix=.lean)"; trap 'rm -f "$META"' EXIT
cat "$SRC" > "$META"
cat >> "$META" <<'EOF'
theorem META_should_fail : lib.def_eq (lib.render_def raw_tri) defdata_tri = 0 := by decide
EOF
"$LEAN_BIN" "$META" >/dev/null 2>&1; mrc=$?
if [ "$mrc" -ne 0 ]; then echo "meta-check OK: decide refuses the false '= 0' on a correct def (rc=$mrc)"; else echo "META-CHECK REGRESSION: decide accepted '= 0' on a correct def"; rc=1; fi

echo
if [ "$rc" -eq 0 ]; then echo "W7D DEF-BRIDGE PROBE OK ✓ (def_eq/dt_eq close on real transcriber output; kills non-vacuous)"; else echo "W7D DEF-BRIDGE PROBE FAILED ✗"; fi
exit "$rc"
