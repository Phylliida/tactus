#!/usr/bin/env bash
# W7-AppN probe runner (board bootstrap-34). Pure Lean core — no prelude imports,
# no tactus-core oleans, no Mathlib. Elaborates the standalone probe; the file's
# own `theorem`s ARE the bridge (correct AppN/CallN renders close by decide+rfl;
# dropped / mis-placed / spurious per-arg coercions are provably unequal). rc=0 ⇒
# every bridge behaved as classified and the axiom closure is clean.
#
# Also runs the non-vacuity meta-check: asserting ¬(a=a) on a CORRECT render must
# FAIL (nonzero) — proving the `_kill` theorems test genuine inequality, not that
# `decide` rubber-stamps every negation.
#
# Usage: probe-w0/probe18_appn/run.sh   (LEAN=<lean> to override)
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_BIN="${LEAN:-$(command -v lean)}"
SRC="$HERE/probe18_appn.lean"

echo "== W7-AppN (multi-arg CallN/AppN per-arg-TypData) probe =="
echo "lean : $LEAN_BIN"
echo "src  : $SRC"
echo

t0=$(date +%s%N); "$LEAN_BIN" "$SRC"; rc=$?; t1=$(date +%s%N)
echo "--- probe rc=$rc  wall=$(( (t1 - t0) / 1000000 ))ms ---"

# non-vacuity meta-check (expected to FAIL): a correct render is NOT unequal.
META="$(mktemp --suffix=.lean)"; trap 'rm -f "$META"' EXIT
cat "$SRC" > "$META"
cat >> "$META" <<'EOF'
theorem META_should_fail : ¬ (render_exp raw_B = prod_B_ok) := by decide
EOF
"$LEAN_BIN" "$META" >/dev/null 2>&1; mrc=$?
if [ "$mrc" -ne 0 ]; then echo "meta-check OK: decide refuses the false ¬ (rc=$mrc)"; else echo "META-CHECK REGRESSION: decide accepted ¬(a=a)"; rc=1; fi

echo
if [ "$rc" -eq 0 ]; then echo "W7-AppN PROBE OK ✓ (all multi-arg bridges behave; kills non-vacuous; axioms clean)"; else echo "W7-AppN PROBE FAILED ✗"; fi
exit "$rc"
