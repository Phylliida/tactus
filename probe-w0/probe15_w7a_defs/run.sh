#!/usr/bin/env bash
# W7a probe runner (board bootstrap-26). Pure Lean core — no prelude imports,
# no tactus-core oleans, no Mathlib. Elaborates the standalone probe; the
# file's own `theorem`s ARE the bridge (correct DefData/DtData close by
# decide+rfl; mutated bodies/ctors/measures are provably unequal). rc=0 ⇒ every
# bridge behaved as classified and the axiom closure is clean.
#
# Also runs the non-vacuity meta-check: asserting ¬(a=a) on a CORRECT def must
# FAIL (nonzero) — proving the `_kill` theorems test genuine inequality, not
# that `decide` rubber-stamps every negation.
#
# Usage: probe-w0/probe15_w7a_defs/run.sh   (LEAN=<lean> to override)
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_BIN="${LEAN:-$(command -v lean)}"
SRC="$HERE/probe15_w7a_defs.lean"

echo "== W7a defs-layer probe =="
echo "lean : $LEAN_BIN"
echo "src  : $SRC"
echo

t0=$(date +%s%N); "$LEAN_BIN" "$SRC"; rc=$?; t1=$(date +%s%N)
echo "--- probe rc=$rc  wall=$(( (t1 - t0) / 1000000 ))ms ---"

# non-vacuity meta-check (expected to FAIL): a correct def is NOT unequal
META="$(mktemp --suffix=.lean)"; trap 'rm -f "$META"' EXIT
cat "$SRC" > "$META"
cat >> "$META" <<'EOF'
theorem META_should_fail : ¬ (render_def raw_tri = prod_tri_ok) := by decide
EOF
"$LEAN_BIN" "$META" >/dev/null 2>&1; mrc=$?
if [ "$mrc" -ne 0 ]; then echo "meta-check OK: decide refuses the false ¬ (rc=$mrc)"; else echo "META-CHECK REGRESSION: decide accepted ¬(a=a)"; rc=1; fi

echo
if [ "$rc" -eq 0 ]; then echo "W7A PROBE OK ✓ (all defs-layer bridges behave; kills non-vacuous; axioms clean)"; else echo "W7A PROBE FAILED ✗"; fi
exit "$rc"
