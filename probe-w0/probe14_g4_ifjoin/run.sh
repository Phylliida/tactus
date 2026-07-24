#!/usr/bin/env bash
# W6e G4.2 probe runner (board bootstrap-24). Elaborates the standalone probe
# against tactus-core's REAL emitted defs (ref_wp / goals_eq / render_exp /
# expr_eq + the Let/Not mirror vocabulary), so the bridge it proves is the
# genuine wired bridge, not a re-inlined copy.
#
# The file's own `example`s ARE the probe: a single `lean` elaboration with
# rc=0 proves ALL of —
#   (0) the current opaque bridge is 0 (the honest-fail is real),
#   (A) the WIRED deep bridge is 1 (the fix), + 2-goal count,
#   (B) render_exp(recompute) == the deep goal leaf (leaf 15 & 16),
#   (C) six single-drop mutations each FLIP the bridge 1→0.
# If any `= 1`/`= 0` were wrong, `decide` errors and rc != 0.
#
# Usage: probe-w0/probe14_g4_ifjoin/run.sh          (LEAN=<lean> to override)
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
CORE_OUT="$ROOT/tactus-core/out/lib"
# All prelude caches (probe9-style glob — a pinned pre-prelude-split dir
# lacks the collapsed bare TactusDefs and fails module resolution).
PRELUDES="$(ls -d "$HOME"/.cache/tactus/prelude-* 2>/dev/null | tr '\n' ':')"
PRELUDE="${TACTUS_PRELUDE:-${PRELUDES%:}}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
SRC="$HERE/probe14_g4_ifjoin.lean"

export LEAN_PATH="$CORE_OUT:$PRELUDE"

echo "== W6e G4.2 If-fold probe =="
echo "core out : $CORE_OUT"
echo "prelude  : $PRELUDE"
echo "lean     : $LEAN_BIN"
echo "src      : $SRC"
echo

t0=$(date +%s%N); "$LEAN_BIN" "$SRC"; rc=$?; t1=$(date +%s%N)
echo "--- probe rc=$rc  wall=$(( (t1 - t0) / 1000000 ))ms ---"

# non-vacuity meta-check (expected to FAIL): a ¬ over a CORRECT render-diff must
# be REFUSED by decide — proving the `= 0` kills test genuine inequality, not
# that decide rubber-stamps every negation.
META="$(mktemp --suffix=.lean)"; trap 'rm -f "$META"' EXIT
cat "$SRC" > "$META"
cat >> "$META" <<'EOF'
theorem META_should_fail : ¬ (lib.expr_eq (lib.render_exp impl15) deep15 = 1) := by decide
EOF
"$LEAN_BIN" "$META" >/dev/null 2>&1; mrc=$?
if [ "$mrc" -ne 0 ]; then echo "meta-check OK: decide refuses the false ¬ (rc=$mrc)"; else echo "META-CHECK REGRESSION: decide accepted ¬(a=a)"; rc=1; fi

echo
if [ "$rc" -eq 0 ]; then echo "G4.2 PROBE OK ✓ (opaque bridge 0; wired bridge 1; render diff matches; 6 kills flip)"; else echo "G4.2 PROBE FAILED ✗"; fi
exit "$rc"
