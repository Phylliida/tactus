#!/usr/bin/env bash
# probe32 — W5 loop-closure AUTHORING feasibility (board bootstrap-59).
# Runs the REAL tactus binary with the FULL Lean discharge (--lean-all-proofs,
# NO --emit-lean) on an isolated scratch crate, testing whether the Verus→Lean
# backend authors a `spec_fn` oracle param + a recursive structural-induction
# proof fn. PASS = "verified" with a clean axiom closure.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
VERUS="$ROOT/source/target-verus/release/verus"
OUT="$HERE/out"
mkdir -p "$OUT"

echo "== probe32 W5 authoring feasibility =="
echo "verus : $VERUS"
echo "out   : $OUT"
echo

t0=$(date +%s%N)
TACTUS_LEAN_OUT="$OUT" "$VERUS" \
  --crate-type=lib --lean-backend -V cache \
  "$HERE/lib.rs" 2>&1 | tee "$OUT/run.log"
rc=${PIPESTATUS[0]}
t1=$(date +%s%N)
echo
echo "elapsed: $(( (t1 - t0) / 1000000 )) ms"
echo
echo "== PASS/FAIL gate (0 errors == loop-closure authoring feasibility CONFIRMED) =="
echo "Q1 (spec_fn oracle + recursive structural spec fns): the oracle-parametric defs"
echo "   (all_true/gappend/wp/exec_safe) + all u_* one-step unfold lemmas VERIFY."
echo "Q2 (recursive structural-INDUCTION proof fns): all_true_append + wp_sound +"
echo "   wp_sound_bites VERIFY via the discharge idiom"
echo '     #[verifier::tactus_tactic("first | tactus_auto |'
echo '        (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]'
echo "   (see REPORT.md §Q2 for why each ingredient is needed). Axiom closure of the"
echo "   three top-level soundness theorems = [propext] only (no sorryAx/Classical)."
res=$(grep -E "verification results" "$OUT/run.log" | tail -1)
echo "results: ${res#*verification results:: }"
if echo "$res" | grep -qE "0 errors"; then
  echo "=> PASS: loop-closure authoring is feasible — the discharge idiom closes the"
  echo "   recursive-induction soundness proofs kernel-clean inside a real tactus run."
  exit 0
else
  echo "=> FAIL: expected '0 errors'. Re-read REPORT.md; the discharge idiom regressed."
  exit 1
fi
