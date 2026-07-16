#!/usr/bin/env bash
# probe33 — W5 authoring SHAPE de-risk (board bootstrap-60).
# Runs the REAL tactus binary with the FULL Lean discharge (--lean-all-proofs,
# NO --emit-lean) on an isolated mini-W5c crate, testing the four model shapes
# probe32 did not cover (M1 spec-closure literals / M2 nested spec_fn types /
# M3 recursion under `forall` / M4 induction THROUGH the ∀ arm).
# PASS = "0 errors" — the state-generic authoring idiom closes everything.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
VERUS="$ROOT/source/target-verus/release/verus"
OUT="$HERE/out"
mkdir -p "$OUT"

echo "== probe33 W5 authoring shape =="
echo "verus : $VERUS"
echo "out   : $OUT"
echo

t0=$(date +%s%N)
TACTUS_LEAN_OUT="$OUT" "$VERUS" \
  --crate-type=lib --lean-backend --lean-all-proofs -V cache \
  "$HERE/lib.rs" 2>&1 | tee "$OUT/run.log"
rc=${PIPESTATUS[0]}
t1=$(date +%s%N)
echo
echo "elapsed: $(( (t1 - t0) / 1000000 )) ms"
echo
echo "== PASS/FAIL gate (0 errors == the frozen authoring shape holds) =="
echo "M1 spec-closure literal (upd) / M2 nested spec_fn (oracle over St) /"
echo "M3 recursion under forall (FBind/All arms): all spec fns + u_* verify."
echo "M4 induction through the ∀ arm: close_leaf_sem + wp_stm_sound verify in"
echo "   the STATE-GENERIC shape (∀st in the ensures; no facts under binders —"
echo "   proof-fn calls inside assert-forall-by are DROPPED by the backend,"
echo "   rendering as True; see REPORT.md F1/F2)."
res=$(grep -E "verification results" "$OUT/run.log" | tail -1)
echo "results: ${res#*verification results:: }"
if echo "$res" | grep -qE "0 errors"; then
  echo "=> PASS: the bootstrap-61..64 authoring shape is frozen and validated."
  exit 0
else
  echo "=> FAIL: expected '0 errors'. Re-read REPORT.md; the shape regressed."
  exit 1
fi
