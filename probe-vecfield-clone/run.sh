#!/usr/bin/env bash
# Repro for the final e2e residue (test_exec_vec_field_index_clone).
# Regenerate the artifact first:
#   cd source && vargo test --release -p rust_verify_test --test tactus -- test_exec_vec_field_index_clone
# Then:
set -e
cd "$(dirname "$0")/.."
ART=$(ls -td source/target/release/test_inputs/*-test_exec_vec_field_index_clone | head -1)/tactus-lean/test_crate
PRE=$(ls -dt ~/.cache/tactus/prelude-* | head -1)
export LEAN_PATH="$(cd lean-project && lake env printenv LEAN_PATH):$PRE:$PWD/$ART"
echo "== hand proof (granted: strictly_cloned Int a b -> a = b) — expect CLEAN"
lean probe-vecfield-clone/repro_hand_proof.lean
echo "== derived closer with same granted fact — expect FAIL (tactic gap)"
lean probe-vecfield-clone/repro_derived_closer.lean || true
