#!/usr/bin/env bash
# W2b bridge runner (bootstrap-07).
#
# For each freshly-emitted fixture cert `<fn>.cert.lean`, construct the bridge
#   example : lib.goals_eq (lib.ref_wp cert_<fn>_ctx cert_<fn>_sst)
#                          cert_<fn>_goals = 1 := by decide   (and by rfl)
# and elaborate it against tactus-core's emitted defs (which carry ref_wp /
# goals_eq + the mirror types). Records rc + wall-clock per fn.
#
# The cert files are gitignored/regenerable; this runner CONSUMES whatever is
# on disk in bootstrap-fixture/out/lib/cert/. Regen recipe: see
# board/bootstrap-15 Progress (vargo release build + --tactus-emit-cert).
#
# Classification (from the W2a/15/16/17 arc, DESIGN-W2-refwp.md §2.4/§5):
#   CLOSE      — expected to bridge (refWp reconstructs production verbatim).
#   HONEST-FAIL — a DOCUMENTED stage-A caveat (§2.4.1): the certificate is
#                 SOUND precisely because it does NOT silent-pass here. A
#                 honest-fail that suddenly CLOSED is a regression (refWp went
#                 lax or a caveat was silently "fixed") and this runner FAILS
#                 on it too.
#
# Usage: probe-w0/probe9_bridge/run.sh        (auto-locates everything)
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CERT_DIR="$ROOT/bootstrap-fixture/out/lib/cert"
CORE_OUT="$ROOT/tactus-core/out/lib"
# All prelude caches (slim-prelude work mints new hashes; the collapsed
# bare TactusDefs ships inside the prelude — glob them all, probe37-style).
PRELUDES="$(ls -d "$HOME"/.cache/tactus/prelude-* 2>/dev/null | tr '\n' ':')"
PRELUDE="${PRELUDES%:}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

export LEAN_PATH="$CORE_OUT:$CORE_OUT/pkg:$PRELUDE"

# fns that are DOCUMENTED honest-fails (a leaf-rendering / stage-A-scope
# divergence where the bridge SOUNDLY does not close). Each has a recorded
# reason (see REPORT.md + DESIGN-W2-refwp.md §5 triage). Everything else must
# CLOSE. A honest-fail that suddenly CLOSES is a regression and fails the run.
# NOTE (bootstrap-18, 2026-07-13): head_exec was FIXED and is now expected-CLOSE.
# The serializer's oblig_leaf / neg_oblig_leaf now render through the binder-aware
# render_ctx() (with_binder_typs(caller_param_typs) + with_fn_map) — byte-for-byte
# production's WpCtx postcondition ctx — so the ensures `*t` derefs to `t.deref`
# and the obligation leaf cancels across the bridge (old leaf 3 vs 6 → one leaf).
# Removed from the honest-fail set; it must now close-ok like the other fixtures.
# NOTE (bootstrap-24 G4.3, 2026-07-14): max_u64 was FIXED by the W6e value-if-lift
# recompute. The serializer now recomputes the branch-folded implication
# obligations `Ret([x<y -> let r:=(let m:=y;m); r≥x∧r≥y, ¬(x<y) -> …], RetNone)`
# (`lift_if_raw`, mirroring production's `lift_if_value_coerced`) and deepens the
# matching `Implies`-topped goal leaves (`lexpr_to_exprdata` Let/Not arms), so the
# FROZEN refWp reproduces production's two branch-split goals. Removed from the
# honest-fail set; it must now close-ok. (Pinned end-to-end by probe14.)
honest_fail_reason() {
  case "$1" in
    # count_down: FIXED by bootstrap-19 (2026-07-15). The two-way If-join
    # (both branches fall through to a common Ret) is now desugared IN THE
    # SERIALIZER (Option 2): `Seq(If(t,e), rest)` → `If(t;rest, e;rest)`, so
    # the FROZEN refWp reproduces production's 4 goals via its flat If/Seq
    # arms. (Option 1 — teach refWp — was proven infeasible: it forces
    # WellFounded.fix, which `decide` cannot reduce.) Now expected-CLOSE.
    # NOTE (bootstrap-80 A7, 2026-07-31): the ENTIRE stage-B deep-leaf
    # honest-fail class is FIXED — vec_read, count_to_len, vec_push7,
    # fill_zeros all CLOSE and are expected-CLOSE. Two landings:
    # (1) the callee-signature vocabulary: RawList carries per-arg
    # EXPECTED param typs (fn_param_typs_of, same VIR fn_map production
    # consults), render_exp derives the per-arg slot coercions via
    # reconcile_arg (the two-phase coerce_lexpr fragment: sort bridge +
    # wrapper reconciliation — Ref↔bare deref/mk-wrap, Ref↔Box,
    # passthrough when the callee param IS ref-typed, which was the
    # vec_read `v.deref` mis-derivation; `Int.ofNat` on Seq.index args).
    # The `Tactus.Ref.mk`/`Tactus.Box.mk` wraps are first-class
    # ExprData nodes (id-free; the reference cannot mint interned ids).
    # (2) F5 (pulled forward — vec_read's residual telescope divergence
    # was NOT the leaf class): production's bound predicates ran on the
    # UNINSTANTIATED declared typ, so a generic callee (`Seq.index` →
    # `Int`, `swap_incr` at `&mut T`) silently dropped the numeric
    # bound hyp; production now substitutes (instantiate_callee_typ,
    # single-sourced with the cert serializer's ret_typ_subst) at the
    # Phase-1 mut-arg / Phase-E ret / ∀-path ret / prophecy sites, and
    # the cert serializer's Phase-1 mirror substitutes identically.
    # If any of the four reverts to failing, that is a reclassify-
    # required regression (an A7 reconcile_arg or F5 substitution bug),
    # not a new honest-fail class.
    # NOTE (bootstrap-77, 2026-07-24): head_exec is expected-CLOSE again —
    # the A5 `ret_fork`/`StmData::IfCtor` arm mirrors production's
    # walk_let fork (N2 ctor frames on the positive branch, per-branch
    # RetLetH). If it reverts to failing, that is a fork-mirror
    # regression, not a reclassify.
    # bootstrap-78 S3 (2026-07-26): the mut-call FRAME machinery is
    # bridge-validated by call_inc + inc (both CLOSE: mut_post/ret
    # binders, bound hyp, ens hyp, plain rebind FLets, fn-entry
    # preamble, at_pre ensures rewrite).
    *)         printf '%s' '' ;;
  esac
}
is_honest_fail() { [ -n "$(honest_fail_reason "$1")" ]; }

echo "== W2b bridge runner =="
echo "cert dir : $CERT_DIR"
echo "core out : $CORE_OUT"
echo "prelude  : $PRELUDE"
echo "lean     : $LEAN_BIN"
echo

printf "%-14s %-11s %8s %8s   %s\n" "fn" "verdict" "decide" "rfl" "class"
printf "%-14s %-11s %8s %8s   %s\n" "--" "-------" "------" "---" "-----"

fail=0
for cert in "$CERT_DIR"/*.cert.lean; do
  [ -e "$cert" ] || { echo "no certs found in $CERT_DIR"; exit 2; }
  fn="$(basename "$cert" .cert.lean)"
  klass="CLOSE"; is_honest_fail "$fn" && klass="HONEST-FAIL"

  base="$WORK/Bridge_$fn"
  # decide bridge
  cat "$cert" > "$base.decide.lean"
  cat >> "$base.decide.lean" <<EOF

-- ── W2b bridge (bootstrap-07) ──
set_option maxRecDepth 8000
example : lib.goals_eq (lib.ref_wp cert_${fn}_ctx cert_${fn}_sst) cert_${fn}_goals = 1 := by decide
EOF
  # rfl bridge (task asks to confirm rfl also closes)
  cat "$cert" > "$base.rfl.lean"
  cat >> "$base.rfl.lean" <<EOF

set_option maxRecDepth 8000
example : lib.goals_eq (lib.ref_wp cert_${fn}_ctx cert_${fn}_sst) cert_${fn}_goals = 1 := by rfl
EOF

  t0=$(date +%s%N); "$LEAN_BIN" "$base.decide.lean" >"$base.decide.log" 2>&1; drc=$?; t1=$(date +%s%N)
  dms=$(( (t1 - t0) / 1000000 ))
  t0=$(date +%s%N); "$LEAN_BIN" "$base.rfl.lean"    >"$base.rfl.log"    2>&1; rrc=$?; t1=$(date +%s%N)
  rms=$(( (t1 - t0) / 1000000 ))

  # closes iff rc==0 (the `= 1` example elaborated). honest-fail: rc!=0 expected.
  if [ "$klass" = "CLOSE" ]; then
    if [ $drc -eq 0 ] && [ $rrc -eq 0 ]; then verdict="close-ok"; else verdict="CLOSE-BROKE"; fail=1; fi
  else
    # honest-fail: the = 1 bridge must NOT elaborate (goals_eq is 0)
    if [ $drc -ne 0 ]; then verdict="hfail-ok"; else verdict="LAX-REGRESS"; fail=1; fi
  fi
  printf "%-14s %-11s %6dms %6dms   %s\n" "$fn" "$verdict" "$dms" "$rms" "$klass"
  [ "$klass" = "HONEST-FAIL" ] && echo "  ↳ reason: $(honest_fail_reason "$fn")"
  # keep logs of any anomaly for inspection
  case "$verdict" in CLOSE-BROKE|LAX-REGRESS) echo "  ↳ decide.log:"; sed 's/^/    /' "$base.decide.log" | head -20;; esac
done

echo

# ── Subject-population pin (b81 review R3, 2026-08-06; modelled on
# probe11's b78 S5 pin) ─────────────────────────────────────────────
# A cert that VANISHES between emits is silent coverage loss (the loop
# above only iterates what is on disk). Every previously-seen subject
# is either present above or listed in expected_absent_reason with its
# census tag. A documented-absent subject that REAPPEARS must be
# reclassified loud (its tag was retired or its arm landed).
expected_absent_reason() {
  case "$1" in
    mix_trip2) printf '%s' "hoist-mixed-shadow" ;;
    *) printf '%s' '' ;;
  esac
}
# Every fn ever seen as a bridge subject or documented absentee.
expected_subjects="add_capped assert_by_default call_g2_ob call_g3_ob call_inc call_swap_incr clamped_inc count_down count_to_len double_exec fill_zeros find_square forall_int_skolem forall_leading_prefix forall_nested_shadow forall_u64_skolem head_exec head_via_let id_generic inc max_u64 mk_point mul_bound pick_max proof_block_fn quad_exec scope_shape sum_to swap_incr swap_pair tri_one use_clamped use_multiarg vec_push7 vec_read mix_trip2"

for fn in $expected_subjects; do
  if [ -f "$CERT_DIR/$fn.cert.lean" ]; then
    reason="$(expected_absent_reason "$fn")"
    if [ -n "$reason" ]; then
      echo "SUBJECT-RETURNED: $fn has a cert again — retire its expected_absent_reason entry and classify the bridge verdict."; fail=1
    fi
  else
    reason="$(expected_absent_reason "$fn")"
    if [ -n "$reason" ]; then
      echo "absent-ok  $fn  ($reason)"
    else
      echo "SUBJECT-VANISHED: $fn — no cert and no documented absence (silent coverage loss)"; fail=1
    fi
  fi
done

echo
if [ $fail -eq 0 ]; then echo "ALL BRIDGES BEHAVE AS CLASSIFIED ✓"; else echo "SOME BRIDGES DIVERGED FROM CLASSIFICATION ✗"; fi
exit $fail
