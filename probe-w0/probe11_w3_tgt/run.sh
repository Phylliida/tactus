#!/usr/bin/env bash
# W3 differential gate over tgt (bootstrap-08).
#
# Runs the refWp↔production bridge over the certs the serializer emits for
# tactus-group-theory (tgt) EXEC fns, and classifies every verdict. This is the
# first time the bridge runs on certs produced from REAL corpus code (a group-
# theory crate) rather than the hand-authored bootstrap-fixture family — i.e.
# the differential gate's actual bug-finding payoff.
#
# ── Corpus fact (N4 census, DESIGN-W2-refwp.md §1.1) ──────────────────────────
# Stage-A cert emission is EXEC-FN-ONLY. tgt is proof/spec-heavy: 9 exec fns
# crate-wide. Of those, exactly 1 emits a stage-A cert today
# (runtime::impl__4::clone, a derived Copy-clone with a trivial WP); the other 8
# are LOUD serializer scope-rejections (5×StmData::Call = bootstrap-02b;
# 3×assert-query), which emit NO cert and so are NOT bridge subjects. So the
# differential gate has exactly ONE bridgeable subject today. When the Call and
# assert-query serializer arms land, more tgt exec fns emit certs and this gate
# re-runs with them.
#
# ── Regen the tgt cert (cold, cert on, targeted; ~80s) ───────────────────────
#   OUT=probe-w0/probe11_w3_tgt/out
#   source/target-verus/release/verus --lean-backend --crate-type=lib \
#     /home/bepis/prog/verus-cad/tactus-group-theory/src/lib.rs \
#     --emit-lean --tactus-emit-cert --verify-module runtime \
#     TACTUS_LEAN_OUT=$OUT      # (env; see command form in the board card)
# Must run COLD (omit -V cache): a cache-hit fn skips the emit path (census
# prereq B). The cert lands at $OUT/lib/cert/runtime__impl__4__clone.cert.lean.
#
# Classification (same discipline as probe9_bridge):
#   CLOSE       — refWp reconstructs production verbatim; = 1 bridge elaborates.
#   HONEST-FAIL — a DOCUMENTED stage-A caveat (leaf rendering not certified,
#                 §2.5). The = 1 bridge SOUNDLY does NOT elaborate. A honest-fail
#                 that suddenly CLOSES is a regression (refWp went lax or the
#                 serializer caveat was silently "fixed") and FAILS the run too.
#
# Usage: probe-w0/probe11_w3_tgt/run.sh      (auto-locates everything)
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CERT_DIR="$ROOT/probe-w0/probe11_w3_tgt/out/lib/cert"
CORE_OUT="$ROOT/tactus-core/out/lib"
# All prelude caches (slim-prelude work mints new hashes; the collapsed
# bare TactusDefs ships inside the prelude — glob them all, probe37-style).
PRELUDES="$(ls -d "$HOME"/.cache/tactus/prelude-* 2>/dev/null | tr '\n' ':')"
PRELUDE="${PRELUDES%:}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

export LEAN_PATH="$CORE_OUT:$CORE_OUT/pkg:$PRELUDE"

# DOCUMENTED honest-fails: a serializer leaf-rendering divergence the bridge
# SOUNDLY does not close. Each has a recorded, pinpoint-proved reason.
#
# NOTE (bootstrap-18, 2026-07-13): runtime__impl__4__clone was FIXED and is now
# expected-CLOSE. Its RetBind value (the return-var `let _return := *self`) is a
# bare `Var(self) : &RuntimeSymbol` whose `.deref` comes from production's
# per-leaf return-typ coercion (lift_if_value_coerced base case → coerce_leaf),
# NOT from binder_typs (a bare Var carries no explicit *self to deref). The
# serializer now applies that SAME coercion — coerce_lexpr(render(e), &e.typ,
# ret_typ) — in the Return arm, so the RetBind value renders `self.deref`
# (leaf 5) and the SST RetLet 4 5 matches the goal's Let 4 5. Removed from the
# honest-fail set; it must now close-ok.
honest_fail_reason() {
  case "$1" in
    runtime__apply_hom_gen|runtime__apply_hom_inv) printf '%s' 'call-arg temp lets + auto-ref arg coercion unmodeled (bootstrap-74 slice 2 sweep, 2026-07-21): Verus lowers `&h.generator_images[i]` to a `tmp__N := h.deref.generator_images` arg temp whose Wp::LetRaw frame is TYP-LESS (production bails hoist_all to whole-goal wrap); the serializer typed it from local_typs and hoisted (AssignH). And the instantiated callee requires keeps the auto-ref coercion (`Tactus.Ref.mk <arg>`) which the serializer drops. New Call-arm machinery — carded follow-up.' ;;
    runtime__lemma_runtime_word_view_append|runtime__lemma_runtime_word_view_subrange) printf '%s' 'assert-forall quantifier binders unmodeled (bootstrap-74 slice 2 sweep, 2026-07-21): the fn asserts `forall |k: int| …` — production emits the skolem binder `∀ (k : Int)` in the goal telescope; stage A has no quantifier-binder arm, so the serializer instead emits the lowering bool temp as a residue let + a poisoned Assume and wraps. SHOULD be a loud census rejection (assert-forall tag), not a non-bridging cert — census-gap follow-up.' ;;
    *) printf '%s' '' ;;
  esac
}
is_honest_fail() { [ -n "$(honest_fail_reason "$1")" ]; }

echo "== W3 differential gate over tgt =="
echo "cert dir : $CERT_DIR"
echo "core out : $CORE_OUT"
echo "prelude  : $PRELUDE"
echo "lean     : $LEAN_BIN"
echo

if ! ls "$CERT_DIR"/*.cert.lean >/dev/null 2>&1; then
  echo "no tgt certs on disk in $CERT_DIR"
  echo "regen them with the cold emit command in this script's header."
  exit 2
fi

printf "%-28s %-11s %8s %8s   %s\n" "fn" "verdict" "decide" "rfl" "class"
printf "%-28s %-11s %8s %8s   %s\n" "--" "-------" "------" "---" "-----"

fail=0
for cert in "$CERT_DIR"/*.cert.lean; do
  fn="$(basename "$cert" .cert.lean)"
  klass="CLOSE"; is_honest_fail "$fn" && klass="HONEST-FAIL"

  base="$WORK/Bridge_$fn"
  cat "$cert" > "$base.decide.lean"
  cat >> "$base.decide.lean" <<EOF

-- ── W3 bridge (bootstrap-08) ──
set_option maxRecDepth 8000
example : lib.goals_eq (lib.ref_wp cert_${fn}_ctx cert_${fn}_sst) cert_${fn}_goals = 1 := by decide
EOF
  cat "$cert" > "$base.rfl.lean"
  cat >> "$base.rfl.lean" <<EOF

set_option maxRecDepth 8000
example : lib.goals_eq (lib.ref_wp cert_${fn}_ctx cert_${fn}_sst) cert_${fn}_goals = 1 := by rfl
EOF

  t0=$(date +%s%N); "$LEAN_BIN" "$base.decide.lean" >"$base.decide.log" 2>&1; drc=$?; t1=$(date +%s%N)
  dms=$(( (t1 - t0) / 1000000 ))
  t0=$(date +%s%N); "$LEAN_BIN" "$base.rfl.lean"    >"$base.rfl.log"    2>&1; rrc=$?; t1=$(date +%s%N)
  rms=$(( (t1 - t0) / 1000000 ))

  if [ "$klass" = "CLOSE" ]; then
    if [ $drc -eq 0 ] && [ $rrc -eq 0 ]; then verdict="close-ok"; else verdict="CLOSE-BROKE"; fail=1; fi
  else
    # honest-fail: the = 1 bridge must NOT elaborate (goals_eq is 0)
    if [ $drc -ne 0 ]; then verdict="hfail-ok"; else verdict="LAX-REGRESS"; fail=1; fi
  fi
  printf "%-28s %-11s %6dms %6dms   %s\n" "$fn" "$verdict" "$dms" "$rms" "$klass"
  [ "$klass" = "HONEST-FAIL" ] && echo "  ↳ reason: $(honest_fail_reason "$fn")"
  case "$verdict" in CLOSE-BROKE|LAX-REGRESS) echo "  ↳ decide.log:"; sed 's/^/    /' "$base.decide.log" | head -20;; esac
done

echo
if [ $fail -eq 0 ]; then echo "ALL TGT BRIDGES BEHAVE AS CLASSIFIED ✓"; else echo "SOME TGT BRIDGES DIVERGED FROM CLASSIFICATION ✗"; fi
exit $fail
