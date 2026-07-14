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
PRELUDE="${TACTUS_PRELUDE:-$HOME/.cache/tactus/prelude-e81fbf9a86375c12}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

export LEAN_PATH="$CORE_OUT:$PRELUDE"

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
honest_fail_reason() {
  case "$1" in
    max_u64)   printf '%s' 'branch-in-leaf: frontend lifts the fall-through if INTO the ensures leaf [x<y -> let r:=...]; refWp folds the raw per-ensures leaves. DESIGN 2.4.1.' ;;
    count_down) printf '%s' 'two-way If-join not merged at stage A (DESIGN 2.4.1): `if n==0 {0} else {recurse}` — BOTH branches fall through to a common Ret. frame_after(If) returns the pre-If frame (the merge special case needs diverges(then) && is_skip(else)), so the common Ret closes under the bare pre-If frame (missing each branch tmp__3 binding) -> 1 malformed postcond where production clones 2. refWp=3 goals, prod=4; the assert+termination goals AROUND the recursive call match production exactly (Call arm is faithful — quad_exec closes). Surfaced (not caused) by bootstrap-02b making count_down emittable. Follow-up: bootstrap-19 (model the two-way If-join).' ;;
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
if [ $fail -eq 0 ]; then echo "ALL BRIDGES BEHAVE AS CLASSIFIED ✓"; else echo "SOME BRIDGES DIVERGED FROM CLASSIFICATION ✗"; fi
exit $fail
