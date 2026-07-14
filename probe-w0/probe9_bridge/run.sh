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
honest_fail_reason() {
  case "$1" in
    max_u64)   printf '%s' 'branch-in-leaf: frontend lifts the fall-through if INTO the ensures leaf [x<y -> let r:=...]; refWp folds the raw per-ensures leaves. DESIGN 2.4.1.' ;;
    head_exec) printf '%s' 'ref-param deref: ensures r==tree_head(*t) renders *t as bare t via the serializer empty-RenderCtx oblig_leaf [leaf 3], but production postcondition renders t.deref [leaf 6]. Sole divergence = the oblig leaf. DESIGN 2.5 leaf-rendering not certified; sibling of finding-4 coercion caveat.' ;;
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
