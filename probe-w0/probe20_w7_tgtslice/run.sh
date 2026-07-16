#!/usr/bin/env bash
# W7 tgt-slice defs-layer bridge runner (board bootstrap-37).
#
# The probe17 runner, pointed at the tgt-slice cert dir (emit.sh output) instead
# of the bootstrap-fixture. Elaborates each emitted `.defcert`/`.dtcert` against
# `tactus-core/out/lib` + prelude:
#   positive : every emitted def/dt cert must elaborate rc=0 (bridge closes).
#   kill     : flip its `= 1 := by decide` to `= 0` — `decide` MUST now reject.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CERT_DIR="$ROOT/probe-w0/probe20_w7_tgtslice/out/lib/cert"
CORE_OUT="$ROOT/tactus-core/out/lib"
PRELUDE="${TACTUS_PRELUDE:-$HOME/.cache/tactus/prelude-e81fbf9a86375c12}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT

export LEAN_PATH="$CORE_OUT:$PRELUDE"

echo "== W7 tgt-slice defs-layer bridge runner =="
echo "cert dir : $CERT_DIR"
echo "core out : $CORE_OUT"
echo "lean     : $LEAN_BIN"
echo

shopt -s nullglob
files=( "$CERT_DIR"/*.defcert.lean "$CERT_DIR"/*.dtcert.lean )
if [ "${#files[@]}" -eq 0 ]; then
  echo "no tgt def/dt certs found in $CERT_DIR — did emit.sh run with --tactus-emit-cert?"
  exit 2
fi

printf "%-40s %-9s %-9s   %s\n" "cert" "positive" "kill" "wall"
printf "%-40s %-9s %-9s   %s\n" "----" "--------" "----" "----"

fail=0
for cert in "${files[@]}"; do
  base="$(basename "$cert")"
  t0=$(date +%s%N); "$LEAN_BIN" "$cert" >"$WORK/pos.log" 2>&1; prc=$?; t1=$(date +%s%N)
  pos="OK"; [ "$prc" -eq 0 ] || { pos="FAIL"; fail=1; }

  mut="$WORK/mut.lean"
  sed 's/= 1 := by decide/= 0 := by decide/' "$cert" > "$mut"
  "$LEAN_BIN" "$mut" >"$WORK/kill.log" 2>&1; krc=$?
  kill="OK"; [ "$krc" -ne 0 ] || { kill="VACUOUS"; fail=1; }

  printf "%-40s %-9s %-9s   %sms\n" "$base" "$pos" "$kill" "$(( (t1 - t0) / 1000000 ))"
  if [ "$pos" = "FAIL" ]; then echo "  --- positive elaboration output ($base) ---"; sed 's/^/  /' "$WORK/pos.log" | head -40; fi
done

echo
if [ "$fail" -eq 0 ]; then
  echo "W7 TGT-SLICE DEF-BRIDGE OK ✓ (every emitted def/dt cert closes by decide; kills non-vacuous)"
else
  echo "W7 TGT-SLICE DEF-BRIDGE had FAILURES ✗ (see above — triage: honest scope-gap vs real divergence)"
fi
exit "$fail"
