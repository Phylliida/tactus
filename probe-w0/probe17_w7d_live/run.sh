#!/usr/bin/env bash
# W7d LIVE defs-layer bridge runner (board bootstrap-33).
#
# The live-path analog of probe16: probe16 elaborates HAND-PINNED literals;
# THIS runner elaborates the `.defcert.lean` / `.dtcert.lean` files freshly
# EMITTED by a real `verus --lean-backend --tactus-emit-cert` run over the
# bootstrap fixture (`bootstrap-fixture/out/lib/cert/`). Each emitted file is
# self-contained (`import TactusDefs_lib_exec` + `cert_<leaf>_raw`/`_defdata`
# + `example : lib.def_eq (lib.render_def raw) defdata = 1 := by decide`), so
# elaborating it with the tactus-core oleans on LEAN_PATH IS the bridge.
#
#  positive : every emitted def/dt cert must elaborate rc=0 (bridge closes).
#  kill     : perturb one emitted `= 1` bridge to `= 0` (per file) and confirm
#             `decide` now REJECTS — the bridge is non-vacuous on the live path.
#
# Regen recipe (fresh emit): from the tactus-bootstrap dir, fork vargo on PATH,
#   TACTUS_LEAN_OUT=$PWD/bootstrap-fixture/out \
#     source/target-verus/release/verus --crate-type=lib \
#     --lean-backend --emit-lean --lean-all-proofs --tactus-emit-cert \
#     bootstrap-fixture/lib.rs
#
# Usage: probe-w0/probe17_w7d_live/run.sh   (LEAN=<lean> / TACTUS_PRELUDE=<dir>)
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CERT_DIR="$ROOT/bootstrap-fixture/out/lib/cert"
CORE_OUT="$ROOT/tactus-core/out/lib"
PRELUDE="${TACTUS_PRELUDE:-$HOME/.cache/tactus/prelude-e81fbf9a86375c12}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT

export LEAN_PATH="$CORE_OUT:$PRELUDE"

echo "== W7d LIVE defs-layer bridge runner =="
echo "cert dir : $CERT_DIR"
echo "core out : $CORE_OUT"
echo "prelude  : $PRELUDE"
echo "lean     : $LEAN_BIN"
echo

shopt -s nullglob
files=( "$CERT_DIR"/*.defcert.lean "$CERT_DIR"/*.dtcert.lean )
if [ "${#files[@]}" -eq 0 ]; then
  echo "no live def/dt certs found in $CERT_DIR — did the emit run with --tactus-emit-cert?"
  exit 2
fi

printf "%-28s %-9s %-9s   %s\n" "cert" "positive" "kill" "wall"
printf "%-28s %-9s %-9s   %s\n" "----" "--------" "----" "----"

fail=0
for cert in "${files[@]}"; do
  base="$(basename "$cert")"

  # positive: the live file must elaborate as-emitted.
  t0=$(date +%s%N); "$LEAN_BIN" "$cert" >"$WORK/pos.log" 2>&1; prc=$?; t1=$(date +%s%N)
  pos="OK"; [ "$prc" -eq 0 ] || { pos="FAIL"; fail=1; }

  # kill: flip the bridge's `= 1 := by decide` to `= 0 := by decide` in a copy;
  # `decide` MUST now reject (the correct pair is not `= 0`). If it accepts, the
  # bridge is vacuous. (This is the emitted-literal perturbation on the live path.)
  mut="$WORK/mut.lean"
  sed 's/= 1 := by decide/= 0 := by decide/' "$cert" > "$mut"
  "$LEAN_BIN" "$mut" >"$WORK/kill.log" 2>&1; krc=$?
  kill="OK"; [ "$krc" -ne 0 ] || { kill="VACUOUS"; fail=1; }

  printf "%-28s %-9s %-9s   %sms\n" "$base" "$pos" "$kill" "$(( (t1 - t0) / 1000000 ))"
  if [ "$pos" = "FAIL" ]; then echo "  --- positive elaboration output ($base) ---"; sed 's/^/  /' "$WORK/pos.log" | head -30; fi
done

echo
if [ "$fail" -eq 0 ]; then
  echo "W7D LIVE DEF-BRIDGE OK ✓ (every emitted def/dt cert closes by decide; kills non-vacuous)"
else
  echo "W7D LIVE DEF-BRIDGE FAILED ✗"
fi
exit "$fail"
