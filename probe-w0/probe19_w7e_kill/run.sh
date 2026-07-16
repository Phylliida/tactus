#!/usr/bin/env bash
# W7e defs-layer CONTENT-perturbation mutation-kill (board bootstrap-35).
#
# probe17 (W7d) proved the live `def_eq`/`dt_eq` bridges CLOSE, and its `kill`
# column flips the bridge LITERAL `= 1 := by decide` → `= 0` (proving the bridge
# is non-vacuous — not `decide`-of-`True`). That is the VACUITY FLOOR.
#
# THIS probe is the deeper kill: it perturbs the emitted `*_defdata`/`*_dtdata`
# TERM ITSELF (a body literal / opcode / match-arm body / datatype field type),
# leaves `render_def raw` UNTOUCHED, and keeps the bridge at `= 1 := by decide`.
# Because the two transcriber sides use disjoint constructor namespaces
# (reference `RawExp.`/`RawDt.` vs production `ExprData.`/`DtData.`) AND the
# perturbation is scoped to the production `_defdata`/`_dtdata` def block only,
# `render_def raw` still expects the ORIGINAL content while the production side
# now differs ⟹ `def_eq` must return 0 ⟹ the unchanged `= 1` bridge must now
# FAIL to elaborate. That proves `def_eq`/`dt_eq` actually compare body content,
# not just top-level shape.
#
# Each cert is perturbed at a DIFFERENT structural position so the kill set
# exercises distinct `def_eq`/`dt_eq` recursion arms:
#   tri       : deep body literal          (the `n-1` subtraction const, Lit 1→2)
#   sq        : body opcode                (mul BinOp 8 → add BinOp 6)
#   tree_head : match-arm body literal     (the Node arm's Lit 0 → 9)
#   Tree (dt) : datatype field type        (Node's Box field TyBox 0 → TyInt)
#
#  positive : the UNPERTURBED cert must still elaborate rc=0 (bridge closes).
#  kill     : the content-perturbed copy must elaborate rc!=0 (bridge detects it).
#
# Depends on the live certs emitted by probe17's regen recipe (see
# probe17_w7d_live/run.sh). Usage: probe-w0/probe19_w7e_kill/run.sh
#   (LEAN=<lean> / TACTUS_PRELUDE=<dir>)
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CERT_DIR="$ROOT/bootstrap-fixture/out/lib/cert"
CORE_OUT="$ROOT/tactus-core/out/lib"
PRELUDE="${TACTUS_PRELUDE:-$HOME/.cache/tactus/prelude-e81fbf9a86375c12}"
LEAN_BIN="${LEAN:-$(command -v lean)}"
WORK="$(mktemp -d)"; trap 'rm -rf "$WORK"' EXIT

export LEAN_PATH="$CORE_OUT:$PRELUDE"

echo "== W7e defs-layer CONTENT-perturbation mutation-kill =="
echo "cert dir : $CERT_DIR"
echo "core out : $CORE_OUT"
echo "prelude  : $PRELUDE"
echo "lean     : $LEAN_BIN"
echo

# Ordered perturbation list :: "file:::pattern:::replacement:::position-label".
# pattern/replacement are applied (as awk regex) ONLY inside the file's
# `def cert_..._{def,dt}data := ...` block (up to the next blank line), so the
# reference `cert_..._raw` def (a separate block) is never touched. Together
# these cover the position classes the card requires: body / opcode / arm /
# ctor / field. A file may appear more than once (independent kills).
PERTURB=(
  "tri.defcert.lean:::ExprData[.]Lit 1:::ExprData.Lit 2:::body: deep literal (n-1 const)"
  "sq.defcert.lean:::ExprData[.]BinOp 8:::ExprData.BinOp 6:::opcode: mul->add"
  "tree_head.defcert.lean:::ExprData[.]Lit 0:::ExprData.Lit 9:::arm: match-arm body literal"
  "tree_head.defcert.lean:::ArmList[.]Cons 6:::ArmList.Cons 9:::ctor: match-arm ctor id"
  "lib__Tree.dtcert.lean:::CtorList[.]Cons 2:::CtorList.Cons 9:::ctor: datatype ctor id"
  "lib__Tree.dtcert.lean:::TypData[.]TyBox 0:::TypData.TyInt:::field: datatype field type (Box->Int)"
)

printf "%-24s %-9s %-9s  %s\n" "cert" "positive" "kill" "perturbation"
printf "%-24s %-9s %-9s  %s\n" "----" "--------" "----" "------------"

fail=0
# de-dup the positive elaboration (a file may appear more than once).
declare -A POS_DONE=()
for spec in "${PERTURB[@]}"; do
  base="${spec%%:::*}";        rest="${spec#*:::}"
  pat="${rest%%:::*}";         rest="${rest#*:::}"
  rep="${rest%%:::*}";         label="${rest#*:::}"
  cert="$CERT_DIR/$base"

  if [ ! -f "$cert" ]; then
    printf "%-24s %-9s %-9s  %s\n" "$base" "MISSING" "-" "(run probe17 regen recipe first)"
    fail=1; continue
  fi

  # positive: the unperturbed live cert must still close (once per file).
  pos="—"
  if [ -z "${POS_DONE[$base]:-}" ]; then
    "$LEAN_BIN" "$cert" >"$WORK/pos.log" 2>&1; prc=$?
    pos="OK"; [ "$prc" -eq 0 ] || { pos="FAIL"; fail=1; }
    POS_DONE[$base]=1
  fi

  # kill: perturb ONLY the production `_{def,dt}data` block; the `= 1` bridge is
  # left as-is and must now fail (def_eq/dt_eq detects the content change).
  mut="$WORK/mut.lean"
  awk -v pat="$pat" -v rep="$rep" '
    /def cert_.*_(def|dt)data/ { inblock=1 }
    inblock && /^[[:space:]]*$/ { inblock=0 }
    inblock { gsub(pat, rep) }
    { print }
  ' "$cert" > "$mut"

  # guard: the perturbation must have actually changed the file (else a silent
  # no-op would masquerade as a passing kill).
  if cmp -s "$cert" "$mut"; then
    printf "%-24s %-9s %-9s  %s\n" "$base" "$pos" "NO-OP" "$label (pattern did not match!)"
    fail=1; continue
  fi

  "$LEAN_BIN" "$mut" >"$WORK/kill.log" 2>&1; krc=$?
  kill="OK"; [ "$krc" -ne 0 ] || { kill="VACUOUS"; fail=1; }

  printf "%-24s %-9s %-9s  %s\n" "$base" "$pos" "$kill" "$label"
  if [ "$pos" = "FAIL" ]; then echo "  --- positive output ($base) ---"; sed 's/^/  /' "$WORK/pos.log" | head -20; fi
  if [ "$kill" = "VACUOUS" ]; then echo "  --- kill accepted?! ($base / $label) — perturbed data still closed = 1 ---"; fi
done

echo
if [ "$fail" -eq 0 ]; then
  echo "W7E CONTENT-KILL OK ✓ (every live def/dt cert closes unperturbed; each content perturbation is detected — def_eq/dt_eq compare body content, not just shape)"
else
  echo "W7E CONTENT-KILL FAILED ✗"
fi
exit "$fail"
