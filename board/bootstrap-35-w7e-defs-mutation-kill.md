---
title: "W7e — defs-layer mutation-kill: perturb body / ctor / height ⟹ def_eq/dt_eq bridge flips 1→0"
status: todo
claimed_by:
created: 2026-07-15T04:10:00Z
updated: 2026-07-15T04:10:00Z
---

## Description

The final W7 rung (design `DESIGN-W7-defslayer.md` §6, mirrors W6e). W7d proved
the live `def_eq`/`dt_eq` bridges CLOSE (`= 1 := by decide`) on the emitted
`.defcert`/`.dtcert` files. This card proves they are **content-sensitive**: a
perturbation of the *body* / *constructor* / *field type* / *height* must flip
the bridge `1 → 0`.

**What probe17 already covers (the vacuity floor):** its `kill` column flips the
bridge LITERAL `= 1 := by decide` → `= 0 := by decide` and confirms `decide`
now rejects — i.e. the pair is genuinely `= 1`, not `decide`-of-`True`. That
proves the bridge is non-vacuous, but NOT that `def_eq` inspects body content.

**What W7e must add (the real mutation-kill):** perturb the emitted `*_defdata`
/ `*_dtdata` term itself (leave `render_def raw` alone) and confirm
`def_eq (render_def raw) (perturbed data) = 0`:
- **body literal:** `tri`'s base-case `Lit 0` → `Lit 1` ⟹ 0.
- **body opcode:** `sq`'s `BinOp 8` (mul) → `BinOp 7` (sub) ⟹ 0.
- **match arm:** `tree_head`'s `Node _ _ => 0` body `Lit 0` → `Lit 1`, or swap
  the two arms' ctor ids ⟹ 0.
- **ctor / field:** `Tree`'s `Node` field `TyBox 0` → `TyInt`, or drop a ctor,
  or rename a ctor id ⟹ 0.
- **height** (if a height measure is emitted as its own def): perturb it ⟹ 0.

Each perturbation must land on a DIFFERENT structural position so the kill set
demonstrably exercises each `def_eq`/`dt_eq` recursion arm (not just the top
literal).

**Done when:** a `probe-w0/probe19_w7e_kill/run.sh` (or an extension of
`probe17`'s kill column) applies each perturbation above to the LIVE emitted
certs and confirms every one flips the bridge to `0` (`decide` rejects),
covering body/opcode/arm/ctor/field positions. Honest note if any position is
not reachable from the current fixture (e.g. height) — add a fixture caller or
mark it a tgt-slice follow-up.

**Blocked by:** `bootstrap-33` (W7d live wire) — DONE. **Blocks:** nothing;
this is the W7 acceptance rung.

## Progress
- (2026-07-15, opus-w7d-settle) Created when W7d closed. The vacuity floor
  (bridge-literal flip) is already green in `probe17`; W7e is the deeper
  content-perturbation kill that proves `def_eq`/`dt_eq` actually compare body
  structure, not just top-level shape.

## Writeup
_todo_
