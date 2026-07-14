---
title: "W7e — defs-layer mutation-kill: perturb body / ctor / height ⟹ def_eq/dt_eq bridge flips 1→0"
status: done
claimed_by: opus-w7e
created: 2026-07-15T04:10:00Z
updated: 2026-07-15T04:40:00Z
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
- (2026-07-15, opus-w7e) **DONE — `probe-w0/probe19_w7e_kill/run.sh` built and
  green (6 kills / 5 position classes).** Key mechanic (the thing that makes
  this a REAL content kill, not another bridge-literal flip): the two
  transcriber sides use disjoint constructor namespaces (reference
  `RawExp.`/`RawDt.` vs production `ExprData.`/`DtData.`), and each live cert has
  the reference `cert_*_raw` and production `cert_*_{def,dt}data` in SEPARATE
  `def` blocks. So an `awk` region-scoped `gsub` (from `def cert_*_{def,dt}data`
  to the next blank line) perturbs ONLY the production side; `render_def raw`
  still expects the original content, so `def_eq`/`dt_eq` genuinely returns 0 and
  the UNCHANGED `= 1 := by decide` bridge now fails to elaborate. Verified by a
  manual `tri` spot-check (diff touched only line 18; `decide proved ... = 1 is
  false`) before writing the probe. A `cmp -s` no-op guard rejects any
  perturbation whose pattern didn't match (so a silent miss can't masquerade as
  a kill). Positives de-duped (elaborated once per file).
  - **Coverage (each a distinct `def_eq`/`dt_eq` recursion arm):**
    body literal (`tri` `n-1` const `Lit 1→2`), opcode (`sq` `BinOp 8→6`,
    mul→add), match-arm body literal (`tree_head` Node-arm `Lit 0→9`), match-arm
    ctor id (`tree_head` `ArmList.Cons 6→9`), datatype ctor id (`Tree`
    `CtorList.Cons 2→9`), datatype field type (`Tree` `TyBox 0→TyInt`). All six
    kill; all four positives close.
  - **Height — resolved (no separate cert to perturb).** Checked: the live
    fixture emits NO `Tree.height` defcert. The datatype's Lean `.height` is
    auto-derived by tactus-core `render_dt`/`deriving` from the `Tree` decl, not
    a transcribed production `DefData`, so there is nothing standalone to bridge
    or perturb. The ctors + field types that DETERMINE the derived height ARE
    certified via the dtcert, and this probe perturbs both (ctor-id + field-type
    kills) — so height-determining content is covered. (The only `.height` in
    the emitted defs is vstd's poly `set.Set.height`, correctly `rawvir-def-poly`
    gated, no cert.)

## Writeup
**DONE.** `probe-w0/probe19_w7e_kill/run.sh` is the defs-layer content-kill: it
perturbs each live emitted `.defcert`/`.dtcert` at a distinct structural
position (body literal, opcode, match-arm body, match-arm ctor id, datatype ctor
id, datatype field type — 6 kills / 5 classes), scoped to the production
`_{def,dt}data` block only, and confirms every one flips the `def_eq`/`dt_eq`
bridge from 1→0 (unchanged `= 1 := by decide` now fails), while every unperturbed
cert still closes. This is strictly deeper than `probe17`'s vacuity floor (which
only flips the bridge LITERAL): it proves the bridge inspects body *content*, at
every recursion arm the fixture reaches.

### How it works
The reference and production transcriptions live in separate `def` blocks and use
disjoint constructor namespaces, so an `awk` region-scoped `gsub` over the
production data block leaves `render_def raw` intact — the two sides genuinely
disagree after the edit, forcing `def_eq = 0`. A `cmp -s` no-op guard fails the
run if any pattern silently didn't match (prevents a false "kill OK").

### Assumptions / honest scope
- Runs against the certs from probe17's regen recipe (fork verus
  `--tactus-emit-cert` over `bootstrap-fixture`); it does not re-emit them.
- No separate `Tree.height` cert exists to perturb (auto-derived, not
  transcribed); height-determining content is covered via the datatype ctor/field
  kills (see Progress).
- Like all W7 probes, this certifies the transcribers AGREE under perturbation;
  it does not certify the transcribers themselves (TCB) or SST-semantics
  adequacy — that's W5 (`bootstrap-10`).
