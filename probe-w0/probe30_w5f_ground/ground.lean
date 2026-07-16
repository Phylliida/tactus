import TactusDefs_lib_exec              -- tactus-core: lib.render_exp / lib.RawExp / lib.ExprData …
import w5f_v2_match_sem                 -- probe29 (W5f): SymEnv, eval/edenote, FACT 5/8 (abstract)
import TactusDefs_fixlib_exec__root     -- fixture (RENAMED, obstacle D): fixlib.sq / fixlib.g2

set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 8000

-- ══════════════════════════════════════════════════════════════════════
-- W5f v2 GROUNDING — RUNG 1 (board bootstrap-57): ground the CALL-fragment leaf
-- oracles `fn`/`fnN` to REAL emitted defs, discharging FACT 5/8's free hypotheses.
--
-- probe29's adequacy facts `adequacy_leaf_app_grounded` (FACT 5) and
-- `adequacy_leaf_appn_grounded` (FACT 8) are stated over an ABSTRACT `E : SymEnv`
-- with a FREE hypothesis `hfn : E.fn fId = g` (resp. `hfnN : E.fnN fId = h`). The
-- honest content there is the render→denote arm-selection + call-shape; the oracle
-- `E.fn` itself is unconstrained — you could plug in ANY interpretation.
--
-- THIS PROBE pins it. `crateEnv : W5f.SymEnv` is a concrete P5 match-literal whose
-- `fn`/`fnN` fields are the RENAMED emitter output `fixlib.sq`/`fixlib.g2` (lifted
-- across the Nat/Int seam). The specialized facts (`ground_app_sq`/`ground_appn_g2`)
-- discharge `hfn`/`hfnN` by `rfl` — the leaf denotation is now TIED to real emitted
-- spec-fn defs, not a free assumption. That closes the "free hypothesis" gap for the
-- CALL fragment (the bootstrap-56 census: fn-pinned bodies ⇒ this is where user
-- spec-fn calls actually land).
-- ══════════════════════════════════════════════════════════════════════

namespace W5fGround
open W5f

-- ── the Nat/Int seam (recon Rung 1 note). The emitted fixlib fns are `Nat → Nat`;
--    the goal language / FACT 5's `g` is `Int → Int`. Lift each emitted fn across
--    the seam: an Int argument is decoded via `Int.toNat`, the Nat result re-coerced
--    to Int. This is exactly the render path's `needs_nat_coercion`/`coerce_if`
--    decision, made EXPLICIT here at the pin (FACT 5's `Call fId TyInt … TyInt`
--    shape carries no cast node, so the coercion lives in the pin, not the denote).
noncomputable def sqLift : Int → Int :=
  fun x => ((fixlib.sq x.toNat : Nat) : Int)
noncomputable def g2Lift : List Int → Int :=
  fun xs => match xs with
    | a :: b :: _ => ((fixlib.g2 a.toNat b.toNat : Nat) : Int)
    | _           => 0

-- ── interned symbol ids. In a real crate these are the serializer's string-table
--    indices; the grounding needs only that `crateEnv.fn sqId` REDUCES to `sqLift`,
--    so any concrete constant works (`ltId = 2` matches the emitter's Lt opcode, as
--    used by FACT 2 `adequacy_leaf_overflow`).
def ltId : Int := 2
def sqId : Int := 0
def g2Id : Int := 0

-- ══ RUNG 2 encoding — ground `proj`/FieldProj to the REAL emitted `fixlib.Point`.
--    A record value can't survive the flat-Int `eval` as itself: `proj : Int → Int →
--    Int` reads an Int base. So grounding proj is an ENCODING theorem (recon note A),
--    not an rfl discharge — CHOOSE `embPoint : fixlib.Point → Int` and PROVE the proj
--    oracle inverts the constructor w.r.t. it. `Point` has ONE constructor (no tag
--    decode), so the encoding is a plain base-2^64 pairing `a·2^64 + b`, whose
--    round-trip is `omega`-provable and REUSES the fixture obligation's own field
--    bound `0 ≤ b < 2^64` (`h_b_bound` in mk_point.lean). embPoint + the fnN pin
--    reference the GENUINE emitted `fixlib.Point.mk`/`.x`/`.y` — proj grounded to
--    emitter output, the faithful analog of rung-1's `fixlib.sq`. ══
def POW : Int := 18446744073709551616          -- 2^64 field width (the fixture's bound)
def xFieldId : Int := 0
def yFieldId : Int := 1                         -- DISTINCT from xFieldId (proj if-guard)
def mkPointId : Int := 1                        -- fnN id of the `Point.mk` constructor

-- the embedding: pack the REAL emitted `fixlib.Point` projections base-2^64.
noncomputable def embPoint (p : fixlib.Point) : Int := p.x * POW + p.y
-- the constructor pin (fnN): build the real `fixlib.Point.mk` from args, then embed.
noncomputable def mkPointLift : List Int → Int :=
  fun xs => match xs with
    | a :: b :: _ => embPoint (fixlib.Point.mk a b)
    | _           => 0

-- ══ RUNG 3 encoding — ground `ctorTag`/`ctorField` (the Match decode oracles) over the
--    REAL emitted ENUM `fixlib.Tree` + the REAL match-bodied `fixlib.tree_head`. This is
--    the Hard Rung (recon note A): a genuine encoding theorem, not an rfl discharge —
--    CHOOSE `embTree : fixlib.Tree → Int` and PROVE the `ctorTag`/`ctorField` oracles
--    invert the constructor tag + fields w.r.t. it. The flat-Int model stores a Tree
--    value as ONE Int, and the emitted `tree_head`'s match (`Leaf v => v | Node _ _ => 0`)
--    maps EXACTLY onto FACT 9/10/11's 2-arm shape (arm0 = 1 binder, body reads it; arm1 =
--    2 binders, body 0). So grounding = pin the scrutinee slot to `embTree t` and
--    discharge FACT 9/10/11's `htag`/`hmiss`/`htag1` by the encoding consistency.
--
--    THE ENCODING (parity tag; low-bit = constructor). `Leaf v` ↦ EVEN `2·v` (the value
--    survives in the high bits, recoverable by `/2` — for ALL Int v, incl. negative);
--    `Node l r` ↦ ODD `2·(embTree l + embTree r)+1` (RECURSES through both children, so
--    it is a genuine whole-tree fold, not a constant). `ctorTag n = if n%2=0 then 0 else
--    1` picks the arm — robust to the Int emod/tdiv sign convention (odd is NEVER ≡0 mod
--    2 under either; Danielle's model flagged the naked `n%2` trap for negative-odd, so
--    the guarded form is used). `ctorField n _ = n/2` recovers the Leaf payload.
--
--    SCOPE (honest, per Danielle's model + card): `tree_head` never READS Node children
--    (returns 0 for every Node), so its faithful grounding needs the Node PARITY (tag)
--    only, NOT Node-child DECODE. Full injective Node decode = an invertible unbounded
--    pairing, which is OUTSIDE omega's Presburger fragment (no Mathlib here) — that is
--    the genuine remaining hard kernel, explicitly DEFERRED. What lands here: the tags
--    (both ctors) + the Leaf field are grounded to a real encoding of the real `Tree`,
--    tying the flat-Int Match evaluation to the REAL `fixlib.tree_head t` for ALL t. ══
def leafTag : Int := 0                          -- Tree.Leaf constructor id (even → low bit 0)
def nodeTag : Int := 1                          -- Tree.Node constructor id (odd → low bit 1)

-- the embedding: pack the REAL emitted `fixlib.Tree` base-2 with the ctor tag in the low
-- bit. Well-founded (through `Tactus.Box`, mirroring the emitted `Tree.height`); its two
-- head equations are the `embTree_leaf`/`embTree_node` rfl-grade lemmas below.
noncomputable def embTree (t : fixlib.Tree) : Int :=
  match t with
  | fixlib.Tree.Leaf v => 2 * v
  | fixlib.Tree.Node l r => 2 * (embTree l.deref + embTree r.deref) + 1
termination_by sizeOf t
decreasing_by all_goals (simp_all; omega)

theorem embTree_leaf (v : Int) : embTree (fixlib.Tree.Leaf v) = 2 * v := by
  simp only [embTree]
theorem embTree_node (l r : Tactus.Box fixlib.Tree) :
    embTree (fixlib.Tree.Node l r) = 2 * (embTree l.deref + embTree r.deref) + 1 := by
  simp only [embTree]

-- ── the per-crate SymEnv literal (P5 match-literal discipline, cf. probe5's
--    `crateEnv`). fn/fnN PINNED to the renamed emitter output; proj PINNED to the
--    base-2^64 decode of the `fixlib.Point` embedding (rung 2). av/avP given their
--    natural readings (atom id = state variable). ctorTag/ctorField stubbed to 0 —
--    rung 3 pins those (the enum+Match encoding theorem).
noncomputable def crateEnv : SymEnv where
  av        := fun id st => st id
  avP       := fun id st => st id ≠ 0
  opk       := fun o => match o with
                        | 2  => OpKind.lt
                        | 3  => OpKind.le
                        | 11 => OpKind.andC
                        | _  => OpKind.other
  fn        := fun f => match f with | 0 => sqLift | _ => fun _ => 0
  fnN       := fun f => match f with | 0 => g2Lift | 1 => mkPointLift | _ => fun _ => 0
  proj      := fun v fld => if fld = xFieldId then v / POW
                            else if fld = yFieldId then v % POW else 0
  -- RUNG 3: pinned to the `fixlib.Tree` parity encoding. `ctorTag` reads the low bit
  -- (guarded form — sign-convention-robust); `ctorField` recovers the packed payload.
  ctorTag   := fun n => if n % 2 = 0 then leafTag else nodeTag
  ctorField := fun n _ => n / 2

-- ── the free hypotheses of FACT 5/8, now DISCHARGED (not passed in) by rfl. This is
--    the whole point: the oracle lookups reduce to the real emitted defs. ──
theorem hop_lt   : crateEnv.opk ltId = OpKind.lt := rfl
theorem hfn_sq   : crateEnv.fn sqId  = sqLift    := rfl
theorem hfnN_g2  : crateEnv.fnN g2Id = g2Lift    := rfl

-- ══ RUNG 1a — the UNARY CALL leaf pinned to emitter output. FACT 5 specialized:
--    the rendered obligation `sq(n) < 10` DENOTES `fixlib.sq (st n).toNat < 10` — the
--    leaf reads the REAL emitted `fixlib.sq`, with `hfn` discharged by `rfl`. ══
theorem ground_app_sq (nId : Int) (st : St) :
    edenote crateEnv (lib.render_exp
      (lib.RawExp.BinOp ltId lib.TypData.TyBool
        (Tactus.Box.mk (lib.RawExp.Call sqId lib.TypData.TyInt
          (Tactus.Box.mk (lib.RawExp.Var nId lib.TypData.TyInt)) lib.TypData.TyInt))
        (Tactus.Box.mk (lib.RawExp.Lit 10 lib.TypData.TyInt)))) st
      ↔ ((fixlib.sq (st nId).toNat : Int) < 10) :=
  -- FACT 5 gives `… ↔ sqLift (crateEnv.av nId st) < 10`; the goal RHS is defeq
  -- (sqLift unfolds to fixlib.sq∘toNat, crateEnv.av nId st = st nId).
  adequacy_leaf_app_grounded crateEnv nId sqId ltId sqLift st hop_lt hfn_sq

-- ══ RUNG 1b — the N-ARY CALL leaf pinned to emitter output. FACT 8 specialized:
--    `g2(m, n) < 100` DENOTES `fixlib.g2 (st m).toNat (st n).toNat < 100`, with the
--    `evalList` arg-fold grounded through the RENAMED emitted `fixlib.g2`; `hfnN`
--    discharged by `rfl`. ══
theorem ground_appn_g2 (mId nId : Int) (st : St) :
    edenote crateEnv (lib.render_exp
      (lib.RawExp.BinOp ltId lib.TypData.TyBool
        (Tactus.Box.mk (lib.RawExp.CallN g2Id lib.TypData.TyInt
          (Tactus.Box.mk (lib.RawList.Cons
            (Tactus.Box.mk (lib.RawExp.Var mId lib.TypData.TyInt))
            (Tactus.Box.mk (lib.RawList.Cons
              (Tactus.Box.mk (lib.RawExp.Var nId lib.TypData.TyInt))
              (Tactus.Box.mk lib.RawList.Nil)))))))
        (Tactus.Box.mk (lib.RawExp.Lit 100 lib.TypData.TyInt)))) st
      ↔ ((fixlib.g2 (st mId).toNat (st nId).toNat : Int) < 100) :=
  -- FACT 8 gives `… ↔ g2Lift [crateEnv.av mId st, crateEnv.av nId st] < 100`; the
  -- goal RHS is defeq (g2Lift's 2-elt-list match reduces to fixlib.g2∘toNat).
  adequacy_leaf_appn_grounded crateEnv mId nId g2Id ltId g2Lift st hop_lt hfnN_g2

-- ══════════════════════════════════════════════════════════════════════
-- RUNG 2 — ground `proj`/FieldProj to the REAL emitted `fixlib.Point` structure.
-- ══════════════════════════════════════════════════════════════════════

-- ── the emitted-constructor base: `Point.mk a b` rendered as an N-ary call (recon
--    note B — constructor apps render through AppN). Its `eval` is the `mkPointId`
--    fnN pin, i.e. `embPoint (fixlib.Point.mk (st a) (st b))`. ──
def mkPointCall (aId bId : Int) : lib.RawExp :=
  lib.RawExp.CallN mkPointId lib.TypData.TyInt
    (Tactus.Box.mk (lib.RawList.Cons
      (Tactus.Box.mk (lib.RawExp.Var aId lib.TypData.TyInt))
      (Tactus.Box.mk (lib.RawList.Cons
        (Tactus.Box.mk (lib.RawExp.Var bId lib.TypData.TyInt))
        (Tactus.Box.mk lib.RawList.Nil)))))

-- ══ RUNG 2 ENCODING THEOREM — the proj oracle inverts the constructor. NOT an rfl
--    discharge (recon note A): a genuine base-2^64 round-trip, closed by `omega`,
--    consuming EXACTLY the fixture obligation's own field bound `0 ≤ b < 2^64`
--    (`h_b_bound` in mk_point.lean). `embPoint (fixlib.Point.mk a b)` reduces (rfl,
--    via the REAL `.x`/`.y` structure projections) to `a·POW + b`; the proj if-guard
--    selects the field, and `omega` recovers the component. This is what makes proj
--    "grounded to emitter output": the flat-Int oracle provably AGREES with the real
--    `fixlib.Point` projection. ══
theorem proj_x_consistent (a b : Int) (hb : 0 ≤ b ∧ b < POW) :
    crateEnv.proj (embPoint (fixlib.Point.mk a b)) xFieldId = a := by
  show (a * POW + b) / POW = a
  unfold POW at *; omega

theorem proj_y_consistent (a b : Int) (hb : 0 ≤ b ∧ b < POW) :
    crateEnv.proj (embPoint (fixlib.Point.mk a b)) yFieldId = b := by
  show (a * POW + b) % POW = b
  unfold POW at *; omega

-- ══ RUNG 2a — the x-field leaf pinned to emitter output. FACT 12 reduces the rendered
--    obligation `(Point.mk a b).x < 10` to `crateEnv.proj ⟦Point.mk a b⟧ xFieldId < 10`;
--    the encoding theorem then grounds that to the REAL `(fixlib.Point.mk (st a)(st b)).x`.
--    Needs the y-component bound (the packed field the x-decode divides out) — supplied
--    by the fixture's `h_b_bound`. ══
theorem ground_proj_x (aId bId : Int) (st : St) (hb : 0 ≤ st bId ∧ st bId < POW) :
    edenote crateEnv (lib.render_exp
      (lib.RawExp.BinOp ltId lib.TypData.TyBool
        (Tactus.Box.mk (lib.RawExp.Field xFieldId lib.TypData.TyInt
          (Tactus.Box.mk (mkPointCall aId bId))))
        (Tactus.Box.mk (lib.RawExp.Lit 10 lib.TypData.TyInt)))) st
      ↔ ((fixlib.Point.mk (st aId) (st bId)).x < 10) := by
  rw [adequacy_leaf_proj crateEnv xFieldId ltId (mkPointCall aId bId) st hop_lt]
  -- goal LHS eval reduces (rfl) to `embPoint (fixlib.Point.mk (st aId) (st bId))`;
  -- the encoding theorem grounds proj to the real `.x`.
  have hx : crateEnv.proj (eval crateEnv (lib.render_exp (mkPointCall aId bId)) st) xFieldId
          = (fixlib.Point.mk (st aId) (st bId)).x :=
    proj_x_consistent (st aId) (st bId) hb
  rw [hx]

-- ══ RUNG 2b — the y-field mirror. `(Point.mk a b).y < 10` grounds to the real
--    `(fixlib.Point.mk (st a)(st b)).y` via the `% POW` decode. ══
theorem ground_proj_y (aId bId : Int) (st : St) (hb : 0 ≤ st bId ∧ st bId < POW) :
    edenote crateEnv (lib.render_exp
      (lib.RawExp.BinOp ltId lib.TypData.TyBool
        (Tactus.Box.mk (lib.RawExp.Field yFieldId lib.TypData.TyInt
          (Tactus.Box.mk (mkPointCall aId bId))))
        (Tactus.Box.mk (lib.RawExp.Lit 10 lib.TypData.TyInt)))) st
      ↔ ((fixlib.Point.mk (st aId) (st bId)).y < 10) := by
  rw [adequacy_leaf_proj crateEnv yFieldId ltId (mkPointCall aId bId) st hop_lt]
  have hy : crateEnv.proj (eval crateEnv (lib.render_exp (mkPointCall aId bId)) st) yFieldId
          = (fixlib.Point.mk (st aId) (st bId)).y :=
    proj_y_consistent (st aId) (st bId) hb
  rw [hy]

-- ══════════════════════════════════════════════════════════════════════
-- RUNG 3 — ground `ctorTag`/`ctorField` to the REAL `fixlib.Tree` + `fixlib.tree_head`.
-- ══════════════════════════════════════════════════════════════════════

-- ── the rendered `tree_head` match, shared by the three grounded facts. Matches FACT
--    9/10/11's inline `MatchR` exactly (abbrev ⇒ reducibly interchangeable with the
--    fact's own expression, so the `rw [FACT]` fires). arm0 = Leaf (ctor c0, binds
--    [xId], body reads xId); arm1 = Node (ctor c1, binds [yId,zId], body 0). ──
abbrev treeHeadMatchR (scrutId c0 c1 xId yId zId : Int) : lib.RawExp :=
  lib.RawExp.MatchR
    (Tactus.Box.mk (lib.RawExp.Var scrutId (lib.TypData.TyNamed 100)))
    (Tactus.Box.mk (lib.RawArmList.Cons c0
      (lib.BinderIdList.Cons xId (Tactus.Box.mk lib.BinderIdList.Nil))
      (Tactus.Box.mk (lib.RawExp.Var xId lib.TypData.TyInt))
      (Tactus.Box.mk (lib.RawArmList.Cons c1
        (lib.BinderIdList.Cons yId (Tactus.Box.mk (lib.BinderIdList.Cons zId (Tactus.Box.mk lib.BinderIdList.Nil))))
        (Tactus.Box.mk (lib.RawExp.Lit 0 lib.TypData.TyInt))
        (Tactus.Box.mk lib.RawArmList.Nil)))))
    lib.TypData.TyInt

-- ══ RUNG 3 ENCODING CONSISTENCY (the encoding theorem) — the `ctorTag`/`ctorField`
--    oracles invert the constructor tag + Leaf field w.r.t. `embTree`. omega round-trips
--    over the parity encoding (recon note A: a genuine proof, not an rfl discharge). ══
theorem ctorTag_leaf (v : Int) :
    crateEnv.ctorTag (embTree (fixlib.Tree.Leaf v)) = leafTag := by
  show (if (embTree (fixlib.Tree.Leaf v)) % 2 = 0 then (0:Int) else 1) = 0
  rw [embTree_leaf]; omega
theorem ctorTag_node (l r : Tactus.Box fixlib.Tree) :
    crateEnv.ctorTag (embTree (fixlib.Tree.Node l r)) = nodeTag := by
  show (if (embTree (fixlib.Tree.Node l r)) % 2 = 0 then (0:Int) else 1) = 1
  rw [embTree_node]; omega
theorem ctorTag_node_ne_leaf (l r : Tactus.Box fixlib.Tree) :
    crateEnv.ctorTag (embTree (fixlib.Tree.Node l r)) ≠ leafTag := by
  rw [ctorTag_node]; decide
theorem ctorField_leaf (v : Int) :
    crateEnv.ctorField (embTree (fixlib.Tree.Leaf v)) 0 = v := by
  show (embTree (fixlib.Tree.Leaf v)) / 2 = v
  rw [embTree_leaf]; omega

-- ══ RUNG 3a — the LEAF-arm VALUE leaf pinned to emitter output. The scrutinee slot holds
--    `embTree (Leaf v)`; FACT 9 selects arm0 (`htag` discharged by `ctorTag_leaf`, NOT
--    passed in) and reads the threaded binder; the encoding grounds the whole match to the
--    REAL `fixlib.tree_head (Leaf v)` (= v). ══
theorem ground_match_leaf_val (scrutId xId yId zId : Int) (st : St) (v : Int)
    (hscrut : st scrutId = embTree (fixlib.Tree.Leaf v)) :
    eval crateEnv (lib.render_exp (treeHeadMatchR scrutId leafTag nodeTag xId yId zId)) st
      = fixlib.tree_head (fixlib.Tree.Leaf v) := by
  have htag : crateEnv.ctorTag (crateEnv.av scrutId st) = leafTag := by
    show crateEnv.ctorTag (st scrutId) = leafTag
    rw [hscrut]; exact ctorTag_leaf v
  rw [adequacy_leaf_match_hd crateEnv scrutId leafTag nodeTag xId yId zId st htag]
  -- RHS: `av xId (upd st xId (ctorField (st scrutId) 0))` → `(st scrutId)/2` → `(2v)/2` = v;
  --      `tree_head (Leaf v)` reduces (rfl) to v.
  show (if xId = xId then (crateEnv.ctorField (st scrutId) 0) else st xId)
      = fixlib.tree_head (fixlib.Tree.Leaf v)
  rw [if_pos rfl]
  show (st scrutId) / 2 = v
  rw [hscrut, embTree_leaf]; omega

-- ══ RUNG 3b — the NODE-arm VALUE leaf pinned to emitter output. The scrutinee slot holds
--    `embTree (Node l r)`; FACT 10 walks PAST arm0 (`hmiss` by `ctorTag_node_ne_leaf`) to
--    arm1 (`htag1` by `ctorTag_node`), whose body is 0 = the REAL `fixlib.tree_head (Node
--    l r)`. Exercises the recursive arm walk over the real enum's Node ctor. ══
theorem ground_match_node_val (scrutId xId yId zId : Int) (st : St)
    (l r : Tactus.Box fixlib.Tree) (hscrut : st scrutId = embTree (fixlib.Tree.Node l r)) :
    eval crateEnv (lib.render_exp (treeHeadMatchR scrutId leafTag nodeTag xId yId zId)) st
      = fixlib.tree_head (fixlib.Tree.Node l r) := by
  have hmiss : crateEnv.ctorTag (crateEnv.av scrutId st) ≠ leafTag := by
    show crateEnv.ctorTag (st scrutId) ≠ leafTag
    rw [hscrut]; exact ctorTag_node_ne_leaf l r
  have htag1 : crateEnv.ctorTag (crateEnv.av scrutId st) = nodeTag := by
    show crateEnv.ctorTag (st scrutId) = nodeTag
    rw [hscrut]; exact ctorTag_node l r
  rw [adequacy_leaf_match_tl crateEnv scrutId leafTag nodeTag xId yId zId st hmiss htag1]
  -- FACT 10 gives `= 0`; `fixlib.tree_head (Node l r)` reduces (rfl) to 0.
  rfl

-- ══ RUNG 3c — the LEAF-arm PROP leaf pinned to emitter output. The prop-position mirror
--    (FACT 11 / `edenote`): the arm-0 body's Prop reading is `avP xId (…)` = `(st slot ≠
--    0)`, grounded to the REAL `fixlib.tree_head (Leaf v) ≠ 0` (= `v ≠ 0`). ══
theorem ground_match_leaf_prop (scrutId xId yId zId : Int) (st : St) (v : Int)
    (hscrut : st scrutId = embTree (fixlib.Tree.Leaf v)) :
    edenote crateEnv (lib.render_exp (treeHeadMatchR scrutId leafTag nodeTag xId yId zId)) st
      ↔ (fixlib.tree_head (fixlib.Tree.Leaf v) ≠ 0) := by
  have htag : crateEnv.ctorTag (crateEnv.av scrutId st) = leafTag := by
    show crateEnv.ctorTag (st scrutId) = leafTag
    rw [hscrut]; exact ctorTag_leaf v
  rw [adequacy_leaf_match_prop_hd crateEnv scrutId leafTag nodeTag xId yId zId st htag]
  -- RHS: `avP xId (upd st xId (ctorField (st scrutId) 0))` = `((st scrutId)/2 ≠ 0)` =
  --      `((2v)/2 ≠ 0)` = `(v ≠ 0)`; `tree_head (Leaf v) ≠ 0` reduces to `v ≠ 0`.
  show (if xId = xId then (crateEnv.ctorField (st scrutId) 0) else st xId) ≠ 0
      ↔ (v ≠ 0)
  rw [if_pos rfl]
  show ((st scrutId) / 2 ≠ 0) ↔ (v ≠ 0)
  have h2 : (2 * v) / 2 = v := by omega
  rw [hscrut, embTree_leaf, h2]

end W5fGround

-- axiom closure (regression guard): the grounded CALL-fragment facts close over ONLY
-- standard logical axioms — the oracle discharge is `rfl` (kernel iota/delta on the
-- concrete crateEnv literal + the renamed emitted fixlib defs), adding nothing beyond
-- the propext FACT 5/8 already carry. NO Classical.choice, NO sorryAx. The rung-2
-- encoding theorems (proj_*_consistent) are `omega` round-trips → expect [propext].
#print axioms W5fGround.hfn_sq
#print axioms W5fGround.hfnN_g2
#print axioms W5fGround.ground_app_sq
#print axioms W5fGround.ground_appn_g2
#print axioms W5fGround.proj_x_consistent    -- rung 2: base-2^64 x-decode round-trip
#print axioms W5fGround.proj_y_consistent    -- rung 2: base-2^64 y-decode round-trip
#print axioms W5fGround.ground_proj_x        -- rung 2: (Point.mk a b).x grounded
#print axioms W5fGround.ground_proj_y        -- rung 2: (Point.mk a b).y grounded
-- rung 3: the ctorTag/ctorField parity-encoding consistency (the encoding theorem) +
-- the three grounded Match facts tied to the REAL fixlib.tree_head. Expect [propext,
-- Quot.sound] (omega Int div/mod + the wf-rec embTree unfold) — no Classical.choice, no
-- sorryAx (matches rung-2's proj_*_consistent axiom profile).
#print axioms W5fGround.ctorTag_leaf         -- rung 3: Leaf tag decode (parity)
#print axioms W5fGround.ctorTag_node         -- rung 3: Node tag decode (parity)
#print axioms W5fGround.ctorField_leaf       -- rung 3: Leaf field decode (/2)
#print axioms W5fGround.ground_match_leaf_val  -- rung 3: Match Leaf arm → tree_head (=v)
#print axioms W5fGround.ground_match_node_val  -- rung 3: Match Node arm → tree_head (=0)
#print axioms W5fGround.ground_match_leaf_prop -- rung 3: Match Leaf arm, prop position
