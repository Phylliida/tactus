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

-- ── the per-crate SymEnv literal (P5 match-literal discipline, cf. probe5's
--    `crateEnv`). fn/fnN PINNED to the renamed emitter output. av/avP given their
--    natural readings (atom id = state variable). proj/ctorTag/ctorField are stubbed
--    to 0 — rungs 2/3 pin those; rung 1 is the CALL fragment only.
noncomputable def crateEnv : SymEnv where
  av        := fun id st => st id
  avP       := fun id st => st id ≠ 0
  opk       := fun o => match o with
                        | 2  => OpKind.lt
                        | 3  => OpKind.le
                        | 11 => OpKind.andC
                        | _  => OpKind.other
  fn        := fun f => match f with | 0 => sqLift | _ => fun _ => 0
  fnN       := fun f => match f with | 0 => g2Lift | _ => fun _ => 0
  proj      := fun _ _ => 0
  ctorTag   := fun _ => 0
  ctorField := fun _ _ => 0

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

end W5fGround

-- axiom closure (regression guard): the grounded CALL-fragment facts close over ONLY
-- standard logical axioms — the oracle discharge is `rfl` (kernel iota/delta on the
-- concrete crateEnv literal + the renamed emitted fixlib defs), adding nothing beyond
-- the propext FACT 5/8 already carry. NO Classical.choice, NO sorryAx.
#print axioms W5fGround.hfn_sq
#print axioms W5fGround.hfnN_g2
#print axioms W5fGround.ground_app_sq
#print axioms W5fGround.ground_appn_g2
