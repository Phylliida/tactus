/- W7a probe (board bootstrap-26): the defs-layer analog of W6a
   (probe12_w6a_castleaf). Prove the DEFINITION-level bridge mechanic
   end-to-end in a standalone `.lean` (ZERO `tactus-core` edit → zero cache
   churn) and FREEZE the extended body vocabulary the one batched W7b edit
   will land. Parent design: DESIGN-W7-defslayer.md (§3.1 the ExprData
   superset, §4 the mirrors, §6 the ladder, §7 open questions).

   W6a certified an obligation LEAF (one expression). W7 certifies the
   DEFINITIONS the obligations are stated in terms of: `@[reducible] def`
   spec-fn bodies, `inductive` datatype decls, and `<T>.height` measures.
   A wrong-but-CONSISTENT def lowering (both the obligation and the def read
   the same wrong denotation) is invisible to obligation-level bridges — this
   is trust-inventory row 4. W7 closes it with an INDEPENDENT `render_def`.

   What this probe freezes for W7b (the extended vocabulary):
     * ExprData / RawExp gain the body constructors bodies use that W6 lacked:
       `Ite` (first-class if — W6 G4 folded If→Let), `Match` (scrutinee +
       arms, each arm = ctor id + bound-var ids + arm body — inductive spec
       fns are match-bodied), `AppN` (multi-arg application — W6 App was
       single-arg), `Forall`/`Exists` (quantifier nodes — GoalData::All was
       goal-level only).
     * DefData / RawDef + render_def : the def HEADER (name, typed params,
       ret) around a body ExprData; render_def is an INDEPENDENT lowering
       (transcribe a RawDef straight from VIR, NOT through production's
       renderer — the §2 diversity that gives the bridge teeth).
     * DtData / RawDt / CtorData + render_dt : positional field TYPES only
       (accessor names are a separate certifiable surface — §7 Q4).
     * TypData gains `box` (Box<T> is NOT Ref<T> — conflating them would mask a
       real Box/Ref field bug; §7 Q4 verdict).

   Bridge per case: the CORRECT production DefData/DtData EQUALS render_def(raw)
   / render_dt(raw) (closes by `decide` AND `rfl`); a body/ctor/measure
   mutation is PROVABLY unequal (`¬ (… = …)` by `decide`) — mutation-kill at
   the definition level. The primary equality is Lean's derived structural
   `=` on the mirrors (the W6a discipline); W7b's nat-returning `def_eq` will
   extend the W6 `expr_eq` tag+projection idiom (the arm-list one novel step,
   §7 Q1) — the §Q1 demonstration below pins that concretely.

   Pure Lean core: no Mathlib, no prelude imports, no tactus-core oleans. Run
   with just `lean probe15_w7a_defs.lean`. Ground truth for every shape is the
   REAL emitted fixture: bootstrap-fixture/out/lib/{TactusDefs_lib_exec__root,
   TactusDefs_lib_exec__base}.lean (tri / tree_head / Tree / Tree.height). -/

-- ── mirror types (the shapes W7b lands in tactus-core) ──────────────────────

/-- Type mirror. W6 needed int/nat/bool/named/ref; W7 adds `box` for the
    `Box<T>` datatype field type (`Node (val0 : Tactus.Box lib.Tree)`), kept
    DISTINCT from `ref` (`&T` borrow) — see §7 Q4 verdict in the report. -/
inductive TypData where
  | int
  | nat
  | bool
  | named (id : Nat)
  | ref   (inner : Nat)
  | box   (inner : Nat)
deriving DecidableEq, Repr

inductive CastKind where
  | intToNat   -- `Int.toNat` (the materialized `as nat`)
  | natToInt   -- `Int.ofNat`
deriving DecidableEq, Repr

/- The expression mirror — the W6 hybrid leaf EXTENDED with the four body
   constructors (§3.1). `Match`/`AppN` recurse through dedicated list
   inductives (ArmList/ExprList), mirroring production's own `RawExpList`
   discipline (dedicated list types, not `Seq`/`Vec`, so the tactus Lean
   backend reduces them). Atoms stay interned `Nat` (a forgotten node is a
   shape diff — the §2.1 W6 safety condition, one level up). -/
mutual
inductive ExprData where
  -- W6 subset (verbatim from tactus-core/lib.rs:282):
  | atom      (id : Nat)                        -- var read / spec-fn or type name
  | lit       (val : Int)
  | litBool   (val : Nat)                       -- 0/1 nat encoding (bool → Prop)
  | cast      (k : CastKind) (e : ExprData)
  | binOp     (op : Nat) (l r : ExprData)
  | app       (fn : Nat) (arg : ExprData)       -- single-arg call (kept for the common case)
  | fieldProj (e : ExprData) (field : Nat)      -- `.deref`, `.x`, `.1`
  | spanMark  (loc : Nat) (e : ExprData)
  | letE      (name : Nat) (val body : ExprData)
  | notE      (e : ExprData)
  -- W7 body constructors (the freeze):
  | ite       (c t e : ExprData)                     -- first-class `if c then t else e`
  | matchE    (scrut : ExprData) (arms : ArmList)    -- `match scrut with | …`
  | appN      (fn : Nat) (args : ExprList)           -- multi-arg `f a b c`
  | forallE   (bid : Nat) (bty : TypData) (body : ExprData)
  | existsE   (bid : Nat) (bty : TypData) (body : ExprData)
inductive MatchArm where
  | arm (ctor : Nat) (binders : List Nat) (body : ExprData)   -- ctor id + bound vars + body
inductive ArmList where
  | nil | cons (hd : MatchArm) (tl : ArmList)
inductive ExprList where
  | nil | cons (hd : ExprData) (tl : ExprList)
end
deriving instance DecidableEq for ExprData, MatchArm, ArmList, ExprList

/- The independent RAW input — the VIR-transcribed tree, type-tagged, NOT run
   through production's renderer. `Match`/`AppN` carry a result type (`ty` /
   `ret`) so `type_of` reads it in one step and `render` can coerce arm
   bodies / the value under a nat return type (the Friction-2 discipline,
   parallel to `BinOp`). No `HasType` node — the unsigned-overflow refinement
   is an obligation-goal construct, not a spec-fn body construct. -/
mutual
inductive RawExp where
  | var     (id : Nat) (ty : TypData)
  | lit     (val : Int) (ty : TypData)
  | litBool (val : Nat)
  | clip    (target : TypData) (e : RawExp)             -- explicit `as` cast (Verus Clip)
  | binOp   (op : Nat) (ty : TypData) (l r : RawExp)    -- 2nd slot = op RESULT type
  | call    (fn : Nat) (ret : TypData) (arg : RawExp) (argTy : TypData)
  | field   (fid : Nat) (fty : TypData) (base : RawExp)
  | deref   (e : RawExp)                                -- `*t` / `*l` → `.deref` FieldProj
  | letE    (name : Nat) (val body : RawExp)
  | notE    (e : RawExp)
  | span    (loc : Nat) (e : RawExp)
  -- W7 body constructors:
  | ite     (ty : TypData) (c t e : RawExp)             -- ty = branch RESULT type
  | matchR  (scrut : RawExp) (arms : RawArmList) (ty : TypData)   -- ty = arm-body RESULT type
  | callN   (fn : Nat) (ret : TypData) (args : RawList)
  | forallR (bid : Nat) (bty : TypData) (body : RawExp)
  | existsR (bid : Nat) (bty : TypData) (body : RawExp)
inductive RawArm where
  | arm (ctor : Nat) (binders : List Nat) (body : RawExp)
inductive RawArmList where
  | nil | cons (hd : RawArm) (tl : RawArmList)
inductive RawList where
  | nil | cons (hd : RawExp) (tl : RawList)
end

-- ── the def/dt top-level mirrors (§4 shapes) ────────────────────────────────
-- DefData/RawDef are NOT in the mutual group: a body contains an ExprData, but
-- ExprData never contains a DefData, so plain structures suffice.

/-- `@[reducible] def <name> <params> : <ret> := <body>`. Params carry TypData
    (a wrong param type is a real, certifiable bug — so typed, not the
    opaque-`u64` `BinderList` production uses for hypotheses). -/
structure DefData where
  name   : Nat
  params : List (Nat × TypData)
  ret    : TypData
  body   : ExprData
deriving DecidableEq

structure RawDef where
  name   : Nat
  params : List (Nat × TypData)
  ret    : TypData
  body   : RawExp

/-- One `inductive` constructor: name + POSITIONAL field types (no accessor
    names — §7 Q4). -/
structure CtorData where
  name   : Nat
  fields : List TypData
deriving DecidableEq

structure DtData where
  name  : Nat
  ctors : List CtorData
deriving DecidableEq

structure RawCtor where
  name   : Nat
  fields : List TypData

structure RawDt where
  name  : Nat
  ctors : List RawCtor

-- ── the reference lowering (INDEPENDENT reimplementation) ───────────────────

/-- The type a `Deref` presents to its parent: `&T` (`ref`) and `Box<T>`
    (`box`) both become the pointee `named T`; everything else derefs to
    itself. (Box and Ref differ semantically but deref identically.) -/
def deref_type : TypData → TypData
  | .ref inner => .named inner
  | .box inner => .named inner
  | .int       => .int
  | .nat       => .nat
  | .bool      => .bool
  | .named n   => .named n

/-- The rendered type a raw node presents to its parent. A `clip target`
    presents `target` (how an elided-clip operand still reads `int` and a
    materialized one reads `nat`); `matchR`/`ite`/`callN` present the carried
    result type. Recurses only within RawExp (never into arms) — structural. -/
def type_of : RawExp → TypData
  | .var _ ty        => ty
  | .lit _ ty        => ty
  | .litBool _       => .bool
  | .clip target _   => target
  | .binOp _ ty _ _  => ty
  | .call _ ret _ _  => ret
  | .field _ fty _   => fty
  | .deref e         => deref_type (type_of e)
  | .letE _ _ body   => type_of body
  | .notE _          => .bool
  | .span _ e        => type_of e
  | .ite ty _ _ _    => ty
  | .matchR _ _ ty   => ty
  | .callN _ ret _   => ret
  | .forallR _ _ _   => .bool
  | .existsR _ _ _   => .bool

/-- The coercion PREDICATE (unchanged from W6): an `int`-rendering operand
    under a `nat` target needs the `Int.toNat` the `as nat` denotes. -/
def needs_nat_coercion : TypData → TypData → Bool
  | .int, .nat => true
  | _,    _    => false

/-- A spec-fn `Call` arg whose mirror type is `ref` gets a `.deref` (the W6 G2
    path). Box-deref is modeled via an EXPLICIT `.deref` node instead (source
    `*l`), so `box` does NOT auto-fire here — no double-deref. -/
def needs_ref_deref : TypData → Bool
  | .ref _ => true
  | _      => false

def derefField : Nat := 0

@[inline] def coerceIf (b : Bool) (e : ExprData) : ExprData :=
  if b then .cast .intToNat e else e
@[inline] def derefIf (b : Bool) (e : ExprData) : ExprData :=
  if b then .fieldProj e derefField else e

/- `render_exp` reimplements the cast/coercion decision UNIFORMLY from the
   type tags — the W6 core, extended to the body constructors. Plainly
   structural over the mutual group (each call is on a subterm) so the kernel
   reduces it under `decide`/`rfl` (no `WellFounded.fix`). -/
mutual
def render_exp : RawExp → ExprData
  | .var id _        => .atom id
  | .lit v _         => .lit v
  | .litBool b       => .litBool b
  | .clip target e   => coerceIf (needs_nat_coercion (type_of e) target) (render_exp e)
  | .binOp op ty l r =>
      .binOp op
        (coerceIf (needs_nat_coercion (type_of l) ty) (render_exp l))
        (coerceIf (needs_nat_coercion (type_of r) ty) (render_exp r))
  | .call fn _ arg argTy =>
      -- W6 order: nat-coerce at the param type, THEN the G2 ref-deref.
      .app fn (derefIf (needs_ref_deref (type_of arg))
                 (coerceIf (needs_nat_coercion (type_of arg) argTy) (render_exp arg)))
  | .field fid _ base   => .fieldProj (render_exp base) fid
  | .deref e            => .fieldProj (render_exp e) derefField
  | .letE name val body => .letE name (render_exp val) (render_exp body)
  | .notE e             => .notE (render_exp e)
  | .span loc e         => .spanMark loc (render_exp e)
  -- W7: first-class if. Cond is bool (never coerced); each branch is
  -- materialized iff it renders int under a nat return type (Friction-2, like
  -- BinOp operands). tri's branches are already Nat, so no cast is inserted.
  | .ite ty c t e =>
      .ite (render_exp c)
        (coerceIf (needs_nat_coercion (type_of t) ty) (render_exp t))
        (coerceIf (needs_nat_coercion (type_of e) ty) (render_exp e))
  -- W7: match. Scrutinee is never coerced; each arm body is materialized like
  -- an Ite branch (the carried result type ty flows into render_arms).
  | .matchR scrut arms ty => .matchE (render_exp scrut) (render_arms arms ty)
  -- W7: multi-arg app. Args rendered straight (any coercion is a materialized
  -- `clip` in the arg; per-arg expected-type coercion is a W7c note, below).
  | .callN fn _ args => .appN fn (render_list args)
  -- W7: quantifiers pass the binder + type through; body renders recursively.
  | .forallR bid bty body => .forallE bid bty (render_exp body)
  | .existsR bid bty body => .existsE bid bty (render_exp body)
def render_arms : RawArmList → TypData → ArmList
  | .nil,       _  => .nil
  | .cons h t,  ty => .cons (render_arm h ty) (render_arms t ty)
def render_arm : RawArm → TypData → MatchArm
  -- binder ids ride STRAIGHT THROUGH (the §7 Q1 discipline: reference and
  -- production must intern arm-binder ids identically — a mismatch is a shape
  -- diff, demonstrated by B_th_binder_kill).
  | .arm c bs body, ty => .arm c bs (coerceIf (needs_nat_coercion (type_of body) ty) (render_exp body))
def render_list : RawList → ExprList
  | .nil       => .nil
  | .cons h t  => .cons (render_exp h) (render_list t)
end

/-- Reference def lowering: copy the header (name/params/ret transcribed
    directly from VIR), render the body independently. -/
def render_def : RawDef → DefData
  | ⟨name, params, ret, body⟩ => ⟨name, params, ret, render_exp body⟩

/-- Reference datatype lowering: ctor names + positional field types straight
    through (no body to render — the diversity is VIR-vs-LExpr transcription,
    which the probe abstracts as two hand-written inputs; a wrong-transcribed
    field type is the mutation-kill). -/
def render_ctor : RawCtor → CtorData
  | ⟨name, fields⟩ => ⟨name, fields⟩
def render_ctors : List RawCtor → List CtorData
  | []      => []
  | c :: t  => render_ctor c :: render_ctors t
def render_dt : RawDt → DtData
  | ⟨name, ctors⟩ => ⟨name, render_ctors ctors⟩

-- ── interned ids / opcodes (readability only; concrete Nats, internally
--    consistent between each raw/prod pair — NOT production's real interning) ─

def nId : Nat := 1          -- tri's `n`
def vId : Nat := 2          -- Leaf's `v`
def tId : Nat := 3          -- tree_head / sum_tree param `t`
def sId : Nat := 4          -- height param `s`
def lId : Nat := 5          -- Node's `l`
def rId : Nat := 6          -- Node's `r`
def val0Id : Nat := 7       -- height's `val0`
def val1Id : Nat := 8       -- height's `val1`
def aId : Nat := 9          -- synthetic AppN arg
def bId : Nat := 10         -- synthetic AppN arg
def kId : Nat := 15         -- synthetic forall binder
def wildId : Nat := 99      -- a `_` pattern field (positional, canonical id)
def triId : Nat := 20
def treeHeadId : Nat := 21
def sumTreeId : Nat := 22
def heightId : Nat := 23
def gId : Nat := 24         -- synthetic multi-arg spec fn
def leafCtor : Nat := 30
def nodeCtor : Nat := 31
def treeTy : Nat := 100     -- `lib.Tree`
def eqOp : Nat := 0
def mulOp : Nat := 1
def addOp : Nat := 6
def subOp : Nat := 7

/- ════════════════════════════════════════════════════════════════════════════
   CASE A — `Ite` via `tri`  (the first-class-if exemplar)
   Ground truth (TactusDefs_lib_exec__root.lean:9):
     def lib.tri (n : Nat) : Nat :=
       if n = 0 then 0 else n + lib.tri (Int.toNat (n - 1))
   Exercises: Ite + recursive Call(App) + Clip(→ Int.toNat) + BinOp (Eq/Add/Sub).
   ════════════════════════════════════════════════════════════════════════════ -/

def raw_tri : RawDef :=
  ⟨triId, [(nId, .nat)], .nat,
    .ite .nat
      (.binOp eqOp .bool (.var nId .nat) (.lit 0 .nat))            -- n = 0
      (.lit 0 .nat)                                                -- then 0
      (.binOp addOp .nat                                           -- else n + …
        (.var nId .nat)
        (.call triId .nat
          (.clip .nat (.binOp subOp .int (.var nId .int) (.lit 1 .int)))  -- Int.toNat (n - 1)
          .nat))⟩

def prod_tri_ok : DefData :=
  ⟨triId, [(nId, .nat)], .nat,
    .ite
      (.binOp eqOp (.atom nId) (.lit 0))
      (.lit 0)
      (.binOp addOp (.atom nId)
        (.app triId (.cast .intToNat (.binOp subOp (.atom nId) (.lit 1)))))⟩

theorem A_tri_ok_decide : render_def raw_tri = prod_tri_ok := by decide
theorem A_tri_ok_rfl    : render_def raw_tri = prod_tri_ok := by rfl

-- (a) swap the then/else branches
def prod_tri_swap : DefData :=
  ⟨triId, [(nId, .nat)], .nat,
    .ite (.binOp eqOp (.atom nId) (.lit 0))
      (.binOp addOp (.atom nId) (.app triId (.cast .intToNat (.binOp subOp (.atom nId) (.lit 1)))))
      (.lit 0)⟩
theorem A_tri_swap_kill : ¬ (render_def raw_tri = prod_tri_swap) := by decide

-- (b) drop the recursive `tri` call (else collapses to `n`)
def prod_tri_norecur : DefData :=
  ⟨triId, [(nId, .nat)], .nat,
    .ite (.binOp eqOp (.atom nId) (.lit 0)) (.lit 0) (.atom nId)⟩
theorem A_tri_norecur_kill : ¬ (render_def raw_tri = prod_tri_norecur) := by decide

-- (c) `+` ↔ `-` opcode in the else
def prod_tri_opswap : DefData :=
  ⟨triId, [(nId, .nat)], .nat,
    .ite (.binOp eqOp (.atom nId) (.lit 0)) (.lit 0)
      (.binOp subOp (.atom nId) (.app triId (.cast .intToNat (.binOp subOp (.atom nId) (.lit 1)))))⟩
theorem A_tri_opswap_kill : ¬ (render_def raw_tri = prod_tri_opswap) := by decide

-- (d) drop the `Int.toNat` (Clip) on `(n - 1)` — the Friction-2 dropped cast
def prod_tri_nocast : DefData :=
  ⟨triId, [(nId, .nat)], .nat,
    .ite (.binOp eqOp (.atom nId) (.lit 0)) (.lit 0)
      (.binOp addOp (.atom nId) (.app triId (.binOp subOp (.atom nId) (.lit 1))))⟩
theorem A_tri_nocast_kill : ¬ (render_def raw_tri = prod_tri_nocast) := by decide

/- ════════════════════════════════════════════════════════════════════════════
   CASE B — `Match` via `tree_head` + `sum_tree`
   tree_head ground truth (TactusDefs_lib_exec__root.lean:13):
     def lib.tree_head (t : lib.Tree) : Int :=
       match t with | lib.Tree.Leaf v => v | lib.Tree.Node _l _r => 0
   sum_tree is PRUNED from this fixture (no exec/proof caller pulls it), so its
   shape is the mechanical prediction from the source + the tree_head/height
   patterns — flagged as predicted, not emitted-verified (see report census).
   ════════════════════════════════════════════════════════════════════════════ -/

def raw_tree_head : RawDef :=
  ⟨treeHeadId, [(tId, .named treeTy)], .int,
    .matchR (.var tId (.named treeTy))
      (.cons (.arm leafCtor [vId] (.var vId .int))
        (.cons (.arm nodeCtor [lId, rId] (.lit 0 .int)) .nil)) .int⟩

def prod_tree_head_ok : DefData :=
  ⟨treeHeadId, [(tId, .named treeTy)], .int,
    .matchE (.atom tId)
      (.cons (.arm leafCtor [vId] (.atom vId))
        (.cons (.arm nodeCtor [lId, rId] (.lit 0)) .nil))⟩

theorem B_th_ok_decide : render_def raw_tree_head = prod_tree_head_ok := by decide
theorem B_th_ok_rfl    : render_def raw_tree_head = prod_tree_head_ok := by rfl

-- (a) wrong arm value: Leaf returns 0 instead of `v`
def prod_th_wrongval : DefData :=
  ⟨treeHeadId, [(tId, .named treeTy)], .int,
    .matchE (.atom tId)
      (.cons (.arm leafCtor [vId] (.lit 0))
        (.cons (.arm nodeCtor [lId, rId] (.lit 0)) .nil))⟩
theorem B_th_wrongval_kill : ¬ (render_def raw_tree_head = prod_th_wrongval) := by decide

-- (b) swapped arms (ctor ids exchanged)
def prod_th_swaparm : DefData :=
  ⟨treeHeadId, [(tId, .named treeTy)], .int,
    .matchE (.atom tId)
      (.cons (.arm nodeCtor [vId] (.atom vId))
        (.cons (.arm leafCtor [lId, rId] (.lit 0)) .nil))⟩
theorem B_th_swaparm_kill : ¬ (render_def raw_tree_head = prod_th_swaparm) := by decide

-- (b′) binder-id mismatch (Leaf binds wildId, body still reads vId) — the §7 Q1
--      discipline: arm binder ids are part of structural equality.
def prod_th_binder : DefData :=
  ⟨treeHeadId, [(tId, .named treeTy)], .int,
    .matchE (.atom tId)
      (.cons (.arm leafCtor [wildId] (.atom vId))
        (.cons (.arm nodeCtor [lId, rId] (.lit 0)) .nil))⟩
theorem B_th_binder_kill : ¬ (render_def raw_tree_head = prod_th_binder) := by decide

-- (c) forgotten Match (bare arm value, scrutinee dropped)
def prod_th_nomatch : DefData :=
  ⟨treeHeadId, [(tId, .named treeTy)], .int, .atom vId⟩
theorem B_th_nomatch_kill : ¬ (render_def raw_tree_head = prod_th_nomatch) := by decide

-- sum_tree: Match + recursion + Clip(`v as nat`) + Box-Deref (`*l`, `*r`)
def raw_sum_tree : RawDef :=
  ⟨sumTreeId, [(tId, .named treeTy)], .nat,
    .matchR (.var tId (.named treeTy))
      (.cons (.arm leafCtor [vId] (.clip .nat (.var vId .int)))          -- v as nat
        (.cons (.arm nodeCtor [lId, rId]
          (.binOp addOp .nat
            (.call sumTreeId .nat (.deref (.var lId (.box treeTy))) (.named treeTy))   -- sum_tree l.deref
            (.call sumTreeId .nat (.deref (.var rId (.box treeTy))) (.named treeTy))))
          .nil)) .nat⟩

def prod_sum_tree_ok : DefData :=
  ⟨sumTreeId, [(tId, .named treeTy)], .nat,
    .matchE (.atom tId)
      (.cons (.arm leafCtor [vId] (.cast .intToNat (.atom vId)))
        (.cons (.arm nodeCtor [lId, rId]
          (.binOp addOp
            (.app sumTreeId (.fieldProj (.atom lId) derefField))
            (.app sumTreeId (.fieldProj (.atom rId) derefField))))
          .nil))⟩

theorem B_st_ok_decide : render_def raw_sum_tree = prod_sum_tree_ok := by decide
theorem B_st_ok_rfl    : render_def raw_sum_tree = prod_sum_tree_ok := by rfl

-- dropped recursive call (Node's left summand becomes a bare deref)
def prod_st_norecur : DefData :=
  ⟨sumTreeId, [(tId, .named treeTy)], .nat,
    .matchE (.atom tId)
      (.cons (.arm leafCtor [vId] (.cast .intToNat (.atom vId)))
        (.cons (.arm nodeCtor [lId, rId]
          (.binOp addOp
            (.fieldProj (.atom lId) derefField)
            (.app sumTreeId (.fieldProj (.atom rId) derefField))))
          .nil))⟩
theorem B_st_norecur_kill : ¬ (render_def raw_sum_tree = prod_st_norecur) := by decide

-- dropped Box-`.deref` (sum_tree l instead of sum_tree l.deref)
def prod_st_noderef : DefData :=
  ⟨sumTreeId, [(tId, .named treeTy)], .nat,
    .matchE (.atom tId)
      (.cons (.arm leafCtor [vId] (.cast .intToNat (.atom vId)))
        (.cons (.arm nodeCtor [lId, rId]
          (.binOp addOp
            (.app sumTreeId (.atom lId))
            (.app sumTreeId (.fieldProj (.atom rId) derefField))))
          .nil))⟩
theorem B_st_noderef_kill : ¬ (render_def raw_sum_tree = prod_st_noderef) := by decide

/- ════════════════════════════════════════════════════════════════════════════
   CASE C — the `Tree` datatype + its `height` measure
   Ground truth (TactusDefs_lib_exec__base.lean:22 / :36):
     inductive lib.Tree where
       | Leaf (val0 : Int)
       | Node (val0 : Tactus.Box lib.Tree) (val1 : Tactus.Box lib.Tree)
     def lib.Tree.height (s : lib.Tree) : Nat :=
       match s with | Leaf _ => 1
                    | Node val0 val1 => 1 + Tree.height val0.deref + Tree.height val1.deref
   The height is MODELLED AS A DefData (§4) — a Match→Nat body whose arms call
   height itself (the §7 Q2 case: def_eq is syntactic, never reduces the callee).
   ════════════════════════════════════════════════════════════════════════════ -/

def raw_tree_dt : RawDt :=
  ⟨treeTy, [⟨leafCtor, [.int]⟩, ⟨nodeCtor, [.box treeTy, .box treeTy]⟩]⟩
def prod_tree_dt_ok : DtData :=
  ⟨treeTy, [⟨leafCtor, [.int]⟩, ⟨nodeCtor, [.box treeTy, .box treeTy]⟩]⟩

theorem C_dt_ok_decide : render_dt raw_tree_dt = prod_tree_dt_ok := by decide
theorem C_dt_ok_rfl    : render_dt raw_tree_dt = prod_tree_dt_ok := by rfl

-- ctor field-type wrong (Leaf carries Box<Tree> instead of Int) — the
-- Box-vs-Int / positional-field mutation-kill
def prod_tree_dt_wrong : DtData :=
  ⟨treeTy, [⟨leafCtor, [.box treeTy]⟩, ⟨nodeCtor, [.box treeTy, .box treeTy]⟩]⟩
theorem C_dt_wrong_kill : ¬ (render_dt raw_tree_dt = prod_tree_dt_wrong) := by decide

-- ctor order swapped
def prod_tree_dt_swap : DtData :=
  ⟨treeTy, [⟨nodeCtor, [.box treeTy, .box treeTy]⟩, ⟨leafCtor, [.int]⟩]⟩
theorem C_dt_swap_kill : ¬ (render_dt raw_tree_dt = prod_tree_dt_swap) := by decide

def raw_height : RawDef :=
  ⟨heightId, [(sId, .named treeTy)], .nat,
    .matchR (.var sId (.named treeTy))
      (.cons (.arm leafCtor [wildId] (.lit 1 .nat))                       -- Leaf _ => 1
        (.cons (.arm nodeCtor [val0Id, val1Id]                           -- Node val0 val1 =>
          (.binOp addOp .nat
            (.binOp addOp .nat
              (.lit 1 .nat)
              (.call heightId .nat (.deref (.var val0Id (.box treeTy))) (.named treeTy)))  -- height val0.deref
            (.call heightId .nat (.deref (.var val1Id (.box treeTy))) (.named treeTy))))   -- height val1.deref
          .nil)) .nat⟩

def prod_height_ok : DefData :=
  ⟨heightId, [(sId, .named treeTy)], .nat,
    .matchE (.atom sId)
      (.cons (.arm leafCtor [wildId] (.lit 1))
        (.cons (.arm nodeCtor [val0Id, val1Id]
          (.binOp addOp
            (.binOp addOp (.lit 1) (.app heightId (.fieldProj (.atom val0Id) derefField)))
            (.app heightId (.fieldProj (.atom val1Id) derefField))))
          .nil))⟩

theorem C_height_ok_decide : render_def raw_height = prod_height_ok := by decide
theorem C_height_ok_rfl    : render_def raw_height = prod_height_ok := by rfl

-- wrong measure (Leaf => 0 instead of 1)
def prod_height_wrong : DefData :=
  ⟨heightId, [(sId, .named treeTy)], .nat,
    .matchE (.atom sId)
      (.cons (.arm leafCtor [wildId] (.lit 0))
        (.cons (.arm nodeCtor [val0Id, val1Id]
          (.binOp addOp
            (.binOp addOp (.lit 1) (.app heightId (.fieldProj (.atom val0Id) derefField)))
            (.app heightId (.fieldProj (.atom val1Id) derefField))))
          .nil))⟩
theorem C_height_wrong_kill : ¬ (render_def raw_height = prod_height_wrong) := by decide

-- dropped recursive height call (val1 branch bare)
def prod_height_norecur : DefData :=
  ⟨heightId, [(sId, .named treeTy)], .nat,
    .matchE (.atom sId)
      (.cons (.arm leafCtor [wildId] (.lit 1))
        (.cons (.arm nodeCtor [val0Id, val1Id]
          (.binOp addOp
            (.binOp addOp (.lit 1) (.app heightId (.fieldProj (.atom val0Id) derefField)))
            (.fieldProj (.atom val1Id) derefField)))
          .nil))⟩
theorem C_height_norecur_kill : ¬ (render_def raw_height = prod_height_norecur) := by decide

/- ════════════════════════════════════════════════════════════════════════════
   VOCAB COMPLETENESS — `Forall` + `AppN`
   No fixture spec-fn BODY quantifies or multi-arg-calls (tri/tree_head/
   sum_tree/height are all ≤1-arg, non-quantified). These constructors are
   frozen for the tgt slice (W7d); validated here synthetically so the freeze
   is real (they kernel-compute + mutation-kill), not merely declared.
   ════════════════════════════════════════════════════════════════════════════ -/

-- Forall: `∀ k : Nat, k = k`
def raw_forall : RawExp :=
  .forallR kId .nat (.binOp eqOp .bool (.var kId .nat) (.var kId .nat))
def prod_forall_ok : ExprData :=
  .forallE kId .nat (.binOp eqOp (.atom kId) (.atom kId))
theorem V_forall_ok_decide : render_exp raw_forall = prod_forall_ok := by decide
def prod_forall_wrongty : ExprData :=
  .forallE kId .int (.binOp eqOp (.atom kId) (.atom kId))    -- binder type mutated
theorem V_forall_kill : ¬ (render_exp raw_forall = prod_forall_wrongty) := by decide

-- AppN: `g a b`
def raw_appN : RawExp :=
  .callN gId .nat (.cons (.var aId .nat) (.cons (.var bId .nat) .nil))
def prod_appN_ok : ExprData :=
  .appN gId (.cons (.atom aId) (.cons (.atom bId) .nil))
theorem V_appN_ok_decide : render_exp raw_appN = prod_appN_ok := by decide
def prod_appN_swap : ExprData :=
  .appN gId (.cons (.atom bId) (.cons (.atom aId) .nil))     -- args swapped
theorem V_appN_swap_kill : ¬ (render_exp raw_appN = prod_appN_swap) := by decide
def prod_appN_drop : ExprData :=
  .appN gId (.cons (.atom aId) .nil)                         -- one arg dropped
theorem V_appN_drop_kill : ¬ (render_exp raw_appN = prod_appN_drop) := by decide

/- ── §7 Q1 demonstration: the PRODUCTION nat-returning `expr_eq` idiom over a
   Match arm-list reduces under `decide` (the one novel equality shape W7b
   lands). Mirrors tactus-core's tag+projection+if-chain discipline: match the
   FIRST arg, read the second through non-recursive tag/projection accessors,
   recurse via a dedicated `arms_eq`. Returns nat (1/0). Here for tree_head's
   arm list, closing correct=1 and the swapped-value mutation=0. -/

def marm_ctor  : MatchArm → Nat      | .arm c _ _  => c
def marm_binds : MatchArm → List Nat | .arm _ bs _ => bs
def marm_body  : MatchArm → ExprData | .arm _ _ b  => b
def al_isNil : ArmList → Bool | .nil => true | .cons _ _ => false
def al_hd : ArmList → MatchArm | .cons h _ => h | .nil => .arm 0 [] (.lit 0)
def al_tl : ArmList → ArmList  | .cons _ t => t | .nil => .nil
-- list-Nat equality via the Init `DecidableEq (List Nat)` as a 1/0 nat
def binds_eq (a b : List Nat) : Nat := if a = b then 1 else 0

def arm_eq (a b : MatchArm) : Nat :=
  if marm_ctor a == marm_ctor b then
    if binds_eq (marm_binds a) (marm_binds b) == 1 then
      -- bodies compared by the derived structural `=` (stands in for the full
      -- recursive expr_eq — the arm-list recursion is the point here)
      (if marm_body a = marm_body b then 1 else 0)
    else 0
  else 0

def arms_eq : ArmList → ArmList → Nat
  | .nil,       .nil       => 1
  | .nil,       .cons _ _  => 0
  | .cons _ _,  .nil       => 0
  | .cons h1 t1, b         => if arm_eq h1 (al_hd b) == 1 then arms_eq t1 (al_tl b) else 0

def th_arms_ok : ArmList :=
  (.cons (.arm leafCtor [vId] (.atom vId)) (.cons (.arm nodeCtor [lId, rId] (.lit 0)) .nil))
def th_arms_mut : ArmList :=
  (.cons (.arm leafCtor [vId] (.lit 0)) (.cons (.arm nodeCtor [lId, rId] (.lit 0)) .nil))

theorem Q1_arms_eq_closes : arms_eq th_arms_ok th_arms_ok = 1 := by decide
theorem Q1_arms_eq_kills  : arms_eq th_arms_ok th_arms_mut = 0 := by decide

-- ── axiom hygiene: the whole mechanic is pure kernel computation ─────────────
#print axioms render_exp
#print axioms render_def
#print axioms render_dt
#print axioms arms_eq
#print axioms A_tri_ok_decide
#print axioms B_th_ok_decide
#print axioms B_st_ok_decide
#print axioms C_dt_ok_decide
#print axioms C_height_ok_decide
#print axioms A_tri_nocast_kill
#print axioms B_th_binder_kill
#print axioms Q1_arms_eq_kills

#eval "W7a probe: all defs-layer bridges elaborated (see rc); axioms printed above."
