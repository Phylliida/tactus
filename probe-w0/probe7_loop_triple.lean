/- W0 pre-probe P7 (the LAST W0 item): a real LOOP-MAINTAIN goal bridges.
   Source: bootstrap-fixture out/lib/sum_to.lean, theorem
   _tactus_loop_invariant_sum_to_at_lib_113_13_9 — the cast-bearing invariant
   `acc as nat == tri(i as nat)` re-established after the loop step. Goal
   copied VERBATIM (binder telescope → ∀/→ chain, defeq-identical; span
   comments kept). New shapes over P6: hypothesis binders in the telescope
   (CtxFrame architecture — the loop-state ∀ is signature binders, not nested
   quantifiers), Int-typed lets incl. LET-SHADOWING of binders (`let i := i+1`
   — the SSA-via-shadowing idiom), the decrease-snapshot let, duplicated
   overflow guards, `Int.toNat` coercion sites, and a WF-emitted recursive
   spec fn (lib.tri) as an opaque symbol. -/

-- ── ambient decls (verbatim from the emitted island) ───────────────────────
noncomputable def lib.tri (n : Nat) : Nat :=
  if n = 0 then 0 else n + lib.tri (Int.toNat (n - 1))
termination_by n
decreasing_by all_goals (first | omega | decreasing_tactic)

-- ── the RENDERED goal, verbatim (telescope written as ∀/→ chain) ───────────
noncomputable def rendered7 : Prop :=
  ∀ (n : Int), (0 ≤ n ∧ n < 18446744073709551616) → (n ≤ 1000) →
  ∀ (i : Int), (0 ≤ i ∧ i < 18446744073709551616) →
  ∀ (acc : Int), (0 ≤ acc ∧ acc < 18446744073709551616) →
    (/- @rust:lib.rs:111:13 -/ i ≤ n) →
    (/- @rust:lib.rs:112:13 -/ n ≤ 1000) →
    (/- @rust:lib.rs:113:13 -/ Int.toNat acc = lib.tri (Int.toNat i)) →
    (/- @rust:lib.rs:114:13 -/ acc ≤ 1000 * 1000) →
    (/- @rust:lib.rs:109:11 -/ i < n) →
    (let _tactus_d_old_0_0 := n - i;
    0 ≤ i + 1 ∧ i + 1 < 18446744073709551616 → 0 ≤ i + 1 ∧ i + 1 < 18446744073709551616 → (let i := i + 1;
    0 ≤ acc + i ∧ acc + i < 18446744073709551616 → 0 ≤ acc + i ∧ acc + i < 18446744073709551616 → (let acc := acc + i;
    /- @rust:lib.rs:113:13 -/ Int.toNat acc = lib.tri (Int.toNat i))))

-- ── two-sorted goal language (Int exec side + Nat spec side, per §11.1) ────
inductive TeI where
  | ivar : Nat → TeI            -- de Bruijn: binders AND lets uniformly
  | ilit : Int → TeI
  | iadd : TeI → TeI → TeI
  | isub : TeI → TeI → TeI
  | imul : TeI → TeI → TeI

inductive TeN where
  | toNat : TeI → TeN           -- the Int.toNat materialization site
  | tri : TeN → TeN             -- opaque spec-fn symbol (env-bound in general)

inductive TG where
  | gforallI : TG → TG          -- ∀ (x : Int), …   (telescope binder)
  | ghyp : TG → TG → TG         -- hypothesis binder (h : P) → …
  | glet : TeI → TG → TG        -- Int let (incl. shadowing)
  | gand : TG → TG → TG
  | gle : TeI → TeI → TG
  | glt : TeI → TeI → TG
  | geqN : TeN → TeN → TG

def edI (env : List Int) : TeI → Int
  | .ivar k => env.getD k 0
  | .ilit m => m
  | .iadd a b => edI env a + edI env b
  | .isub a b => edI env a - edI env b
  | .imul a b => edI env a * edI env b

noncomputable def edN (env : List Int) : TeN → Nat
  | .toNat e => Int.toNat (edI env e)
  | .tri e => lib.tri (edN env e)

noncomputable def gd (env : List Int) : TG → Prop
  | .gforallI g => ∀ x : Int, gd (x :: env) g
  | .ghyp h g => gd env h → gd env g
  | .glet e g => let v := edI env e; gd (v :: env) g
  | .gand a b => gd env a ∧ gd env b
  | .gle a b => edI env a ≤ edI env b
  | .glt a b => edI env a < edI env b
  | .geqN a b => edN env a = edN env b

-- ── the goal as reference data (what refWp outputs for maintain/inv-3) ─────
-- de Bruijn env at each depth (head = newest):
--   [n] → [i,n] → [acc,i,n] → +d_old [d,acc,i,n] → +i' [i',d,acc,i,n]
--   → +acc' [acc',i',d,acc,i,n]
def B : TeI := .ilit 18446744073709551616

-- shared piece: every Int binder gets the same u64 bound hyp on (.ivar 0)
def boundHyp : TG := .gand (.gle (.ilit 0) (.ivar 0)) (.glt (.ivar 0) B)

-- innermost out. de Bruijn env at each layer (head = newest):
--   binders: [n] → [i,n] → [acc,i,n]
--   lets:    +d_old [d,acc,i,n] → +i' [i',d,acc,i,n] → +acc' [acc',i',d,acc,i,n]
def inner : TG := .geqN (.toNat (.ivar 0)) (.tri (.toNat (.ivar 1)))      -- acc'=0, i'=1
def stepAcc : TG := .glet (.iadd (.ivar 2) (.ivar 0)) inner               -- SHADOW acc := acc + i'
def accGuard : TG := .gand (.gle (.ilit 0) (.iadd (.ivar 2) (.ivar 0))) (.glt (.iadd (.ivar 2) (.ivar 0)) B)
def afterI : TG := .ghyp accGuard (.ghyp accGuard stepAcc)                -- duplicated overflow guard
def stepI : TG := .glet (.iadd (.ivar 2) (.ilit 1)) afterI                -- SHADOW i := i + 1
def iGuard : TG := .gand (.gle (.ilit 0) (.iadd (.ivar 2) (.ilit 1))) (.glt (.iadd (.ivar 2) (.ilit 1)) B)
def afterD : TG := .ghyp iGuard (.ghyp iGuard stepI)
def body : TG := .glet (.isub (.ivar 2) (.ivar 1)) afterD                 -- d_old snapshot := n - i

def gMaintain3 : TG :=
  .gforallI (.ghyp boundHyp (.ghyp (.gle (.ivar 0) (.ilit 1000))          -- n, h_n_bound, h_req0
   (.gforallI (.ghyp boundHyp                                             -- i, _h_ctx_0
    (.gforallI (.ghyp boundHyp                                            -- acc, _h_ctx_1
     (.ghyp (.gle (.ivar 1) (.ivar 2))                                    -- i ≤ n
      (.ghyp (.gle (.ivar 2) (.ilit 1000))                                -- n ≤ 1000
       (.ghyp (.geqN (.toNat (.ivar 0)) (.tri (.toNat (.ivar 1))))        -- inv-3
        (.ghyp (.gle (.ivar 0) (.imul (.ilit 1000) (.ilit 1000)))         -- inv-4
         (.ghyp (.glt (.ivar 1) (.ivar 2)) body)))))))))))                -- i < n

-- ── THE BRIDGE ─────────────────────────────────────────────────────────────
example : gd [] gMaintain3 = rendered7 := by rfl
