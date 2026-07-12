/- W0 pre-probe P6: a REAL emitted goal, bridged. Source: /tmp/fcx_scratch.lean
   (find_cancellation_exec island, tgt, M6.1-era), theorem
   _tactus_assert_runtime.find_cancellation_exec_at_runtime_103_16_2 — the goal
   copied VERBATIM below (∀-closed over the signature binders, span comments
   kept). Ambient decls are trimmed replicas of the island's spec world.
   Real shapes exercised: Tactus.Ref decoration + type ascription, View
   instance dispatch, `let tmp__N` bindings inside the Prop, usize_hi, mixed
   Nat comparisons incl. the 0 ≤ overflow guard, opaque type constructors
   (Vec/Seq as axioms), spec-fn symbols incl. a WF-compiled recursive one
   (find_cancellation_from — NEVER evaluated by the bridge, only named). -/

-- ── trimmed spec world (verbatim shapes from the island file) ──────────────
structure Tactus.Ref (A : Type) where mk :: deref : A

class view.View (Self : Type) (V : outParam Type) where
  view : Tactus.Ref Self → V
class marker.Tuple (Self : Type) where
class ops.function.FnOnce (Self : Type) (Args : Type) (Output : outParam Type) extends marker.Tuple Args where
class ops.function.FnMut (Self : Type) (Args : Type) (Output : outParam Type) extends ops.function.FnOnce Self Args Output, marker.Tuple Args where
class ops.function.Fn (Self : Type) (Args : Type) (Output : outParam Type) extends ops.function.FnMut Self Args Output, marker.Tuple Args where
class alloc.Allocator (Self : Type) where
noncomputable instance {A : Type} : marker.Tuple A where
noncomputable instance {A : Type} {B : Type} [marker.Tuple A] : ops.function.FnOnce (A → B) A B where
noncomputable instance {A : Type} {B : Type} [marker.Tuple A] : ops.function.FnMut (A → B) A B where
noncomputable instance {A : Type} {B : Type} [marker.Tuple A] : ops.function.Fn (A → B) A B where

axiom alloc.Global : Type
noncomputable instance : alloc.Allocator alloc.Global where
axiom vec.Vec : Type → Type → Type
axiom seq.Seq : Type → Type
@[instance] axiom seq.Seq.instInhabited (A : Type) : Inhabited (seq.Seq A)

inductive symbol.Symbol where
  | Gen (val0 : Nat)
  | Inv (val0 : Nat)
  deriving Inhabited
inductive runtime.RuntimeSymbol where
  | Gen (val0 : Nat)
  | Inv (val0 : Nat)
  deriving Inhabited

axiom seq.Seq.len (A : Type) (self : seq.Seq A) : Nat
axiom seq.Seq.index (A : Type) [Nonempty A] (self : seq.Seq A) (i : Int) : A
axiom seq.Seq.new (A : Type) (impl_1 : Type) {_tactus_assoc_impl_1_Fn_Output : Type} [ops.function.Fn impl_1 Int _tactus_assoc_impl_1_Fn_Output] [Nonempty A] (len : Nat) (f : impl_1) : seq.Seq A
axiom std_specs.vec.spec_vec_len (T : Type) (A : Type) [alloc.Allocator A] (v : Tactus.Ref (vec.Vec T A)) : Nat
axiom Vec.View.impl.view (T : Type) (A : Type) [alloc.Allocator A] [Nonempty T] (self : Tactus.Ref (vec.Vec T A)) : seq.Seq T
noncomputable instance {T : Type} {A : Type} [alloc.Allocator A] [Nonempty T] : view.View (vec.Vec T A) (seq.Seq T) where
  view := fun self => Vec.View.impl.view T A self

noncomputable def symbol.inverse_symbol (s : symbol.Symbol) : symbol.Symbol :=
  match s with | symbol.Symbol.Gen i => symbol.Symbol.Inv i | symbol.Symbol.Inv i => symbol.Symbol.Gen i
noncomputable def symbol.is_inverse_pair (s1 : symbol.Symbol) (s2 : symbol.Symbol) : Prop :=
  s2 = symbol.inverse_symbol s1
attribute [local instance] Classical.propDecidable in
noncomputable def reduction.find_cancellation_from (w : seq.Seq symbol.Symbol) (start : Nat) : Nat :=
  if start ≥ seq.Seq.len symbol.Symbol w - 1 then seq.Seq.len symbol.Symbol w else if symbol.is_inverse_pair (seq.Seq.index symbol.Symbol w start) (seq.Seq.index symbol.Symbol w (start + 1)) then start else reduction.find_cancellation_from w (start + 1)
termination_by seq.Seq.len symbol.Symbol w - start
decreasing_by all_goals (first | omega | decreasing_tactic)
noncomputable def runtime.runtime_symbol_view (s : runtime.RuntimeSymbol) : symbol.Symbol :=
  match s with | runtime.RuntimeSymbol.Gen i => symbol.Symbol.Gen i | runtime.RuntimeSymbol.Inv i => symbol.Symbol.Inv i
noncomputable def runtime.runtime_word_view (w : seq.Seq runtime.RuntimeSymbol) : seq.Seq symbol.Symbol :=
  seq.Seq.new symbol.Symbol (Int → symbol.Symbol) (seq.Seq.len runtime.RuntimeSymbol w) (fun (i : Int) => runtime.runtime_symbol_view (seq.Seq.index runtime.RuntimeSymbol w i))

axiom arch_word_bits : Nat
noncomputable def usize_hi : Nat := 2 ^ arch_word_bits

-- ── the RENDERED goal, verbatim from the island theorem (∀-closed) ─────────
noncomputable def rendered6 : Prop :=
  ∀ (w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global)),
    seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1 →
    (0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__1 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    /- @rust:src/runtime.rs:102:8 -/ tmp__1 ≤ 1 → /- @rust:src/runtime.rs:103:16 -/ reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) 0 = seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))))

-- ── typed goal language (sort-indexed; probe-scale) ────────────────────────
inductive Srt where | nat | w | seqRS | seqSym

structure SymEnv where
  W : Type
  SeqRS : Type
  SeqSym : Type
  vlen  : W → Nat
  vview : W → SeqRS
  rwv   : SeqRS → SeqSym
  fcf   : SeqSym → Nat → Nat
  lenRS : SeqRS → Nat
  uhi   : Nat

@[reducible] def interpS (env : SymEnv) : Srt → Type
  | .nat => Nat | .w => env.W | .seqRS => env.SeqRS | .seqSym => env.SeqSym

inductive TExpr : Srt → Type where
  | natLit : Nat → TExpr .nat
  | usizeHi : TExpr .nat
  | sub : TExpr .nat → TExpr .nat → TExpr .nat
  | tmp : Nat → TExpr .nat                 -- de Bruijn into the let-env
  | wvar : TExpr .w                         -- the ∀-bound signature binder
  | vlen : TExpr .w → TExpr .nat
  | vview : TExpr .w → TExpr .seqRS
  | rwv : TExpr .seqRS → TExpr .seqSym
  | fcf : TExpr .seqSym → TExpr .nat → TExpr .nat
  | lenRS : TExpr .seqRS → TExpr .nat

inductive TGoal where
  | gimp : TGoal → TGoal → TGoal
  | gand : TGoal → TGoal → TGoal
  | glet : TExpr .nat → TGoal → TGoal
  | gle : TExpr .nat → TExpr .nat → TGoal
  | glt : TExpr .nat → TExpr .nat → TGoal
  | geq : TExpr .nat → TExpr .nat → TGoal

def edenote (env : SymEnv) (wv : env.W) (lets : List Nat) : {s : Srt} → TExpr s → interpS env s
  | _, .natLit n => n
  | _, .usizeHi => env.uhi
  | _, .sub a b => edenote env wv lets a - edenote env wv lets b
  | _, .tmp i => lets.getD i 0
  | _, .wvar => wv
  | _, .vlen e => env.vlen (edenote env wv lets e)
  | _, .vview e => env.vview (edenote env wv lets e)
  | _, .rwv e => env.rwv (edenote env wv lets e)
  | _, .fcf e n => env.fcf (edenote env wv lets e) (edenote env wv lets n)
  | _, .lenRS e => env.lenRS (edenote env wv lets e)

def gdenote (env : SymEnv) (wv : env.W) (lets : List Nat) : TGoal → Prop
  | .gimp h g => gdenote env wv lets h → gdenote env wv lets g
  | .gand a b => gdenote env wv lets a ∧ gdenote env wv lets b
  | .glet e g => let v := edenote env wv lets e; gdenote env wv (v :: lets) g
  | .gle a b => edenote env wv lets a ≤ edenote env wv lets b
  | .glt a b => edenote env wv lets a < edenote env wv lets b
  | .geq a b => edenote env wv lets a = edenote env wv lets b

def gdenoteClosed (env : SymEnv) (g : TGoal) : Prop := ∀ wv : env.W, gdenote env wv [] g

-- ── the per-crate environment literal (what the emitter would generate) ────
noncomputable def crateEnv : SymEnv where
  W := Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global)
  SeqRS := seq.Seq runtime.RuntimeSymbol
  SeqSym := seq.Seq symbol.Symbol
  vlen := fun w => std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w
  vview := fun w => (view.View.view w : seq.Seq runtime.RuntimeSymbol)
  rwv := fun s => runtime.runtime_word_view s
  fcf := fun s n => reduction.find_cancellation_from s n
  lenRS := fun s => seq.Seq.len runtime.RuntimeSymbol s
  uhi := usize_hi

-- ── the goal as reference data (what refWp would output) ───────────────────
def gAssert : TGoal :=
  .gimp (.glt (.lenRS (.vview .wvar)) (.sub .usizeHi (.natLit 1)))
    (.gimp (.gand (.gle (.natLit 0) (.vlen .wvar)) (.glt (.vlen .wvar) .usizeHi))
      (.glet (.vlen .wvar)
        (.gimp (.gle (.tmp 0) (.natLit 1))
          (.geq (.fcf (.rwv (.vview .wvar)) (.natLit 0)) (.lenRS (.vview .wvar))))))

-- ── THE BRIDGE ─────────────────────────────────────────────────────────────
example : gdenoteClosed crateEnv gAssert = rendered6 := by rfl
