import TactusPrelude
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
namespace lib
set_option autoImplicit false
class view.View (Self : Type) (V : outParam Type) where
  view : Tactus.Ref Self → V
class view.DeepView (Self : Type) (V : outParam Type) where
  deep_view : Tactus.Ref Self → V
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
@[instance] axiom alloc.Global.instInhabited : Inhabited alloc.Global
axiom vec.Vec : Type → Type → Type
@[instance] axiom vec.Vec.instInhabited (T : Type) (A : Type) : Inhabited (vec.Vec T A)
axiom seq.Seq : Type → Type
@[instance] axiom seq.Seq.instInhabited (A : Type) : Inhabited (seq.Seq A)
structure set.Set (A : Type) where
  set : A → Prop
  deriving Inhabited
@[simp] noncomputable def set.Set.height {A : Type} (_ : set.Set A) : Nat :=
  1
inductive symbol.Symbol where
  | Gen (val0 : Nat)
  | Inv (val0 : Nat)
  deriving Inhabited
@[simp] noncomputable def symbol.Symbol.isGen (x : symbol.Symbol) : Prop :=
  match x with | symbol.Symbol.Gen _ => True | _ => False
@[simp] noncomputable def symbol.Symbol.isInv (x : symbol.Symbol) : Prop :=
  match x with | symbol.Symbol.Inv _ => True | _ => False
@[simp] noncomputable def symbol.Symbol.Gen_val0 (x : symbol.Symbol) : Nat :=
  match x with | symbol.Symbol.Gen val0 => val0 | _ => default
@[simp] noncomputable def symbol.Symbol.Inv_val0 (x : symbol.Symbol) : Nat :=
  match x with | symbol.Symbol.Inv val0 => val0 | _ => default
@[simp] noncomputable def symbol.Symbol.height (_ : symbol.Symbol) : Nat :=
  1
inductive runtime.RuntimeSymbol where
  | Gen (val0 : Nat)
  | Inv (val0 : Nat)
  deriving Inhabited
@[simp] noncomputable def runtime.RuntimeSymbol.isGen (x : runtime.RuntimeSymbol) : Prop :=
  match x with | runtime.RuntimeSymbol.Gen _ => True | _ => False
@[simp] noncomputable def runtime.RuntimeSymbol.isInv (x : runtime.RuntimeSymbol) : Prop :=
  match x with | runtime.RuntimeSymbol.Inv _ => True | _ => False
@[simp] noncomputable def runtime.RuntimeSymbol.Gen_val0 (x : runtime.RuntimeSymbol) : Nat :=
  match x with | runtime.RuntimeSymbol.Gen val0 => val0 | _ => default
@[simp] noncomputable def runtime.RuntimeSymbol.Inv_val0 (x : runtime.RuntimeSymbol) : Nat :=
  match x with | runtime.RuntimeSymbol.Inv val0 => val0 | _ => default
@[simp] noncomputable def runtime.RuntimeSymbol.height (_ : runtime.RuntimeSymbol) : Nat :=
  1
axiom std_specs.vec.spec_vec_len (T : Type) (A : Type) [alloc.Allocator A] (v : Tactus.Ref (vec.Vec T A)) : Nat
noncomputable def std_specs.vec.vec_clone_trigger (T : Type) (A : Type) [alloc.Allocator A] (v1 : vec.Vec T A) (v2 : vec.Vec T A) : Prop :=
  True
axiom seq.Seq.new (A : Type) (impl_1 : Type) {_tactus_assoc_impl_1_Fn_Output : Type} [ops.function.Fn impl_1 Int _tactus_assoc_impl_1_Fn_Output] [Nonempty A] (len : Nat) (f : impl_1) : seq.Seq A
noncomputable def array.array_view (T : Type) (N : Nat) [Nonempty T] (a : Vector T N) : seq.Seq T :=
  seq.Seq.new T (Int → T) N (fun (i : Int) => Tactus.index a i)
noncomputable def Vector.View.impl.view (T : Type) (N : Nat) [Nonempty T] (self : Tactus.Ref (Vector T N)) : seq.Seq T :=
  array.array_view T N self.deref
axiom seq.Seq.empty (A : Type) [Nonempty A] : seq.Seq A
axiom seq.Seq.len (A : Type) (self : seq.Seq A) : Nat
axiom seq.Seq.index (A : Type) [Nonempty A] (self : seq.Seq A) (i : Int) : A
axiom seq.Seq.push (A : Type) [Nonempty A] (self : seq.Seq A) (a : A) : seq.Seq A
axiom seq.Seq.update (A : Type) [Nonempty A] (self : seq.Seq A) (i : Int) (a : A) : seq.Seq A
axiom seq.Seq.subrange (A : Type) [Nonempty A] (self : seq.Seq A) (start_inclusive : Int) (end_exclusive : Int) : seq.Seq A
axiom seq.Seq.add (A : Type) [Nonempty A] (self : seq.Seq A) (rhs : seq.Seq A) : seq.Seq A
axiom set.Set.empty (A : Type) [Nonempty A] : set.Set A
axiom set.Set.contains (A : Type) (self : set.Set A) (a : A) : Prop
noncomputable def set.Set.subset_of (A : Type) (self : set.Set A) (s2 : set.Set A) : Prop :=
  ∀ (a : A), set.Set.contains A self a → set.Set.contains A s2 a
axiom set.Set.insert (A : Type) [Nonempty A] (self : set.Set A) (a : A) : set.Set A
axiom set.Set.remove (A : Type) [Nonempty A] (self : set.Set A) (a : A) : set.Set A
axiom Set.complement (A : Type) [Nonempty A] (self : set.Set A) : set.Set A
axiom Set.finite (A : Type) (self : set.Set A) : Prop
axiom Vec.View.impl.view (T : Type) (A : Type) [alloc.Allocator A] [Nonempty T] (self : Tactus.Ref (vec.Vec T A)) : seq.Seq T
noncomputable instance {T : Type} {N : Nat} [Nonempty T] : view.View (Vector T N) (seq.Seq T) where
  view := fun (self : _) => array.array_view T N self.deref
noncomputable instance {T : Type} {N : Nat} {_tactus_assoc_T_DeepView_V : Type} [view.DeepView T _tactus_assoc_T_DeepView_V] [Nonempty T] [Nonempty _tactus_assoc_T_DeepView_V] : view.DeepView (Vector T N) (seq.Seq _tactus_assoc_T_DeepView_V) where
  deep_view := fun (self : _) => let v := view.View.view ((self : Tactus.Ref (Vector T N)));
    seq.Seq.new _tactus_assoc_T_DeepView_V (Int → _tactus_assoc_T_DeepView_V) (seq.Seq.len T v) (fun (i : Int) => view.DeepView.deep_view (Tactus.Ref.mk (seq.Seq.index T v i)))
noncomputable instance {A : Type} {_tactus_assoc_A_View_V : Type} [view.View A _tactus_assoc_A_View_V] : view.View (Tactus.Ref A) _tactus_assoc_A_View_V where
  view := fun (self : _) => view.View.view (Tactus.Ref.mk self.deref.deref)
noncomputable instance {A : Type} {_tactus_assoc_A_DeepView_V : Type} [view.DeepView A _tactus_assoc_A_DeepView_V] : view.DeepView (Tactus.Ref A) _tactus_assoc_A_DeepView_V where
  deep_view := fun (self : _) => view.DeepView.deep_view (Tactus.Ref.mk self.deref.deref)
noncomputable instance {A : Type} {_tactus_assoc_A_View_V : Type} [view.View A _tactus_assoc_A_View_V] : view.View (Tactus.Box A) _tactus_assoc_A_View_V where
  view := fun (self : _) => view.View.view (Tactus.Ref.mk self.deref.deref)
noncomputable instance {A : Type} {_tactus_assoc_A_DeepView_V : Type} [view.DeepView A _tactus_assoc_A_DeepView_V] : view.DeepView (Tactus.Box A) _tactus_assoc_A_DeepView_V where
  deep_view := fun (self : _) => view.DeepView.deep_view (Tactus.Ref.mk self.deref.deref)
noncomputable instance {A : Type} {_tactus_assoc_A_View_V : Type} [view.View A _tactus_assoc_A_View_V] : view.View (Tactus.Rc A) _tactus_assoc_A_View_V where
  view := fun (self : _) => view.View.view (Tactus.Ref.mk self.deref.deref)
noncomputable instance {A : Type} {_tactus_assoc_A_DeepView_V : Type} [view.DeepView A _tactus_assoc_A_DeepView_V] : view.DeepView (Tactus.Rc A) _tactus_assoc_A_DeepView_V where
  deep_view := fun (self : _) => view.DeepView.deep_view (Tactus.Ref.mk self.deref.deref)
noncomputable instance {A : Type} {_tactus_assoc_A_View_V : Type} [view.View A _tactus_assoc_A_View_V] : view.View (Tactus.Arc A) _tactus_assoc_A_View_V where
  view := fun (self : _) => view.View.view (Tactus.Ref.mk self.deref.deref)
noncomputable instance {A : Type} {_tactus_assoc_A_DeepView_V : Type} [view.DeepView A _tactus_assoc_A_DeepView_V] : view.DeepView (Tactus.Arc A) _tactus_assoc_A_DeepView_V where
  deep_view := fun (self : _) => view.DeepView.deep_view (Tactus.Ref.mk self.deref.deref)
noncomputable instance {T : Type} {A : Type} [alloc.Allocator A] [Nonempty T] : view.View (vec.Vec T A) (seq.Seq T) where
  view := fun (self : _) => Vec.View.impl.view T A self
noncomputable def Vec.DeepView.impl.deep_view (T : Type) (A : Type) {_tactus_assoc_T_DeepView_V : Type} [view.DeepView T _tactus_assoc_T_DeepView_V] [alloc.Allocator A] [Nonempty T] [Nonempty _tactus_assoc_T_DeepView_V] (self : Tactus.Ref (vec.Vec T A)) : seq.Seq _tactus_assoc_T_DeepView_V :=
  let v := view.View.view self;
    seq.Seq.new _tactus_assoc_T_DeepView_V (Int → _tactus_assoc_T_DeepView_V) (seq.Seq.len T v) (fun (i : Int) => view.DeepView.deep_view (Tactus.Ref.mk (seq.Seq.index T v i)))
noncomputable def symbol.inverse_symbol (s : symbol.Symbol) : symbol.Symbol :=
  match s with | symbol.Symbol.Gen i => symbol.Symbol.Inv i | symbol.Symbol.Inv i => symbol.Symbol.Gen i
noncomputable def symbol.is_inverse_pair (s1 : symbol.Symbol) (s2 : symbol.Symbol) : Prop :=
  s2 = symbol.inverse_symbol s1
noncomputable def reduction.find_cancellation_from (w : seq.Seq symbol.Symbol) (start : Nat) : Nat :=
  if start ≥ seq.Seq.len symbol.Symbol w - 1 then seq.Seq.len symbol.Symbol w else if symbol.is_inverse_pair (seq.Seq.index symbol.Symbol w start) (seq.Seq.index symbol.Symbol w (start + 1)) then start else reduction.find_cancellation_from w (start + 1)
termination_by seq.Seq.len symbol.Symbol w - start
decreasing_by all_goals (first | omega | (apply Nat.mod_lt <;> omega) | decreasing_tactic)
noncomputable def runtime.runtime_symbol_view (s : runtime.RuntimeSymbol) : symbol.Symbol :=
  match s with | runtime.RuntimeSymbol.Gen i => symbol.Symbol.Gen i | runtime.RuntimeSymbol.Inv i => symbol.Symbol.Inv i
noncomputable def runtime.runtime_word_view (w : seq.Seq runtime.RuntimeSymbol) : seq.Seq symbol.Symbol :=
  seq.Seq.new symbol.Symbol (Int → symbol.Symbol) (seq.Seq.len runtime.RuntimeSymbol w) (fun (i : Int) => runtime.runtime_symbol_view (seq.Seq.index runtime.RuntimeSymbol w i))
noncomputable instance {T : Type} {A : Type} {_tactus_assoc_T_DeepView_V : Type} [view.DeepView T _tactus_assoc_T_DeepView_V] [alloc.Allocator A] [Nonempty T] [Nonempty _tactus_assoc_T_DeepView_V] : view.DeepView (vec.Vec T A) (seq.Seq _tactus_assoc_T_DeepView_V) where
  deep_view := fun (self : _) => let v := view.View.view self;
    seq.Seq.new _tactus_assoc_T_DeepView_V (Int → _tactus_assoc_T_DeepView_V) (seq.Seq.len T v) (fun (i : Int) => view.DeepView.deep_view (Tactus.Ref.mk (seq.Seq.index T v i)))
noncomputable instance : view.View Unit Unit where
  view := fun (self : _) => self.deref
noncomputable instance : view.DeepView Unit Unit where
  deep_view := fun (self : _) => self.deref
noncomputable instance : view.View Prop Prop where
  view := fun (self : _) => self.deref
noncomputable instance : view.DeepView Prop Prop where
  deep_view := fun (self : _) => self.deref
noncomputable instance : view.View Nat Nat where
  view := fun (self : _) => self.deref
noncomputable instance : view.DeepView Nat Nat where
  deep_view := fun (self : _) => self.deref
noncomputable instance {A0 : Type} {_tactus_assoc_A0_View_V : Type} [view.View A0 _tactus_assoc_A0_View_V] : view.View A0 _tactus_assoc_A0_View_V where
  view := fun (self : _) => (view.View.view (Tactus.Ref.mk self.deref))
noncomputable instance {A0 : Type} {_tactus_assoc_A0_DeepView_V : Type} [view.DeepView A0 _tactus_assoc_A0_DeepView_V] : view.DeepView A0 _tactus_assoc_A0_DeepView_V where
  deep_view := fun (self : _) => (view.DeepView.deep_view (Tactus.Ref.mk self.deref))
noncomputable instance {A0 : Type} {A1 : Type} {_tactus_assoc_A0_View_V : Type} {_tactus_assoc_A1_View_V : Type} [view.View A0 _tactus_assoc_A0_View_V] [view.View A1 _tactus_assoc_A1_View_V] : view.View (A0 × A1) (_tactus_assoc_A0_View_V × _tactus_assoc_A1_View_V) where
  view := fun (self : _) => (view.View.view (Tactus.Ref.mk self.deref.1), view.View.view (Tactus.Ref.mk self.deref.2))
noncomputable instance {A0 : Type} {A1 : Type} {_tactus_assoc_A0_DeepView_V : Type} {_tactus_assoc_A1_DeepView_V : Type} [view.DeepView A0 _tactus_assoc_A0_DeepView_V] [view.DeepView A1 _tactus_assoc_A1_DeepView_V] : view.DeepView (A0 × A1) (_tactus_assoc_A0_DeepView_V × _tactus_assoc_A1_DeepView_V) where
  deep_view := fun (self : _) => (view.DeepView.deep_view (Tactus.Ref.mk self.deref.1), view.DeepView.deep_view (Tactus.Ref.mk self.deref.2))
noncomputable instance {A0 : Type} {A1 : Type} {A2 : Type} {_tactus_assoc_A0_View_V : Type} {_tactus_assoc_A1_View_V : Type} {_tactus_assoc_A2_View_V : Type} [view.View A0 _tactus_assoc_A0_View_V] [view.View A1 _tactus_assoc_A1_View_V] [view.View A2 _tactus_assoc_A2_View_V] : view.View (A0 × A1 × A2) (_tactus_assoc_A0_View_V × _tactus_assoc_A1_View_V × _tactus_assoc_A2_View_V) where
  view := fun (self : _) => (view.View.view (Tactus.Ref.mk self.deref.1), view.View.view (Tactus.Ref.mk self.deref.2.1), view.View.view (Tactus.Ref.mk self.deref.2.2))
noncomputable instance {A0 : Type} {A1 : Type} {A2 : Type} {_tactus_assoc_A0_DeepView_V : Type} {_tactus_assoc_A1_DeepView_V : Type} {_tactus_assoc_A2_DeepView_V : Type} [view.DeepView A0 _tactus_assoc_A0_DeepView_V] [view.DeepView A1 _tactus_assoc_A1_DeepView_V] [view.DeepView A2 _tactus_assoc_A2_DeepView_V] : view.DeepView (A0 × A1 × A2) (_tactus_assoc_A0_DeepView_V × _tactus_assoc_A1_DeepView_V × _tactus_assoc_A2_DeepView_V) where
  deep_view := fun (self : _) => (view.DeepView.deep_view (Tactus.Ref.mk self.deref.1), view.DeepView.deep_view (Tactus.Ref.mk self.deref.2.1), view.DeepView.deep_view (Tactus.Ref.mk self.deref.2.2))
noncomputable instance {A0 : Type} {A1 : Type} {A2 : Type} {A3 : Type} {_tactus_assoc_A0_View_V : Type} {_tactus_assoc_A1_View_V : Type} {_tactus_assoc_A2_View_V : Type} {_tactus_assoc_A3_View_V : Type} [view.View A0 _tactus_assoc_A0_View_V] [view.View A1 _tactus_assoc_A1_View_V] [view.View A2 _tactus_assoc_A2_View_V] [view.View A3 _tactus_assoc_A3_View_V] : view.View (A0 × A1 × A2 × A3) (_tactus_assoc_A0_View_V × _tactus_assoc_A1_View_V × _tactus_assoc_A2_View_V × _tactus_assoc_A3_View_V) where
  view := fun (self : _) => (view.View.view (Tactus.Ref.mk self.deref.1), view.View.view (Tactus.Ref.mk self.deref.2.1), view.View.view (Tactus.Ref.mk self.deref.2.2.1), view.View.view (Tactus.Ref.mk self.deref.2.2.2))
noncomputable instance {A0 : Type} {A1 : Type} {A2 : Type} {A3 : Type} {_tactus_assoc_A0_DeepView_V : Type} {_tactus_assoc_A1_DeepView_V : Type} {_tactus_assoc_A2_DeepView_V : Type} {_tactus_assoc_A3_DeepView_V : Type} [view.DeepView A0 _tactus_assoc_A0_DeepView_V] [view.DeepView A1 _tactus_assoc_A1_DeepView_V] [view.DeepView A2 _tactus_assoc_A2_DeepView_V] [view.DeepView A3 _tactus_assoc_A3_DeepView_V] : view.DeepView (A0 × A1 × A2 × A3) (_tactus_assoc_A0_DeepView_V × _tactus_assoc_A1_DeepView_V × _tactus_assoc_A2_DeepView_V × _tactus_assoc_A3_DeepView_V) where
  deep_view := fun (self : _) => (view.DeepView.deep_view (Tactus.Ref.mk self.deref.1), view.DeepView.deep_view (Tactus.Ref.mk self.deref.2.1), view.DeepView.deep_view (Tactus.Ref.mk self.deref.2.2.1), view.DeepView.deep_view (Tactus.Ref.mk self.deref.2.2.2))
noncomputable instance {A : Type} {F : Type} {_tactus_assoc_F_Fn_Output : Type} [marker.Tuple A] [ops.function.Fn F A _tactus_assoc_F_Fn_Output] : ops.function.Fn (Tactus.Ref F) A _tactus_assoc_F_Fn_Output where
noncomputable instance {Args : Type} {F : Type} {_tactus_assoc_F_Fn_Output : Type} [marker.Tuple Args] [ops.function.Fn F Args _tactus_assoc_F_Fn_Output] : ops.function.Fn (Tactus.Box F) Args _tactus_assoc_F_Fn_Output where
noncomputable instance {A : Type} {F : Type} {_tactus_assoc_F_Fn_Output : Type} [marker.Tuple A] [ops.function.Fn F A _tactus_assoc_F_Fn_Output] : ops.function.FnMut (Tactus.Ref F) A _tactus_assoc_F_Fn_Output where
noncomputable instance {Args : Type} {F : Type} {_tactus_assoc_F_FnMut_Output : Type} [marker.Tuple Args] [ops.function.FnMut F Args _tactus_assoc_F_FnMut_Output] : ops.function.FnMut (Tactus.Box F) Args _tactus_assoc_F_FnMut_Output where
noncomputable instance {A : Type} {F : Type} {_tactus_assoc_F_Fn_Output : Type} [marker.Tuple A] [ops.function.Fn F A _tactus_assoc_F_Fn_Output] : ops.function.FnOnce (Tactus.Ref F) A _tactus_assoc_F_Fn_Output where
noncomputable instance {Args : Type} {F : Type} {_tactus_assoc_F_FnOnce_Output : Type} [marker.Tuple Args] [ops.function.FnOnce F Args _tactus_assoc_F_FnOnce_Output] : ops.function.FnOnce (Tactus.Box F) Args _tactus_assoc_F_FnOnce_Output where
noncomputable instance {A : Type} [alloc.Allocator A] : alloc.Allocator (Tactus.Ref A) where
noncomputable instance : alloc.Allocator alloc.Global where
noncomputable instance {T : Type} [alloc.Allocator T] : alloc.Allocator (Tactus.Box T) where
noncomputable instance {T : Type} [alloc.Allocator T] : alloc.Allocator (Tactus.Rc T) where
noncomputable instance {T : Type} [alloc.Allocator T] : alloc.Allocator (Tactus.Arc T) where
axiom seq.axiom_seq_index_decreases (A : Type) [Nonempty A] (s : seq.Seq A) (i : Int) (h0 : 0 ≤ i ∧ i < seq.Seq.len A s) : Tactus.heightLt (seq.Seq.index A s i) s
axiom seq.axiom_seq_subrange_decreases (A : Type) [Nonempty A] (s : seq.Seq A) (i : Int) (j : Int) (h0 : 0 ≤ i ∧ i ≤ j ∧ j ≤ seq.Seq.len A s) (h1 : seq.Seq.len A (seq.Seq.subrange A s i j) < seq.Seq.len A s) : Tactus.heightLt (seq.Seq.subrange A s i j) s
axiom seq.axiom_seq_empty (A : Type) [Nonempty A] : seq.Seq.len A (seq.Seq.empty A) = 0
axiom seq.axiom_seq_new_len (A : Type) [Nonempty A] (len : Nat) (f : Int → A) : seq.Seq.len A (seq.Seq.new A (Int → A) len f) = len
axiom seq.axiom_seq_new_index (A : Type) [Nonempty A] (len : Nat) (f : Int → A) (i : Int) (h0 : 0 ≤ i ∧ i < len) : seq.Seq.index A (seq.Seq.new A (Int → A) len f) i = (Tactus.Ref.mk f).deref i
axiom seq.axiom_seq_push_len (A : Type) [Nonempty A] (s : seq.Seq A) (a : A) : seq.Seq.len A (seq.Seq.push A s a) = seq.Seq.len A s + 1
axiom seq.axiom_seq_push_index_same (A : Type) [Nonempty A] (s : seq.Seq A) (a : A) (i : Int) (h0 : i = seq.Seq.len A s) : seq.Seq.index A (seq.Seq.push A s a) i = a
axiom seq.axiom_seq_push_index_different (A : Type) [Nonempty A] (s : seq.Seq A) (a : A) (i : Int) (h0 : 0 ≤ i ∧ i < seq.Seq.len A s) : seq.Seq.index A (seq.Seq.push A s a) i = seq.Seq.index A s i
axiom seq.axiom_seq_update_len (A : Type) [Nonempty A] (s : seq.Seq A) (i : Int) (a : A) (h0 : 0 ≤ i ∧ i < seq.Seq.len A s) : seq.Seq.len A (seq.Seq.update A s i a) = seq.Seq.len A s
axiom seq.axiom_seq_update_same (A : Type) [Nonempty A] (s : seq.Seq A) (i : Int) (a : A) (h0 : 0 ≤ i ∧ i < seq.Seq.len A s) : seq.Seq.index A (seq.Seq.update A s i a) i = a
axiom seq.axiom_seq_update_different (A : Type) [Nonempty A] (s : seq.Seq A) (i1 : Int) (i2 : Int) (a : A) (h0 : 0 ≤ i1 ∧ i1 < seq.Seq.len A s) (h1 : 0 ≤ i2 ∧ i2 < seq.Seq.len A s) (h2 : ¬(i1 = i2)) : seq.Seq.index A (seq.Seq.update A s i2 a) i1 = seq.Seq.index A s i1
axiom seq.axiom_seq_ext_equal (A : Type) [Nonempty A] (s1 : seq.Seq A) (s2 : seq.Seq A) : (s1 = s2) = (seq.Seq.len A s1 = seq.Seq.len A s2 ∧ (∀ (i : Int), 0 ≤ i ∧ i < seq.Seq.len A s1 → seq.Seq.index A s1 i = seq.Seq.index A s2 i))
axiom seq.axiom_seq_ext_equal_deep (A : Type) [Nonempty A] (s1 : seq.Seq A) (s2 : seq.Seq A) : (s1 = s2) = (seq.Seq.len A s1 = seq.Seq.len A s2 ∧ (∀ (i : Int), 0 ≤ i ∧ i < seq.Seq.len A s1 → seq.Seq.index A s1 i = seq.Seq.index A s2 i))
axiom seq.axiom_seq_subrange_len (A : Type) [Nonempty A] (s : seq.Seq A) (j : Int) (k : Int) (h0 : 0 ≤ j ∧ j ≤ k ∧ k ≤ seq.Seq.len A s) : seq.Seq.len A (seq.Seq.subrange A s j k) = k - j
axiom seq.axiom_seq_subrange_index (A : Type) [Nonempty A] (s : seq.Seq A) (j : Int) (k : Int) (i : Int) (h0 : 0 ≤ j ∧ j ≤ k ∧ k ≤ seq.Seq.len A s) (h1 : 0 ≤ i ∧ i < k - j) : seq.Seq.index A (seq.Seq.subrange A s j k) i = seq.Seq.index A s (i + j)
axiom seq.lemma_seq_two_subranges_index (A : Type) [Nonempty A] (s : seq.Seq A) (j : Int) (k1 : Int) (k2 : Int) (i : Int) (h0 : 0 ≤ j ∧ j ≤ k1 ∧ k1 ≤ seq.Seq.len A s) (h1 : 0 ≤ j ∧ j ≤ k2 ∧ k2 ≤ seq.Seq.len A s) (h2 : 0 ≤ i ∧ i < k1 - j) (h3 : 0 ≤ i ∧ i < k2 - j) : seq.Seq.index A (seq.Seq.subrange A s j k1) i = seq.Seq.index A (seq.Seq.subrange A s j k2) i
axiom seq.axiom_seq_add_len (A : Type) [Nonempty A] (s1 : seq.Seq A) (s2 : seq.Seq A) : seq.Seq.len A (seq.Seq.add A s1 s2) = seq.Seq.len A s1 + seq.Seq.len A s2
axiom seq.axiom_seq_add_index1 (A : Type) [Nonempty A] (s1 : seq.Seq A) (s2 : seq.Seq A) (i : Int) (h0 : 0 ≤ i ∧ i < seq.Seq.len A s1) : seq.Seq.index A (seq.Seq.add A s1 s2) i = seq.Seq.index A s1 i
axiom seq.axiom_seq_add_index2 (A : Type) [Nonempty A] (s1 : seq.Seq A) (s2 : seq.Seq A) (i : Int) (h0 : seq.Seq.len A s1 ≤ i ∧ i < seq.Seq.len A s1 + seq.Seq.len A s2) : seq.Seq.index A (seq.Seq.add A s1 s2) i = seq.Seq.index A s2 (i - seq.Seq.len A s1)
axiom seq_lib.impl__0.add_empty_left (A : Type) [Nonempty A] (a : seq.Seq A) (b : seq.Seq A) (h0 : seq.Seq.len A a = 0) : seq.Seq.add A a b = b
axiom seq_lib.impl__0.add_empty_right (A : Type) [Nonempty A] (a : seq.Seq A) (b : seq.Seq A) (h0 : seq.Seq.len A b = 0) : seq.Seq.add A a b = a
axiom seq_lib.impl__0.push_distributes_over_add (A : Type) [Nonempty A] (a : seq.Seq A) (b : seq.Seq A) (elt : A) : seq.Seq.push A (seq.Seq.add A a b) elt = seq.Seq.add A a (seq.Seq.push A b elt)
axiom set.axiom_set_empty (A : Type) [Nonempty A] (a : A) : ¬set.Set.contains A (set.Set.empty A) a
axiom set.axiom_set_insert_same (A : Type) [Nonempty A] (s : set.Set A) (a : A) : set.Set.contains A (set.Set.insert A s a) a
axiom set.axiom_set_insert_different (A : Type) [Nonempty A] (s : set.Set A) (a1 : A) (a2 : A) (h0 : ¬(a1 = a2)) : set.Set.contains A (set.Set.insert A s a2) a1 = set.Set.contains A s a1
axiom set.axiom_set_remove_same (A : Type) [Nonempty A] (s : set.Set A) (a : A) : ¬set.Set.contains A (set.Set.remove A s a) a
axiom set.axiom_set_remove_insert (A : Type) [Nonempty A] (s : set.Set A) (a : A) (h0 : set.Set.contains A s a) : set.Set.insert A (set.Set.remove A s a) a = s
axiom set.axiom_set_remove_different (A : Type) [Nonempty A] (s : set.Set A) (a1 : A) (a2 : A) (h0 : ¬(a1 = a2)) : set.Set.contains A (set.Set.remove A s a2) a1 = set.Set.contains A s a1
axiom set.axiom_set_complement (A : Type) [Nonempty A] (s : set.Set A) (a : A) : set.Set.contains A (Set.complement A s) a = (¬set.Set.contains A s a)
axiom set.axiom_set_ext_equal (A : Type) (s1 : set.Set A) (s2 : set.Set A) : (s1 = s2) = (∀ (a : A), set.Set.contains A s1 a = set.Set.contains A s2 a)
axiom set.axiom_set_ext_equal_deep (A : Type) (s1 : set.Set A) (s2 : set.Set A) : (s1 = s2) = (s1 = s2)
axiom set.axiom_set_empty_finite (A : Type) [Nonempty A] : Set.finite A (set.Set.empty A)
axiom set.axiom_set_insert_finite (A : Type) [Nonempty A] (s : set.Set A) (a : A) (h0 : Set.finite A s) : Set.finite A (set.Set.insert A s a)
axiom set.axiom_set_remove_finite (A : Type) [Nonempty A] (s : set.Set A) (a : A) (h0 : Set.finite A s) : Set.finite A (set.Set.remove A s a)
axiom set_lib.lemma_set_subset_finite (A : Type) (s : set.Set A) (sub : set.Set A) (h0 : Set.finite A s) (h1 : set.Set.subset_of A sub s) : Set.finite A sub
axiom array.array_len_matches_n (T : Type) (N : Nat) [Nonempty T] (ar : Tactus.Ref (Vector T N)) : seq.Seq.len T (view.View.view ((ar : Tactus.Ref (Vector T N)))) = N
axiom array.lemma_array_index (T : Type) (N : Nat) [Nonempty T] (a : Vector T N) (i : Int) (h0 : 0 ≤ i ∧ i < N) : seq.Seq.index T (view.View.view ((Tactus.Ref.mk a : Tactus.Ref (Vector T N)))) i = seq.Seq.index T (array.array_view T N a) i
axiom array.axiom_array_ext_equal (T : Type) (N : Nat) [Nonempty T] (a1 : Vector T N) (a2 : Vector T N) : (a1 = a2) = (∀ (i : Int), 0 ≤ i ∧ i < N → seq.Seq.index T (view.View.view ((Tactus.Ref.mk a1 : Tactus.Ref (Vector T N)))) i = seq.Seq.index T (view.View.view ((Tactus.Ref.mk a2 : Tactus.Ref (Vector T N)))) i)
axiom array.axiom_array_has_resolved (T : Type) (N : Nat) [Nonempty T] (array : Vector T N) (i : Int) : 0 ≤ i ∧ i < N → Tactus.hasResolved array → Tactus.hasResolved (seq.Seq.index T (view.View.view ((Tactus.Ref.mk array : Tactus.Ref (Vector T N)))) i)
axiom std_specs.vec.axiom_spec_len (T : Type) (A : Type) [alloc.Allocator A] [Nonempty T] (v : Tactus.Ref (vec.Vec T A)) : std_specs.vec.spec_vec_len T A v = seq.Seq.len T (view.View.view v)
axiom std_specs.vec.axiom_vec_index_decreases (A : Type) [Nonempty A] (v : vec.Vec A alloc.Global) (i : Int) (h0 : 0 ≤ i ∧ i < std_specs.vec.spec_vec_len A alloc.Global (Tactus.Ref.mk v)) : Tactus.heightLt (seq.Seq.index A (view.View.view (Tactus.Ref.mk v)) i) v
axiom std_specs.vec.vec_clone_deep_view_proof (T : Type) (A : Type) {_tactus_assoc_T_DeepView_V : Type} [view.DeepView T _tactus_assoc_T_DeepView_V] [alloc.Allocator A] [Nonempty T] [Nonempty _tactus_assoc_T_DeepView_V] (v1 : vec.Vec T A) (v2 : vec.Vec T A) (h0 : std_specs.vec.vec_clone_trigger T A v1 v2) (h1 : view.DeepView.deep_view (Tactus.Ref.mk v1) = view.DeepView.deep_view (Tactus.Ref.mk v2)) : view.DeepView.deep_view (Tactus.Ref.mk v1) = view.DeepView.deep_view (Tactus.Ref.mk v2)
axiom std_specs.vec.axiom_vec_has_resolved (T : Type) [Nonempty T] (vec : vec.Vec T alloc.Global) (i : Int) : 0 ≤ i ∧ i < std_specs.vec.spec_vec_len T alloc.Global (Tactus.Ref.mk vec) → Tactus.hasResolved vec → Tactus.hasResolved (seq.Seq.index T (view.View.view (Tactus.Ref.mk vec)) i)
axiom std_specs.vec.axiom_vec_decreases_to_view (T : Type) [Nonempty T] (v : vec.Vec T alloc.Global) : Tactus.heightLt (view.View.view (Tactus.Ref.mk v)) v
theorem runtime.lemma_fcf_end (v : seq.Seq symbol.Symbol) (i : Nat) (h0 : i + 1 ≥ seq.Seq.len symbol.Symbol v) :
    reduction.find_cancellation_from v i = seq.Seq.len symbol.Symbol v := by

  rw [reduction.find_cancellation_from.eq_def]
  split <;> omega
theorem runtime.lemma_fcf_found (v : seq.Seq symbol.Symbol) (i : Nat) (h0 : i + 1 < seq.Seq.len symbol.Symbol v) (h1 : symbol.is_inverse_pair (seq.Seq.index symbol.Symbol v (Int.ofNat i)) (seq.Seq.index symbol.Symbol v (i + 1))) :
    reduction.find_cancellation_from v i = i := by

  rw [reduction.find_cancellation_from.eq_def]
  split
  · omega
  · simp_all
theorem runtime.lemma_fcf_step (v : seq.Seq symbol.Symbol) (i : Nat) (h0 : i + 1 < seq.Seq.len symbol.Symbol v) (h1 : ¬symbol.is_inverse_pair (seq.Seq.index symbol.Symbol v (Int.ofNat i)) (seq.Seq.index symbol.Symbol v (i + 1))) :
    reduction.find_cancellation_from v i = reduction.find_cancellation_from v (i + 1) := by

  rw [reduction.find_cancellation_from.eq_def]
  split
  · omega
  · simp_all
theorem machine_group.lemma_div_mod_id (x : Nat) (m : Nat) (h0 : m > 0) :
    x = x / m * m + x % m := by

  have h1 := Nat.div_add_mod x m
  have h2 := Nat.mul_comm (x / m) m
  omega
theorem ii_subset.lemma_exact_div (x : Int) (m : Int) (h0 : m > 0) (h1 : x % m = 0) :
    x = x / m * m := by

  have h1 := Int.ediv_add_emod x m
  have h2 := Int.mul_comm (x / m) m
  omega
theorem _tactus_assert_runtime.find_cancellation_exec_at_runtime_103_16_2 (w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global)) (h_req0 : seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1) :
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__1 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    /- @rust:src/runtime.rs:102:8 -/ tmp__1 ≤ 1 → /- @rust:src/runtime.rs:103:16 -/ reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) 0 = seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) := by
  (
    have _tactus_bc_0 := @seq.axiom_seq_index_decreases
    have _tactus_bc_1 := @seq.axiom_seq_subrange_decreases
    have _tactus_bc_2 := @seq.axiom_seq_empty
    have _tactus_bc_3 := @seq.axiom_seq_new_len
    have _tactus_bc_4 := @seq.axiom_seq_new_index
    have _tactus_bc_5 := @seq.axiom_seq_push_len
    have _tactus_bc_6 := @seq.axiom_seq_push_index_same
    have _tactus_bc_7 := @seq.axiom_seq_push_index_different
    have _tactus_bc_8 := @seq.axiom_seq_update_len
    have _tactus_bc_9 := @seq.axiom_seq_update_same
    have _tactus_bc_10 := @seq.axiom_seq_update_different
    have _tactus_bc_11 := @seq.axiom_seq_ext_equal
    have _tactus_bc_12 := @seq.axiom_seq_ext_equal_deep
    have _tactus_bc_13 := @seq.axiom_seq_subrange_len
    have _tactus_bc_14 := @seq.axiom_seq_subrange_index
    have _tactus_bc_15 := @seq.lemma_seq_two_subranges_index
    have _tactus_bc_16 := @seq.axiom_seq_add_len
    have _tactus_bc_17 := @seq.axiom_seq_add_index1
    have _tactus_bc_18 := @seq.axiom_seq_add_index2
    have _tactus_bc_19 := @seq_lib.impl__0.add_empty_left
    have _tactus_bc_20 := @seq_lib.impl__0.add_empty_right
    have _tactus_bc_21 := @seq_lib.impl__0.push_distributes_over_add
    have _tactus_bc_22 := @set.axiom_set_empty
    have _tactus_bc_23 := @set.axiom_set_insert_same
    have _tactus_bc_24 := @set.axiom_set_insert_different
    have _tactus_bc_25 := @set.axiom_set_remove_same
    have _tactus_bc_26 := @set.axiom_set_remove_insert
    have _tactus_bc_27 := @set.axiom_set_remove_different
    have _tactus_bc_28 := @set.axiom_set_complement
    have _tactus_bc_29 := @set.axiom_set_ext_equal
    have _tactus_bc_30 := @set.axiom_set_ext_equal_deep
    have _tactus_bc_31 := @set.axiom_set_empty_finite
    have _tactus_bc_32 := @set.axiom_set_insert_finite
    have _tactus_bc_33 := @set.axiom_set_remove_finite
    have _tactus_bc_34 := @set_lib.lemma_set_subset_finite
    have _tactus_bc_35 := @array.array_len_matches_n
    have _tactus_bc_36 := @array.lemma_array_index
    have _tactus_bc_37 := @array.axiom_array_ext_equal
    have _tactus_bc_38 := @array.axiom_array_has_resolved
    have _tactus_bc_39 := @std_specs.vec.axiom_spec_len
    have _tactus_bc_40 := @std_specs.vec.axiom_vec_index_decreases
    have _tactus_bc_41 := @std_specs.vec.vec_clone_deep_view_proof
    have _tactus_bc_42 := @std_specs.vec.axiom_vec_has_resolved
    have _tactus_bc_43 := @std_specs.vec.axiom_vec_decreases_to_view
  ) <;> (

    intros; haveI : alloc.Allocator alloc.Global := ⟨⟩; have hlen := std_specs.vec.axiom_spec_len runtime.RuntimeSymbol alloc.Global w; have hend := runtime.lemma_fcf_end (runtime.runtime_word_view (view.View.view w)) 0 (by simp only [runtime.runtime_word_view]; rw [seq.axiom_seq_new_len]; omega); simp_all [runtime.runtime_word_view, seq.axiom_seq_new_len] <;> omega
  )
theorem _tactus_postcondition_runtime.find_cancellation_exec_at_runtime_100_9_4 (w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global)) (h_req0 : seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1) :
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__1 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    /- @rust:src/runtime.rs:102:8 -/ tmp__1 ≤ 1 → reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) 0 = seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) → reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) 0 = seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) → 0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__2 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    let out := tmp__2;
    /- @rust:src/runtime.rs:100:9 -/ out = reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) 0)) := by
  (
    have _tactus_bc_0 := @seq.axiom_seq_index_decreases
    have _tactus_bc_1 := @seq.axiom_seq_subrange_decreases
    have _tactus_bc_2 := @seq.axiom_seq_empty
    have _tactus_bc_3 := @seq.axiom_seq_new_len
    have _tactus_bc_4 := @seq.axiom_seq_new_index
    have _tactus_bc_5 := @seq.axiom_seq_push_len
    have _tactus_bc_6 := @seq.axiom_seq_push_index_same
    have _tactus_bc_7 := @seq.axiom_seq_push_index_different
    have _tactus_bc_8 := @seq.axiom_seq_update_len
    have _tactus_bc_9 := @seq.axiom_seq_update_same
    have _tactus_bc_10 := @seq.axiom_seq_update_different
    have _tactus_bc_11 := @seq.axiom_seq_ext_equal
    have _tactus_bc_12 := @seq.axiom_seq_ext_equal_deep
    have _tactus_bc_13 := @seq.axiom_seq_subrange_len
    have _tactus_bc_14 := @seq.axiom_seq_subrange_index
    have _tactus_bc_15 := @seq.lemma_seq_two_subranges_index
    have _tactus_bc_16 := @seq.axiom_seq_add_len
    have _tactus_bc_17 := @seq.axiom_seq_add_index1
    have _tactus_bc_18 := @seq.axiom_seq_add_index2
    have _tactus_bc_19 := @seq_lib.impl__0.add_empty_left
    have _tactus_bc_20 := @seq_lib.impl__0.add_empty_right
    have _tactus_bc_21 := @seq_lib.impl__0.push_distributes_over_add
    have _tactus_bc_22 := @set.axiom_set_empty
    have _tactus_bc_23 := @set.axiom_set_insert_same
    have _tactus_bc_24 := @set.axiom_set_insert_different
    have _tactus_bc_25 := @set.axiom_set_remove_same
    have _tactus_bc_26 := @set.axiom_set_remove_insert
    have _tactus_bc_27 := @set.axiom_set_remove_different
    have _tactus_bc_28 := @set.axiom_set_complement
    have _tactus_bc_29 := @set.axiom_set_ext_equal
    have _tactus_bc_30 := @set.axiom_set_ext_equal_deep
    have _tactus_bc_31 := @set.axiom_set_empty_finite
    have _tactus_bc_32 := @set.axiom_set_insert_finite
    have _tactus_bc_33 := @set.axiom_set_remove_finite
    have _tactus_bc_34 := @set_lib.lemma_set_subset_finite
    have _tactus_bc_35 := @array.array_len_matches_n
    have _tactus_bc_36 := @array.lemma_array_index
    have _tactus_bc_37 := @array.axiom_array_ext_equal
    have _tactus_bc_38 := @array.axiom_array_has_resolved
    have _tactus_bc_39 := @std_specs.vec.axiom_spec_len
    have _tactus_bc_40 := @std_specs.vec.axiom_vec_index_decreases
    have _tactus_bc_41 := @std_specs.vec.vec_clone_deep_view_proof
    have _tactus_bc_42 := @std_specs.vec.axiom_vec_has_resolved
    have _tactus_bc_43 := @std_specs.vec.axiom_vec_decreases_to_view
  ) <;> tactus_auto
theorem _tactus_loop_invariant_runtime.find_cancellation_exec_at_runtime_111_13_5 (w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global)) (h_req0 : seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1) :
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__1 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    ¬(/- @rust:src/runtime.rs:102:8 -/ tmp__1 ≤ 1) → (let i := 0;
    /- @rust:src/runtime.rs:111:13 -/ let tmp__ := 0;
    let tmp___1 := i;
    let tmp___2 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w - 1;
    tmp__ ≤ tmp___1 ∧ tmp___1 ≤ tmp___2)) := by
  (
    have _tactus_bc_0 := @seq.axiom_seq_index_decreases
    have _tactus_bc_1 := @seq.axiom_seq_subrange_decreases
    have _tactus_bc_2 := @seq.axiom_seq_empty
    have _tactus_bc_3 := @seq.axiom_seq_new_len
    have _tactus_bc_4 := @seq.axiom_seq_new_index
    have _tactus_bc_5 := @seq.axiom_seq_push_len
    have _tactus_bc_6 := @seq.axiom_seq_push_index_same
    have _tactus_bc_7 := @seq.axiom_seq_push_index_different
    have _tactus_bc_8 := @seq.axiom_seq_update_len
    have _tactus_bc_9 := @seq.axiom_seq_update_same
    have _tactus_bc_10 := @seq.axiom_seq_update_different
    have _tactus_bc_11 := @seq.axiom_seq_ext_equal
    have _tactus_bc_12 := @seq.axiom_seq_ext_equal_deep
    have _tactus_bc_13 := @seq.axiom_seq_subrange_len
    have _tactus_bc_14 := @seq.axiom_seq_subrange_index
    have _tactus_bc_15 := @seq.lemma_seq_two_subranges_index
    have _tactus_bc_16 := @seq.axiom_seq_add_len
    have _tactus_bc_17 := @seq.axiom_seq_add_index1
    have _tactus_bc_18 := @seq.axiom_seq_add_index2
    have _tactus_bc_19 := @seq_lib.impl__0.add_empty_left
    have _tactus_bc_20 := @seq_lib.impl__0.add_empty_right
    have _tactus_bc_21 := @seq_lib.impl__0.push_distributes_over_add
    have _tactus_bc_22 := @set.axiom_set_empty
    have _tactus_bc_23 := @set.axiom_set_insert_same
    have _tactus_bc_24 := @set.axiom_set_insert_different
    have _tactus_bc_25 := @set.axiom_set_remove_same
    have _tactus_bc_26 := @set.axiom_set_remove_insert
    have _tactus_bc_27 := @set.axiom_set_remove_different
    have _tactus_bc_28 := @set.axiom_set_complement
    have _tactus_bc_29 := @set.axiom_set_ext_equal
    have _tactus_bc_30 := @set.axiom_set_ext_equal_deep
    have _tactus_bc_31 := @set.axiom_set_empty_finite
    have _tactus_bc_32 := @set.axiom_set_insert_finite
    have _tactus_bc_33 := @set.axiom_set_remove_finite
    have _tactus_bc_34 := @set_lib.lemma_set_subset_finite
    have _tactus_bc_35 := @array.array_len_matches_n
    have _tactus_bc_36 := @array.lemma_array_index
    have _tactus_bc_37 := @array.axiom_array_ext_equal
    have _tactus_bc_38 := @array.axiom_array_has_resolved
    have _tactus_bc_39 := @std_specs.vec.axiom_spec_len
    have _tactus_bc_40 := @std_specs.vec.axiom_vec_index_decreases
    have _tactus_bc_41 := @std_specs.vec.vec_clone_deep_view_proof
    have _tactus_bc_42 := @std_specs.vec.axiom_vec_has_resolved
    have _tactus_bc_43 := @std_specs.vec.axiom_vec_decreases_to_view
  ) <;> tactus_auto
theorem _tactus_loop_invariant_runtime.find_cancellation_exec_at_runtime_112_13_6 (w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global)) (h_req0 : seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1) :
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__1 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    ¬(/- @rust:src/runtime.rs:102:8 -/ tmp__1 ≤ 1) → (let i := 0;
    /- @rust:src/runtime.rs:112:13 -/ seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1)) := by
  (
    have _tactus_bc_0 := @seq.axiom_seq_index_decreases
    have _tactus_bc_1 := @seq.axiom_seq_subrange_decreases
    have _tactus_bc_2 := @seq.axiom_seq_empty
    have _tactus_bc_3 := @seq.axiom_seq_new_len
    have _tactus_bc_4 := @seq.axiom_seq_new_index
    have _tactus_bc_5 := @seq.axiom_seq_push_len
    have _tactus_bc_6 := @seq.axiom_seq_push_index_same
    have _tactus_bc_7 := @seq.axiom_seq_push_index_different
    have _tactus_bc_8 := @seq.axiom_seq_update_len
    have _tactus_bc_9 := @seq.axiom_seq_update_same
    have _tactus_bc_10 := @seq.axiom_seq_update_different
    have _tactus_bc_11 := @seq.axiom_seq_ext_equal
    have _tactus_bc_12 := @seq.axiom_seq_ext_equal_deep
    have _tactus_bc_13 := @seq.axiom_seq_subrange_len
    have _tactus_bc_14 := @seq.axiom_seq_subrange_index
    have _tactus_bc_15 := @seq.lemma_seq_two_subranges_index
    have _tactus_bc_16 := @seq.axiom_seq_add_len
    have _tactus_bc_17 := @seq.axiom_seq_add_index1
    have _tactus_bc_18 := @seq.axiom_seq_add_index2
    have _tactus_bc_19 := @seq_lib.impl__0.add_empty_left
    have _tactus_bc_20 := @seq_lib.impl__0.add_empty_right
    have _tactus_bc_21 := @seq_lib.impl__0.push_distributes_over_add
    have _tactus_bc_22 := @set.axiom_set_empty
    have _tactus_bc_23 := @set.axiom_set_insert_same
    have _tactus_bc_24 := @set.axiom_set_insert_different
    have _tactus_bc_25 := @set.axiom_set_remove_same
    have _tactus_bc_26 := @set.axiom_set_remove_insert
    have _tactus_bc_27 := @set.axiom_set_remove_different
    have _tactus_bc_28 := @set.axiom_set_complement
    have _tactus_bc_29 := @set.axiom_set_ext_equal
    have _tactus_bc_30 := @set.axiom_set_ext_equal_deep
    have _tactus_bc_31 := @set.axiom_set_empty_finite
    have _tactus_bc_32 := @set.axiom_set_insert_finite
    have _tactus_bc_33 := @set.axiom_set_remove_finite
    have _tactus_bc_34 := @set_lib.lemma_set_subset_finite
    have _tactus_bc_35 := @array.array_len_matches_n
    have _tactus_bc_36 := @array.lemma_array_index
    have _tactus_bc_37 := @array.axiom_array_ext_equal
    have _tactus_bc_38 := @array.axiom_array_has_resolved
    have _tactus_bc_39 := @std_specs.vec.axiom_spec_len
    have _tactus_bc_40 := @std_specs.vec.axiom_vec_index_decreases
    have _tactus_bc_41 := @std_specs.vec.vec_clone_deep_view_proof
    have _tactus_bc_42 := @std_specs.vec.axiom_vec_has_resolved
    have _tactus_bc_43 := @std_specs.vec.axiom_vec_decreases_to_view
  ) <;> tactus_auto
theorem _tactus_loop_invariant_runtime.find_cancellation_exec_at_runtime_113_13_7 (w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global)) (h_req0 : seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1) :
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__1 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    ¬(/- @rust:src/runtime.rs:102:8 -/ tmp__1 ≤ 1) → (let i := 0;
    /- @rust:src/runtime.rs:113:13 -/ reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) 0 = reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) i)) := by
  (
    have _tactus_bc_0 := @seq.axiom_seq_index_decreases
    have _tactus_bc_1 := @seq.axiom_seq_subrange_decreases
    have _tactus_bc_2 := @seq.axiom_seq_empty
    have _tactus_bc_3 := @seq.axiom_seq_new_len
    have _tactus_bc_4 := @seq.axiom_seq_new_index
    have _tactus_bc_5 := @seq.axiom_seq_push_len
    have _tactus_bc_6 := @seq.axiom_seq_push_index_same
    have _tactus_bc_7 := @seq.axiom_seq_push_index_different
    have _tactus_bc_8 := @seq.axiom_seq_update_len
    have _tactus_bc_9 := @seq.axiom_seq_update_same
    have _tactus_bc_10 := @seq.axiom_seq_update_different
    have _tactus_bc_11 := @seq.axiom_seq_ext_equal
    have _tactus_bc_12 := @seq.axiom_seq_ext_equal_deep
    have _tactus_bc_13 := @seq.axiom_seq_subrange_len
    have _tactus_bc_14 := @seq.axiom_seq_subrange_index
    have _tactus_bc_15 := @seq.lemma_seq_two_subranges_index
    have _tactus_bc_16 := @seq.axiom_seq_add_len
    have _tactus_bc_17 := @seq.axiom_seq_add_index1
    have _tactus_bc_18 := @seq.axiom_seq_add_index2
    have _tactus_bc_19 := @seq_lib.impl__0.add_empty_left
    have _tactus_bc_20 := @seq_lib.impl__0.add_empty_right
    have _tactus_bc_21 := @seq_lib.impl__0.push_distributes_over_add
    have _tactus_bc_22 := @set.axiom_set_empty
    have _tactus_bc_23 := @set.axiom_set_insert_same
    have _tactus_bc_24 := @set.axiom_set_insert_different
    have _tactus_bc_25 := @set.axiom_set_remove_same
    have _tactus_bc_26 := @set.axiom_set_remove_insert
    have _tactus_bc_27 := @set.axiom_set_remove_different
    have _tactus_bc_28 := @set.axiom_set_complement
    have _tactus_bc_29 := @set.axiom_set_ext_equal
    have _tactus_bc_30 := @set.axiom_set_ext_equal_deep
    have _tactus_bc_31 := @set.axiom_set_empty_finite
    have _tactus_bc_32 := @set.axiom_set_insert_finite
    have _tactus_bc_33 := @set.axiom_set_remove_finite
    have _tactus_bc_34 := @set_lib.lemma_set_subset_finite
    have _tactus_bc_35 := @array.array_len_matches_n
    have _tactus_bc_36 := @array.lemma_array_index
    have _tactus_bc_37 := @array.axiom_array_ext_equal
    have _tactus_bc_38 := @array.axiom_array_has_resolved
    have _tactus_bc_39 := @std_specs.vec.axiom_spec_len
    have _tactus_bc_40 := @std_specs.vec.axiom_vec_index_decreases
    have _tactus_bc_41 := @std_specs.vec.vec_clone_deep_view_proof
    have _tactus_bc_42 := @std_specs.vec.axiom_vec_has_resolved
    have _tactus_bc_43 := @std_specs.vec.axiom_vec_decreases_to_view
  ) <;> tactus_auto
theorem _tactus_assert_runtime.find_cancellation_exec_at_runtime_109_15_9 (w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global)) (h_req0 : seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1) :
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__1 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    ¬(/- @rust:src/runtime.rs:102:8 -/ tmp__1 ≤ 1) → (∀ (i : Nat), 0 ≤ i ∧ i < usize_hi → (/- @rust:src/runtime.rs:111:13 -/ let tmp__ := 0;
    let tmp___1 := i;
    let tmp___2 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w - 1;
    tmp__ ≤ tmp___1 ∧ tmp___1 ≤ tmp___2) → /- @rust:src/runtime.rs:112:13 -/ seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1 → /- @rust:src/runtime.rs:113:13 -/ reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) 0 = reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) i → (let _tactus_d_old_0_0 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w - i;
    let tmp__4 := i;
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__3 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    /- @rust:src/runtime.rs:109:15 -/ 0 ≤ tmp__3 - 1 ∧ tmp__3 - 1 < usize_hi)))) := by
  (
    have _tactus_bc_0 := @seq.axiom_seq_index_decreases
    have _tactus_bc_1 := @seq.axiom_seq_subrange_decreases
    have _tactus_bc_2 := @seq.axiom_seq_empty
    have _tactus_bc_3 := @seq.axiom_seq_new_len
    have _tactus_bc_4 := @seq.axiom_seq_new_index
    have _tactus_bc_5 := @seq.axiom_seq_push_len
    have _tactus_bc_6 := @seq.axiom_seq_push_index_same
    have _tactus_bc_7 := @seq.axiom_seq_push_index_different
    have _tactus_bc_8 := @seq.axiom_seq_update_len
    have _tactus_bc_9 := @seq.axiom_seq_update_same
    have _tactus_bc_10 := @seq.axiom_seq_update_different
    have _tactus_bc_11 := @seq.axiom_seq_ext_equal
    have _tactus_bc_12 := @seq.axiom_seq_ext_equal_deep
    have _tactus_bc_13 := @seq.axiom_seq_subrange_len
    have _tactus_bc_14 := @seq.axiom_seq_subrange_index
    have _tactus_bc_15 := @seq.lemma_seq_two_subranges_index
    have _tactus_bc_16 := @seq.axiom_seq_add_len
    have _tactus_bc_17 := @seq.axiom_seq_add_index1
    have _tactus_bc_18 := @seq.axiom_seq_add_index2
    have _tactus_bc_19 := @seq_lib.impl__0.add_empty_left
    have _tactus_bc_20 := @seq_lib.impl__0.add_empty_right
    have _tactus_bc_21 := @seq_lib.impl__0.push_distributes_over_add
    have _tactus_bc_22 := @set.axiom_set_empty
    have _tactus_bc_23 := @set.axiom_set_insert_same
    have _tactus_bc_24 := @set.axiom_set_insert_different
    have _tactus_bc_25 := @set.axiom_set_remove_same
    have _tactus_bc_26 := @set.axiom_set_remove_insert
    have _tactus_bc_27 := @set.axiom_set_remove_different
    have _tactus_bc_28 := @set.axiom_set_complement
    have _tactus_bc_29 := @set.axiom_set_ext_equal
    have _tactus_bc_30 := @set.axiom_set_ext_equal_deep
    have _tactus_bc_31 := @set.axiom_set_empty_finite
    have _tactus_bc_32 := @set.axiom_set_insert_finite
    have _tactus_bc_33 := @set.axiom_set_remove_finite
    have _tactus_bc_34 := @set_lib.lemma_set_subset_finite
    have _tactus_bc_35 := @array.array_len_matches_n
    have _tactus_bc_36 := @array.lemma_array_index
    have _tactus_bc_37 := @array.axiom_array_ext_equal
    have _tactus_bc_38 := @array.axiom_array_has_resolved
    have _tactus_bc_39 := @std_specs.vec.axiom_spec_len
    have _tactus_bc_40 := @std_specs.vec.axiom_vec_index_decreases
    have _tactus_bc_41 := @std_specs.vec.vec_clone_deep_view_proof
    have _tactus_bc_42 := @std_specs.vec.axiom_vec_has_resolved
    have _tactus_bc_43 := @std_specs.vec.axiom_vec_decreases_to_view
  ) <;> tactus_auto
theorem _tactus_assert_runtime.find_cancellation_exec_at_runtime_117_16_10 (w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global)) (h_req0 : seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1) :
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__1 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    ¬(/- @rust:src/runtime.rs:102:8 -/ tmp__1 ≤ 1) → (∀ (i : Nat), 0 ≤ i ∧ i < usize_hi → (/- @rust:src/runtime.rs:111:13 -/ let tmp__ := 0;
    let tmp___1 := i;
    let tmp___2 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w - 1;
    tmp__ ≤ tmp___1 ∧ tmp___1 ≤ tmp___2) → /- @rust:src/runtime.rs:112:13 -/ seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1 → /- @rust:src/runtime.rs:113:13 -/ reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) 0 = reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) i → (let _tactus_d_old_0_0 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w - i;
    let tmp__4 := i;
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__3 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    0 ≤ tmp__3 - 1 ∧ tmp__3 - 1 < usize_hi → 0 ≤ tmp__3 - 1 ∧ tmp__3 - 1 < usize_hi → tmp__4 < tmp__3 - 1 → /- @rust:src/runtime.rs:117:16 -/ i + 1 < seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)))))) := by
  (
    have _tactus_bc_0 := @seq.axiom_seq_index_decreases
    have _tactus_bc_1 := @seq.axiom_seq_subrange_decreases
    have _tactus_bc_2 := @seq.axiom_seq_empty
    have _tactus_bc_3 := @seq.axiom_seq_new_len
    have _tactus_bc_4 := @seq.axiom_seq_new_index
    have _tactus_bc_5 := @seq.axiom_seq_push_len
    have _tactus_bc_6 := @seq.axiom_seq_push_index_same
    have _tactus_bc_7 := @seq.axiom_seq_push_index_different
    have _tactus_bc_8 := @seq.axiom_seq_update_len
    have _tactus_bc_9 := @seq.axiom_seq_update_same
    have _tactus_bc_10 := @seq.axiom_seq_update_different
    have _tactus_bc_11 := @seq.axiom_seq_ext_equal
    have _tactus_bc_12 := @seq.axiom_seq_ext_equal_deep
    have _tactus_bc_13 := @seq.axiom_seq_subrange_len
    have _tactus_bc_14 := @seq.axiom_seq_subrange_index
    have _tactus_bc_15 := @seq.lemma_seq_two_subranges_index
    have _tactus_bc_16 := @seq.axiom_seq_add_len
    have _tactus_bc_17 := @seq.axiom_seq_add_index1
    have _tactus_bc_18 := @seq.axiom_seq_add_index2
    have _tactus_bc_19 := @seq_lib.impl__0.add_empty_left
    have _tactus_bc_20 := @seq_lib.impl__0.add_empty_right
    have _tactus_bc_21 := @seq_lib.impl__0.push_distributes_over_add
    have _tactus_bc_22 := @set.axiom_set_empty
    have _tactus_bc_23 := @set.axiom_set_insert_same
    have _tactus_bc_24 := @set.axiom_set_insert_different
    have _tactus_bc_25 := @set.axiom_set_remove_same
    have _tactus_bc_26 := @set.axiom_set_remove_insert
    have _tactus_bc_27 := @set.axiom_set_remove_different
    have _tactus_bc_28 := @set.axiom_set_complement
    have _tactus_bc_29 := @set.axiom_set_ext_equal
    have _tactus_bc_30 := @set.axiom_set_ext_equal_deep
    have _tactus_bc_31 := @set.axiom_set_empty_finite
    have _tactus_bc_32 := @set.axiom_set_insert_finite
    have _tactus_bc_33 := @set.axiom_set_remove_finite
    have _tactus_bc_34 := @set_lib.lemma_set_subset_finite
    have _tactus_bc_35 := @array.array_len_matches_n
    have _tactus_bc_36 := @array.lemma_array_index
    have _tactus_bc_37 := @array.axiom_array_ext_equal
    have _tactus_bc_38 := @array.axiom_array_has_resolved
    have _tactus_bc_39 := @std_specs.vec.axiom_spec_len
    have _tactus_bc_40 := @std_specs.vec.axiom_vec_index_decreases
    have _tactus_bc_41 := @std_specs.vec.vec_clone_deep_view_proof
    have _tactus_bc_42 := @std_specs.vec.axiom_vec_has_resolved
    have _tactus_bc_43 := @std_specs.vec.axiom_vec_decreases_to_view
  ) <;> (
    intro _ tmp__1 _ i _ _ _ _ _tactus_d_old_0_0 tmp__4 _ tmp__3 _ _ _;

    intros; haveI : alloc.Allocator alloc.Global := ⟨⟩; have hlen := std_specs.vec.axiom_spec_len runtime.RuntimeSymbol alloc.Global w; omega
  )
theorem _tactus_precondition_runtime.find_cancellation_exec_at_runtime_120_34_12 (w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global)) (h_req0 : seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1) :
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__1 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    ¬(/- @rust:src/runtime.rs:102:8 -/ tmp__1 ≤ 1) → (∀ (i : Nat), 0 ≤ i ∧ i < usize_hi → (/- @rust:src/runtime.rs:111:13 -/ let tmp__ := 0;
    let tmp___1 := i;
    let tmp___2 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w - 1;
    tmp__ ≤ tmp___1 ∧ tmp___1 ≤ tmp___2) → /- @rust:src/runtime.rs:112:13 -/ seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1 → /- @rust:src/runtime.rs:113:13 -/ reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) 0 = reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) i → (let _tactus_d_old_0_0 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w - i;
    let tmp__4 := i;
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__3 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    0 ≤ tmp__3 - 1 ∧ tmp__3 - 1 < usize_hi → 0 ≤ tmp__3 - 1 ∧ tmp__3 - 1 < usize_hi → tmp__4 < tmp__3 - 1 → i + 1 < seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) → i + 1 < seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) → /- @rust:src/runtime.rs:120:34 -/ i < seq.Seq.len runtime.RuntimeSymbol (view.View.view w))))) := by
  (
    have _tactus_bc_0 := @seq.axiom_seq_index_decreases
    have _tactus_bc_1 := @seq.axiom_seq_subrange_decreases
    have _tactus_bc_2 := @seq.axiom_seq_empty
    have _tactus_bc_3 := @seq.axiom_seq_new_len
    have _tactus_bc_4 := @seq.axiom_seq_new_index
    have _tactus_bc_5 := @seq.axiom_seq_push_len
    have _tactus_bc_6 := @seq.axiom_seq_push_index_same
    have _tactus_bc_7 := @seq.axiom_seq_push_index_different
    have _tactus_bc_8 := @seq.axiom_seq_update_len
    have _tactus_bc_9 := @seq.axiom_seq_update_same
    have _tactus_bc_10 := @seq.axiom_seq_update_different
    have _tactus_bc_11 := @seq.axiom_seq_ext_equal
    have _tactus_bc_12 := @seq.axiom_seq_ext_equal_deep
    have _tactus_bc_13 := @seq.axiom_seq_subrange_len
    have _tactus_bc_14 := @seq.axiom_seq_subrange_index
    have _tactus_bc_15 := @seq.lemma_seq_two_subranges_index
    have _tactus_bc_16 := @seq.axiom_seq_add_len
    have _tactus_bc_17 := @seq.axiom_seq_add_index1
    have _tactus_bc_18 := @seq.axiom_seq_add_index2
    have _tactus_bc_19 := @seq_lib.impl__0.add_empty_left
    have _tactus_bc_20 := @seq_lib.impl__0.add_empty_right
    have _tactus_bc_21 := @seq_lib.impl__0.push_distributes_over_add
    have _tactus_bc_22 := @set.axiom_set_empty
    have _tactus_bc_23 := @set.axiom_set_insert_same
    have _tactus_bc_24 := @set.axiom_set_insert_different
    have _tactus_bc_25 := @set.axiom_set_remove_same
    have _tactus_bc_26 := @set.axiom_set_remove_insert
    have _tactus_bc_27 := @set.axiom_set_remove_different
    have _tactus_bc_28 := @set.axiom_set_complement
    have _tactus_bc_29 := @set.axiom_set_ext_equal
    have _tactus_bc_30 := @set.axiom_set_ext_equal_deep
    have _tactus_bc_31 := @set.axiom_set_empty_finite
    have _tactus_bc_32 := @set.axiom_set_insert_finite
    have _tactus_bc_33 := @set.axiom_set_remove_finite
    have _tactus_bc_34 := @set_lib.lemma_set_subset_finite
    have _tactus_bc_35 := @array.array_len_matches_n
    have _tactus_bc_36 := @array.lemma_array_index
    have _tactus_bc_37 := @array.axiom_array_ext_equal
    have _tactus_bc_38 := @array.axiom_array_has_resolved
    have _tactus_bc_39 := @std_specs.vec.axiom_spec_len
    have _tactus_bc_40 := @std_specs.vec.axiom_vec_index_decreases
    have _tactus_bc_41 := @std_specs.vec.vec_clone_deep_view_proof
    have _tactus_bc_42 := @std_specs.vec.axiom_vec_has_resolved
    have _tactus_bc_43 := @std_specs.vec.axiom_vec_decreases_to_view
  ) <;> tactus_auto
theorem _tactus_assert_runtime.find_cancellation_exec_at_runtime_120_43_13 (w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global)) (h_req0 : seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1) :
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__1 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    ¬(/- @rust:src/runtime.rs:102:8 -/ tmp__1 ≤ 1) → (∀ (i : Nat), 0 ≤ i ∧ i < usize_hi → (/- @rust:src/runtime.rs:111:13 -/ let tmp__ := 0;
    let tmp___1 := i;
    let tmp___2 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w - 1;
    tmp__ ≤ tmp___1 ∧ tmp___1 ≤ tmp___2) → /- @rust:src/runtime.rs:112:13 -/ seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1 → /- @rust:src/runtime.rs:113:13 -/ reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) 0 = reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) i → (let _tactus_d_old_0_0 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w - i;
    let tmp__4 := i;
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__3 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    0 ≤ tmp__3 - 1 ∧ tmp__3 - 1 < usize_hi → 0 ≤ tmp__3 - 1 ∧ tmp__3 - 1 < usize_hi → tmp__4 < tmp__3 - 1 → i + 1 < seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) → i + 1 < seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) → (let tmp__5 := Tactus.Ref.mk (seq.Seq.index runtime.RuntimeSymbol (view.View.view w) (Int.ofNat i));
    let tmp__9 := tmp__5;
    let tmp__6 := w.deref;
    /- @rust:src/runtime.rs:120:43 -/ 0 ≤ i + 1 ∧ i + 1 < usize_hi))))) := by
  (
    have _tactus_bc_0 := @seq.axiom_seq_index_decreases
    have _tactus_bc_1 := @seq.axiom_seq_subrange_decreases
    have _tactus_bc_2 := @seq.axiom_seq_empty
    have _tactus_bc_3 := @seq.axiom_seq_new_len
    have _tactus_bc_4 := @seq.axiom_seq_new_index
    have _tactus_bc_5 := @seq.axiom_seq_push_len
    have _tactus_bc_6 := @seq.axiom_seq_push_index_same
    have _tactus_bc_7 := @seq.axiom_seq_push_index_different
    have _tactus_bc_8 := @seq.axiom_seq_update_len
    have _tactus_bc_9 := @seq.axiom_seq_update_same
    have _tactus_bc_10 := @seq.axiom_seq_update_different
    have _tactus_bc_11 := @seq.axiom_seq_ext_equal
    have _tactus_bc_12 := @seq.axiom_seq_ext_equal_deep
    have _tactus_bc_13 := @seq.axiom_seq_subrange_len
    have _tactus_bc_14 := @seq.axiom_seq_subrange_index
    have _tactus_bc_15 := @seq.lemma_seq_two_subranges_index
    have _tactus_bc_16 := @seq.axiom_seq_add_len
    have _tactus_bc_17 := @seq.axiom_seq_add_index1
    have _tactus_bc_18 := @seq.axiom_seq_add_index2
    have _tactus_bc_19 := @seq_lib.impl__0.add_empty_left
    have _tactus_bc_20 := @seq_lib.impl__0.add_empty_right
    have _tactus_bc_21 := @seq_lib.impl__0.push_distributes_over_add
    have _tactus_bc_22 := @set.axiom_set_empty
    have _tactus_bc_23 := @set.axiom_set_insert_same
    have _tactus_bc_24 := @set.axiom_set_insert_different
    have _tactus_bc_25 := @set.axiom_set_remove_same
    have _tactus_bc_26 := @set.axiom_set_remove_insert
    have _tactus_bc_27 := @set.axiom_set_remove_different
    have _tactus_bc_28 := @set.axiom_set_complement
    have _tactus_bc_29 := @set.axiom_set_ext_equal
    have _tactus_bc_30 := @set.axiom_set_ext_equal_deep
    have _tactus_bc_31 := @set.axiom_set_empty_finite
    have _tactus_bc_32 := @set.axiom_set_insert_finite
    have _tactus_bc_33 := @set.axiom_set_remove_finite
    have _tactus_bc_34 := @set_lib.lemma_set_subset_finite
    have _tactus_bc_35 := @array.array_len_matches_n
    have _tactus_bc_36 := @array.lemma_array_index
    have _tactus_bc_37 := @array.axiom_array_ext_equal
    have _tactus_bc_38 := @array.axiom_array_has_resolved
    have _tactus_bc_39 := @std_specs.vec.axiom_spec_len
    have _tactus_bc_40 := @std_specs.vec.axiom_vec_index_decreases
    have _tactus_bc_41 := @std_specs.vec.vec_clone_deep_view_proof
    have _tactus_bc_42 := @std_specs.vec.axiom_vec_has_resolved
    have _tactus_bc_43 := @std_specs.vec.axiom_vec_decreases_to_view
  ) <;> tactus_auto
theorem _tactus_precondition_runtime.find_cancellation_exec_at_runtime_120_41_15 (w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global)) (h_req0 : seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1) :
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__1 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    ¬(/- @rust:src/runtime.rs:102:8 -/ tmp__1 ≤ 1) → (∀ (i : Nat), 0 ≤ i ∧ i < usize_hi → (/- @rust:src/runtime.rs:111:13 -/ let tmp__ := 0;
    let tmp___1 := i;
    let tmp___2 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w - 1;
    tmp__ ≤ tmp___1 ∧ tmp___1 ≤ tmp___2) → /- @rust:src/runtime.rs:112:13 -/ seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1 → /- @rust:src/runtime.rs:113:13 -/ reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) 0 = reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) i → (let _tactus_d_old_0_0 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w - i;
    let tmp__4 := i;
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__3 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    0 ≤ tmp__3 - 1 ∧ tmp__3 - 1 < usize_hi → 0 ≤ tmp__3 - 1 ∧ tmp__3 - 1 < usize_hi → tmp__4 < tmp__3 - 1 → i + 1 < seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) → i + 1 < seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) → (let tmp__5 := Tactus.Ref.mk (seq.Seq.index runtime.RuntimeSymbol (view.View.view w) (Int.ofNat i));
    let tmp__9 := tmp__5;
    let tmp__6 := w.deref;
    0 ≤ i + 1 ∧ i + 1 < usize_hi → 0 ≤ i + 1 ∧ i + 1 < usize_hi → (let tmp__8 := i + 1;
    /- @rust:src/runtime.rs:120:41 -/ tmp__8 < seq.Seq.len runtime.RuntimeSymbol (view.View.view (Tactus.Ref.mk tmp__6)))))))) := by
  (
    have _tactus_bc_0 := @seq.axiom_seq_index_decreases
    have _tactus_bc_1 := @seq.axiom_seq_subrange_decreases
    have _tactus_bc_2 := @seq.axiom_seq_empty
    have _tactus_bc_3 := @seq.axiom_seq_new_len
    have _tactus_bc_4 := @seq.axiom_seq_new_index
    have _tactus_bc_5 := @seq.axiom_seq_push_len
    have _tactus_bc_6 := @seq.axiom_seq_push_index_same
    have _tactus_bc_7 := @seq.axiom_seq_push_index_different
    have _tactus_bc_8 := @seq.axiom_seq_update_len
    have _tactus_bc_9 := @seq.axiom_seq_update_same
    have _tactus_bc_10 := @seq.axiom_seq_update_different
    have _tactus_bc_11 := @seq.axiom_seq_ext_equal
    have _tactus_bc_12 := @seq.axiom_seq_ext_equal_deep
    have _tactus_bc_13 := @seq.axiom_seq_subrange_len
    have _tactus_bc_14 := @seq.axiom_seq_subrange_index
    have _tactus_bc_15 := @seq.lemma_seq_two_subranges_index
    have _tactus_bc_16 := @seq.axiom_seq_add_len
    have _tactus_bc_17 := @seq.axiom_seq_add_index1
    have _tactus_bc_18 := @seq.axiom_seq_add_index2
    have _tactus_bc_19 := @seq_lib.impl__0.add_empty_left
    have _tactus_bc_20 := @seq_lib.impl__0.add_empty_right
    have _tactus_bc_21 := @seq_lib.impl__0.push_distributes_over_add
    have _tactus_bc_22 := @set.axiom_set_empty
    have _tactus_bc_23 := @set.axiom_set_insert_same
    have _tactus_bc_24 := @set.axiom_set_insert_different
    have _tactus_bc_25 := @set.axiom_set_remove_same
    have _tactus_bc_26 := @set.axiom_set_remove_insert
    have _tactus_bc_27 := @set.axiom_set_remove_different
    have _tactus_bc_28 := @set.axiom_set_complement
    have _tactus_bc_29 := @set.axiom_set_ext_equal
    have _tactus_bc_30 := @set.axiom_set_ext_equal_deep
    have _tactus_bc_31 := @set.axiom_set_empty_finite
    have _tactus_bc_32 := @set.axiom_set_insert_finite
    have _tactus_bc_33 := @set.axiom_set_remove_finite
    have _tactus_bc_34 := @set_lib.lemma_set_subset_finite
    have _tactus_bc_35 := @array.array_len_matches_n
    have _tactus_bc_36 := @array.lemma_array_index
    have _tactus_bc_37 := @array.axiom_array_ext_equal
    have _tactus_bc_38 := @array.axiom_array_has_resolved
    have _tactus_bc_39 := @std_specs.vec.axiom_spec_len
    have _tactus_bc_40 := @std_specs.vec.axiom_vec_index_decreases
    have _tactus_bc_41 := @std_specs.vec.vec_clone_deep_view_proof
    have _tactus_bc_42 := @std_specs.vec.axiom_vec_has_resolved
    have _tactus_bc_43 := @std_specs.vec.axiom_vec_decreases_to_view
  ) <;> tactus_auto
theorem _tactus_assert_runtime.find_cancellation_exec_at_runtime_121_20_17 (w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global)) (h_req0 : seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1) :
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__1 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    ¬(/- @rust:src/runtime.rs:102:8 -/ tmp__1 ≤ 1) → (∀ (i : Nat), 0 ≤ i ∧ i < usize_hi → (/- @rust:src/runtime.rs:111:13 -/ let tmp__ := 0;
    let tmp___1 := i;
    let tmp___2 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w - 1;
    tmp__ ≤ tmp___1 ∧ tmp___1 ≤ tmp___2) → /- @rust:src/runtime.rs:112:13 -/ seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1 → /- @rust:src/runtime.rs:113:13 -/ reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) 0 = reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) i → (let _tactus_d_old_0_0 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w - i;
    let tmp__4 := i;
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__3 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    0 ≤ tmp__3 - 1 ∧ tmp__3 - 1 < usize_hi → 0 ≤ tmp__3 - 1 ∧ tmp__3 - 1 < usize_hi → tmp__4 < tmp__3 - 1 → i + 1 < seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) → i + 1 < seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) → (let tmp__5 := Tactus.Ref.mk (seq.Seq.index runtime.RuntimeSymbol (view.View.view w) (Int.ofNat i));
    let tmp__9 := tmp__5;
    let tmp__6 := w.deref;
    0 ≤ i + 1 ∧ i + 1 < usize_hi → 0 ≤ i + 1 ∧ i + 1 < usize_hi → (let tmp__8 := i + 1;
    let tmp__7 := Tactus.Ref.mk (seq.Seq.index runtime.RuntimeSymbol (view.View.view (Tactus.Ref.mk tmp__6)) (Int.ofNat tmp__8));
    let tmp__10 := symbol.is_inverse_pair (runtime.runtime_symbol_view tmp__9.deref) (runtime.runtime_symbol_view tmp__7.deref);
    /- @rust:src/runtime.rs:120:12 -/ tmp__10 → /- @rust:src/runtime.rs:121:20 -/ reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) i = i)))))) := by
  (
    have _tactus_bc_0 := @seq.axiom_seq_index_decreases
    have _tactus_bc_1 := @seq.axiom_seq_subrange_decreases
    have _tactus_bc_2 := @seq.axiom_seq_empty
    have _tactus_bc_3 := @seq.axiom_seq_new_len
    have _tactus_bc_4 := @seq.axiom_seq_new_index
    have _tactus_bc_5 := @seq.axiom_seq_push_len
    have _tactus_bc_6 := @seq.axiom_seq_push_index_same
    have _tactus_bc_7 := @seq.axiom_seq_push_index_different
    have _tactus_bc_8 := @seq.axiom_seq_update_len
    have _tactus_bc_9 := @seq.axiom_seq_update_same
    have _tactus_bc_10 := @seq.axiom_seq_update_different
    have _tactus_bc_11 := @seq.axiom_seq_ext_equal
    have _tactus_bc_12 := @seq.axiom_seq_ext_equal_deep
    have _tactus_bc_13 := @seq.axiom_seq_subrange_len
    have _tactus_bc_14 := @seq.axiom_seq_subrange_index
    have _tactus_bc_15 := @seq.lemma_seq_two_subranges_index
    have _tactus_bc_16 := @seq.axiom_seq_add_len
    have _tactus_bc_17 := @seq.axiom_seq_add_index1
    have _tactus_bc_18 := @seq.axiom_seq_add_index2
    have _tactus_bc_19 := @seq_lib.impl__0.add_empty_left
    have _tactus_bc_20 := @seq_lib.impl__0.add_empty_right
    have _tactus_bc_21 := @seq_lib.impl__0.push_distributes_over_add
    have _tactus_bc_22 := @set.axiom_set_empty
    have _tactus_bc_23 := @set.axiom_set_insert_same
    have _tactus_bc_24 := @set.axiom_set_insert_different
    have _tactus_bc_25 := @set.axiom_set_remove_same
    have _tactus_bc_26 := @set.axiom_set_remove_insert
    have _tactus_bc_27 := @set.axiom_set_remove_different
    have _tactus_bc_28 := @set.axiom_set_complement
    have _tactus_bc_29 := @set.axiom_set_ext_equal
    have _tactus_bc_30 := @set.axiom_set_ext_equal_deep
    have _tactus_bc_31 := @set.axiom_set_empty_finite
    have _tactus_bc_32 := @set.axiom_set_insert_finite
    have _tactus_bc_33 := @set.axiom_set_remove_finite
    have _tactus_bc_34 := @set_lib.lemma_set_subset_finite
    have _tactus_bc_35 := @array.array_len_matches_n
    have _tactus_bc_36 := @array.lemma_array_index
    have _tactus_bc_37 := @array.axiom_array_ext_equal
    have _tactus_bc_38 := @array.axiom_array_has_resolved
    have _tactus_bc_39 := @std_specs.vec.axiom_spec_len
    have _tactus_bc_40 := @std_specs.vec.axiom_vec_index_decreases
    have _tactus_bc_41 := @std_specs.vec.vec_clone_deep_view_proof
    have _tactus_bc_42 := @std_specs.vec.axiom_vec_has_resolved
    have _tactus_bc_43 := @std_specs.vec.axiom_vec_decreases_to_view
  ) <;> (
    intro _ tmp__1 _ i _ _ _ _ _tactus_d_old_0_0 tmp__4 _ tmp__3 _ _ _ _ _ tmp__5 tmp__9 tmp__6 _ _ tmp__8 tmp__7 tmp__10 _;

    intros; haveI : alloc.Allocator alloc.Global := ⟨⟩; have hlen := std_specs.vec.axiom_spec_len runtime.RuntimeSymbol alloc.Global w; have hfound := runtime.lemma_fcf_found (runtime.runtime_word_view (view.View.view w)) i (by simp only [runtime.runtime_word_view]; rw [seq.axiom_seq_new_len]; omega) (by simp only [runtime.runtime_word_view]; rw [seq.axiom_seq_new_index _ _ _ _ (by first | (simp only [Int.ofNat_eq_natCast]; omega) | omega), seq.axiom_seq_new_index _ _ _ _ (by first | (simp only [Int.ofNat_eq_natCast]; omega) | omega)]; first | assumption | simp_all); first | assumption | omega | (simp_all <;> omega)
  )
theorem _tactus_postcondition_runtime.find_cancellation_exec_at_runtime_100_9_18 (w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global)) (h_req0 : seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1) :
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__1 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    ¬(/- @rust:src/runtime.rs:102:8 -/ tmp__1 ≤ 1) → (∀ (i : Nat), 0 ≤ i ∧ i < usize_hi → (/- @rust:src/runtime.rs:111:13 -/ let tmp__ := 0;
    let tmp___1 := i;
    let tmp___2 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w - 1;
    tmp__ ≤ tmp___1 ∧ tmp___1 ≤ tmp___2) → /- @rust:src/runtime.rs:112:13 -/ seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) < usize_hi - 1 → /- @rust:src/runtime.rs:113:13 -/ reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) 0 = reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) i → (let _tactus_d_old_0_0 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w - i;
    let tmp__4 := i;
    0 ≤ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w ∧ std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w < usize_hi → (let tmp__3 := std_specs.vec.spec_vec_len runtime.RuntimeSymbol alloc.Global w;
    0 ≤ tmp__3 - 1 ∧ tmp__3 - 1 < usize_hi → 0 ≤ tmp__3 - 1 ∧ tmp__3 - 1 < usize_hi → tmp__4 < tmp__3 - 1 → i + 1 < seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) → i + 1 < seq.Seq.len runtime.RuntimeSymbol ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol)) → (let tmp__5 := Tactus.Ref.mk (seq.Seq.index runtime.RuntimeSymbol (view.View.view w) (Int.ofNat i));
    let tmp__9 := tmp__5;
    let tmp__6 := w.deref;
    0 ≤ i + 1 ∧ i + 1 < usize_hi → 0 ≤ i + 1 ∧ i + 1 < usize_hi → (let tmp__8 := i + 1;
    let tmp__7 := Tactus.Ref.mk (seq.Seq.index runtime.RuntimeSymbol (view.View.view (Tactus.Ref.mk tmp__6)) (Int.ofNat tmp__8));
    let tmp__10 := symbol.is_inverse_pair (runtime.runtime_symbol_view tmp__9.deref) (runtime.runtime_symbol_view tmp__7.deref);
    /- @rust:src/runtime.rs:120:12 -/ tmp__10 → reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) i = i → reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) i = i → (let out := i;
    /- @rust:src/runtime.rs:100:9 -/ out = reduction.find_cancellation_from (runtime.runtime_word_view ((view.View.view ((w : Tactus.Ref (vec.Vec runtime.RuntimeSymbol alloc.Global))) : seq.Seq runtime.RuntimeSymbol))) 0))))))) := by
  (
    have _tactus_bc_0 := @seq.axiom_seq_index_decreases
    have _tactus_bc_1 := @seq.axiom_seq_subrange_decreases
    have _tactus_bc_2 := @seq.axiom_seq_empty
    have _tactus_bc_3 := @seq.axiom_seq_new_len
    have _tactus_bc_4 := @seq.axiom_seq_new_index
    have _tactus_bc_5 := @seq.axiom_seq_push_len
    have _tactus_bc_6 := @seq.axiom_seq_push_index_same
    have _tactus_bc_7 := @seq.axiom_seq_push_index_different
    have _tactus_bc_8 := @seq.axiom_seq_update_len
    have _tactus_bc_9 := @seq.axiom_seq_update_same
    have _tactus_bc_10 := @seq.axiom_seq_update_different
    have _tactus_bc_11 := @seq.axiom_seq_ext_equal
    have _tactus_bc_12 := @seq.axiom_seq_ext_equal_deep
    have _tactus_bc_13 := @seq.axiom_seq_subrange_len
    have _tactus_bc_14 := @seq.axiom_seq_subrange_index
    have _tactus_bc_15 := @seq.lemma_seq_two_subranges_index
    have _tactus_bc_16 := @seq.axiom_seq_add_len
    have _tactus_bc_17 := @seq.axiom_seq_add_index1
    have _tactus_bc_18 := @seq.axiom_seq_add_index2
    have _tactus_bc_19 := @seq_lib.impl__0.add_empty_left
    have _tactus_bc_20 := @seq_lib.impl__0.add_empty_right
    have _tactus_bc_21 := @seq_lib.impl__0.push_distributes_over_add
    have _tactus_bc_22 := @set.axiom_set_empty
    have _tactus_bc_23 := @set.axiom_set_insert_same
    have _tactus_bc_24 := @set.axiom_set_insert_different
    have _tactus_bc_25 := @set.axiom_set_remove_same
    have _tactus_bc_26 := @set.axiom_set_remove_insert
    have _tactus_bc_27 := @set.axiom_set_remove_different
    have _tactus_bc_28 := @set.axiom_set_complement
    have _tactus_bc_29 := @set.axiom_set_ext_equal
    have _tactus_bc_30 := @set.axiom_set_ext_equal_deep
    have _tactus_bc_31 := @set.axiom_set_empty_finite
    have _tactus_bc_32 := @set.axiom_set_insert_finite
    have _tactus_bc_33 := @set.axiom_set_remove_finite
    have _tactus_bc_34 := @set_lib.lemma_set_subset_finite
    have _tactus_bc_35 := @array.array_len_matches_n
    have _tactus_bc_36 := @array.lemma_array_index
    have _tactus_bc_37 := @array.axiom_array_ext_equal
    have _tactus_bc_38 := @array.axiom_array_has_resolved
    have _tactus_bc_39 := @std_specs.vec.axiom_spec_len
    have _tactus_bc_40 := @std_specs.vec.axiom_vec_index_decreases
    have _tactus_bc_41 := @std_specs.vec.vec_clone_deep_view_proof
    have _tactus_bc_42 := @std_specs.vec.axiom_vec_has_resolved
    have _tactus_bc_43 := @std_specs.vec.axiom_vec_decreases_to_view
  ) <;> tactus_auto
