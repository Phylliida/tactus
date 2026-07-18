import TactusDefs_test_crate_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_clone_field_index_at_test_20_13_4 (h : Tactus.Ref test_crate.Holder) (i : Nat) (h_i_bound : 0 ≤ i ∧ i < usize_hi) (h_req0 : i < test_crate.seq.Seq.len (test_crate.vec.Vec Int test_crate.alloc.Global) ((test_crate.view.View.view ((Tactus.Ref.mk h.deref.imgs : Tactus.Ref (test_crate.vec.Vec (test_crate.vec.Vec Int test_crate.alloc.Global) test_crate.alloc.Global))) : test_crate.seq.Seq (test_crate.vec.Vec Int test_crate.alloc.Global)))) (tmp__2 : test_crate.vec.Vec (test_crate.vec.Vec Int test_crate.alloc.Global) test_crate.alloc.Global) (_h_tmp__2_hoist1 : tmp__2 = h.deref.imgs) (tmp__1 : Tactus.Ref (test_crate.vec.Vec Int test_crate.alloc.Global)) (_h_tmp__1_hoist1 : tmp__1 = Tactus.Ref.mk (test_crate.seq.Seq.index (test_crate.vec.Vec Int test_crate.alloc.Global) (test_crate.view.View.view (Tactus.Ref.mk tmp__2)) (Int.ofNat i))) (tmp__3 : test_crate.vec.Vec Int test_crate.alloc.Global) (_h_hoist_1 : test_crate.std_specs.vec.spec_vec_len Int test_crate.alloc.Global (Tactus.Ref.mk tmp__3) = test_crate.std_specs.vec.spec_vec_len Int test_crate.alloc.Global tmp__1 ∧ (∀ (i : Int), 0 ≤ i ∧ i < test_crate.std_specs.vec.spec_vec_len Int test_crate.alloc.Global tmp__1 → test_crate.pervasive.cloned Int (test_crate.seq.Seq.index Int (test_crate.view.View.view tmp__1) i) (test_crate.seq.Seq.index Int (test_crate.view.View.view (Tactus.Ref.mk tmp__3)) i)) ∧ test_crate.std_specs.vec.vec_clone_trigger Int test_crate.alloc.Global tmp__1.deref tmp__3 ∧ (test_crate.view.View.view tmp__1 = test_crate.view.View.view (Tactus.Ref.mk tmp__3) → test_crate.view.View.view tmp__1 = test_crate.view.View.view (Tactus.Ref.mk tmp__3))) (out : test_crate.vec.Vec Int test_crate.alloc.Global) (_h_clone_sem : ∀ (a b : Int), test_crate.pervasive.strictly_cloned Int a b → a = b) (_h_out_hoist1 : out = tmp__3) :
    ((test_crate.view.View.view ((Tactus.Ref.mk out : Tactus.Ref (test_crate.vec.Vec Int test_crate.alloc.Global))) : test_crate.seq.Seq Int)) = ((test_crate.view.View.view ((Tactus.Ref.mk (test_crate.seq.Seq.index (test_crate.vec.Vec Int test_crate.alloc.Global) ((test_crate.view.View.view ((Tactus.Ref.mk h.deref.imgs : Tactus.Ref (test_crate.vec.Vec (test_crate.vec.Vec Int test_crate.alloc.Global) test_crate.alloc.Global))) : test_crate.seq.Seq (test_crate.vec.Vec Int test_crate.alloc.Global))) (Int.ofNat i)) : Tactus.Ref (test_crate.vec.Vec Int test_crate.alloc.Global))) : test_crate.seq.Seq Int)) := by
  -- grant nothing else; ext axiom + spec_len axiom + cloned unfold
  have hext := @test_crate.seq.axiom_seq_ext_equal
  have hlen := @test_crate.std_specs.vec.axiom_spec_len
  subst _h_out_hoist1 _h_tmp__2_hoist1 _h_tmp__1_hoist1
  obtain ⟨h_len_eq, h_ptwise, h_trig, h_bridge⟩ := _h_hoist_1
  rw [hext]
  constructor
  · rw [hlen, hlen] at h_len_eq
    exact h_len_eq
  · intro j hj
    have hj' := h_ptwise j
    rw [hlen] at hj'
    have hcl := hj' ⟨hj.1, by
      have := h_len_eq
      rw [hlen, hlen] at this
      omega⟩
    unfold test_crate.pervasive.cloned at hcl
    rcases hcl with hstrict | heq
    · exact (_h_clone_sem _ _ hstrict).symm
    · exact heq.symm
