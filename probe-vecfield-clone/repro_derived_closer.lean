import TactusDefs_test_crate_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_clone_field_index_at_test_20_13_4 (h : Tactus.Ref test_crate.Holder) (i : Nat) (h_i_bound : 0 ≤ i ∧ i < usize_hi) (h_req0 : i < test_crate.seq.Seq.len (test_crate.vec.Vec Int test_crate.alloc.Global) ((test_crate.view.View.view ((Tactus.Ref.mk h.deref.imgs : Tactus.Ref (test_crate.vec.Vec (test_crate.vec.Vec Int test_crate.alloc.Global) test_crate.alloc.Global))) : test_crate.seq.Seq (test_crate.vec.Vec Int test_crate.alloc.Global)))) (tmp__2 : test_crate.vec.Vec (test_crate.vec.Vec Int test_crate.alloc.Global) test_crate.alloc.Global) (_h_tmp__2_hoist1 : tmp__2 = h.deref.imgs) (tmp__1 : Tactus.Ref (test_crate.vec.Vec Int test_crate.alloc.Global)) (_h_tmp__1_hoist1 : tmp__1 = Tactus.Ref.mk (test_crate.seq.Seq.index (test_crate.vec.Vec Int test_crate.alloc.Global) (test_crate.view.View.view (Tactus.Ref.mk tmp__2)) (Int.ofNat i))) (tmp__3 : test_crate.vec.Vec Int test_crate.alloc.Global) (_h_hoist_1 : test_crate.std_specs.vec.spec_vec_len Int test_crate.alloc.Global (Tactus.Ref.mk tmp__3) = test_crate.std_specs.vec.spec_vec_len Int test_crate.alloc.Global tmp__1 ∧ (∀ (i : Int), 0 ≤ i ∧ i < test_crate.std_specs.vec.spec_vec_len Int test_crate.alloc.Global tmp__1 → test_crate.pervasive.cloned Int (test_crate.seq.Seq.index Int (test_crate.view.View.view tmp__1) i) (test_crate.seq.Seq.index Int (test_crate.view.View.view (Tactus.Ref.mk tmp__3)) i)) ∧ test_crate.std_specs.vec.vec_clone_trigger Int test_crate.alloc.Global tmp__1.deref tmp__3 ∧ (test_crate.view.View.view tmp__1 = test_crate.view.View.view (Tactus.Ref.mk tmp__3) → test_crate.view.View.view tmp__1 = test_crate.view.View.view (Tactus.Ref.mk tmp__3))) (out : test_crate.vec.Vec Int test_crate.alloc.Global) (_h_clone_sem : ∀ (a b : Int), test_crate.pervasive.strictly_cloned Int a b → a = b) (_h_out_hoist1 : out = tmp__3) :
    ((test_crate.view.View.view ((Tactus.Ref.mk out : Tactus.Ref (test_crate.vec.Vec Int test_crate.alloc.Global))) : test_crate.seq.Seq Int)) = ((test_crate.view.View.view ((Tactus.Ref.mk (test_crate.seq.Seq.index (test_crate.vec.Vec Int test_crate.alloc.Global) ((test_crate.view.View.view ((Tactus.Ref.mk h.deref.imgs : Tactus.Ref (test_crate.vec.Vec (test_crate.vec.Vec Int test_crate.alloc.Global) test_crate.alloc.Global))) : test_crate.seq.Seq (test_crate.vec.Vec Int test_crate.alloc.Global))) (Int.ofNat i)) : Tactus.Ref (test_crate.vec.Vec Int test_crate.alloc.Global))) : test_crate.seq.Seq Int)) := by
  (
    have _tactus_bc_0 := @test_crate.seq.axiom_seq_index_decreases
    have _tactus_bc_1 := @test_crate.seq.axiom_seq_new_len
    have _tactus_bc_2 := @test_crate.seq.axiom_seq_new_index
    have _tactus_bc_3 := @test_crate.seq.axiom_seq_ext_equal
    have _tactus_bc_4 := @test_crate.seq.axiom_seq_ext_equal_deep
    have _tactus_bc_5 := @test_crate.set.axiom_set_empty
    have _tactus_bc_6 := @test_crate.set.axiom_set_insert_same
    have _tactus_bc_7 := @test_crate.set.axiom_set_insert_different
    have _tactus_bc_8 := @test_crate.set.axiom_set_remove_same
    have _tactus_bc_9 := @test_crate.set.axiom_set_remove_insert
    have _tactus_bc_10 := @test_crate.set.axiom_set_remove_different
    have _tactus_bc_11 := @test_crate.set.axiom_set_complement
    have _tactus_bc_12 := @test_crate.set.axiom_set_ext_equal
    have _tactus_bc_13 := @test_crate.set.axiom_set_ext_equal_deep
    have _tactus_bc_14 := @test_crate.set.axiom_set_empty_finite
    have _tactus_bc_15 := @test_crate.set.axiom_set_insert_finite
    have _tactus_bc_16 := @test_crate.set.axiom_set_remove_finite
    have _tactus_bc_17 := @test_crate.set_lib.lemma_set_subset_finite
    have _tactus_bc_18 := @test_crate.std_specs.vec.axiom_spec_len
    have _tactus_bc_19 := @test_crate.std_specs.vec.axiom_vec_index_decreases
    have _tactus_bc_20 := @test_crate.std_specs.vec.vec_clone_deep_view_proof
    have _tactus_bc_21 := @test_crate.std_specs.vec.axiom_vec_has_resolved
    have _tactus_bc_22 := @test_crate.std_specs.vec.axiom_vec_decreases_to_view
  ) <;> (
    first | rfl | decide | omega | (first | rfl | decide | omega) | (simp_all only [Classical.not_forall, Decidable.not_not, Int.add_emod_left, Int.cast_ofNat_Int, Int.natCast_add, Int.neg_add_emod_self, Int.ofNat_eq_coe, Int.ofNat_zero_le, Int.sub_zero, Int.toNat_natCast_add_one, Int.zero_add, Int.zero_sub, Int.mul_add, Int.add_mul, Int.toNat_zero, Int.toNat_one, Int.add_sub_cancel, Nat.add_le_add_iff_right, Nat.add_left_cancel_iff, Nat.add_zero, Nat.le_add_left, Nat.le_add_right, Nat.le_refl, Nat.not_le, Nat.not_lt, Nat.reduceLeDiff, Nat.sub_le_iff_le_add, Nat.zero_add, Nat.zero_le, Nat.mul_add, Nat.add_mul, Nat.add_sub_cancel, and_imp, and_self, and_true, eq_iff_iff, forall_const, forall_eq, ge_iff_le, gt_iff_lt, iff_true, imp_false, imp_self, implies_true, not_and, not_exists, not_false_eq_true, Classical.not_imp, not_or, not_true_eq_false, true_and] <;> omega) | (intros; simp_all +zetaDelta only [Classical.not_forall, Decidable.not_not, Int.add_emod_left, Int.cast_ofNat_Int, Int.natCast_add, Int.neg_add_emod_self, Int.ofNat_eq_coe, Int.ofNat_zero_le, Int.sub_zero, Int.toNat_natCast_add_one, Int.zero_add, Int.zero_sub, Int.mul_add, Int.add_mul, Int.toNat_zero, Int.toNat_one, Int.add_sub_cancel, Nat.add_le_add_iff_right, Nat.add_left_cancel_iff, Nat.add_zero, Nat.le_add_left, Nat.le_add_right, Nat.le_refl, Nat.not_le, Nat.not_lt, Nat.reduceLeDiff, Nat.sub_le_iff_le_add, Nat.zero_add, Nat.zero_le, Nat.mul_add, Nat.add_mul, Nat.add_sub_cancel, and_imp, and_self, and_true, eq_iff_iff, forall_const, forall_eq, ge_iff_le, gt_iff_lt, iff_true, imp_false, imp_self, implies_true, not_and, not_exists, not_false_eq_true, Classical.not_imp, not_or, not_true_eq_false, true_and, true_or, or_true, if_true, if_false, reduceCtorEq, test_crate.pervasive.cloned, test_crate.std_specs.vec.vec_clone_trigger] <;> omega)
  )
