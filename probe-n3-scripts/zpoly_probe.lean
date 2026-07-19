import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_assert_poly_mul.lemma_zpoly_empty_at_poly_mul_29_27_2 (T : Type) [lib.traits.ring.Ring T] [Nonempty T] (i : Int) (_h_hoist_1 : True) (_h_hoist_2 : True) (tmp__1 : T) (_h_tmp__1_hoist1 : tmp__1 = ((lib.traits.additive_commutative_monoid.AdditiveCommutativeMonoid.zero (Self := (T)) : T))) (_tactus_ret_1 : Unit) (_h_hoist_3 : (lib.traits.equivalence.Equivalence.eqv tmp__1 tmp__1 : Prop)) :
    (lib.traits.equivalence.Equivalence.eqv (lib.poly.coeff T (lib.seq.Seq.empty T) i) ((lib.traits.additive_commutative_monoid.AdditiveCommutativeMonoid.zero (Self := (T)) : T)) : Prop) := by
  have _tactus_bc_0 := @lib.seq.axiom_seq_index_decreases
  have _tactus_bc_1 := @lib.seq.axiom_seq_subrange_decreases
  have _tactus_bc_2 := @lib.seq.axiom_seq_empty
  have _tactus_bc_3 := @lib.seq.axiom_seq_new_len
  have _tactus_bc_4 := @lib.seq.axiom_seq_new_index
  have _tactus_bc_5 := @lib.seq.axiom_seq_push_len
  have _tactus_bc_6 := @lib.seq.axiom_seq_push_index_same
  have _tactus_bc_7 := @lib.seq.axiom_seq_push_index_different
  have _tactus_bc_8 := @lib.seq.axiom_seq_ext_equal
  have _tactus_bc_9 := @lib.seq.axiom_seq_ext_equal_deep
  have _tactus_bc_10 := @lib.seq.axiom_seq_subrange_len
  have _tactus_bc_11 := @lib.seq.axiom_seq_subrange_index
  have _tactus_bc_12 := @lib.seq.lemma_seq_two_subranges_index
  have _tactus_bc_0 := @lib.seq.axiom_seq_index_decreases
  have _tactus_bc_1 := @lib.seq.axiom_seq_subrange_decreases
  have _tactus_bc_2 := @lib.seq.axiom_seq_empty
  have _tactus_bc_3 := @lib.seq.axiom_seq_new_len
  have _tactus_bc_4 := @lib.seq.axiom_seq_new_index
  have _tactus_bc_5 := @lib.seq.axiom_seq_push_len
  have _tactus_bc_6 := @lib.seq.axiom_seq_push_index_same
  have _tactus_bc_7 := @lib.seq.axiom_seq_push_index_different
  have _tactus_bc_8 := @lib.seq.axiom_seq_ext_equal
  have _tactus_bc_9 := @lib.seq.axiom_seq_ext_equal_deep
  have _tactus_bc_10 := @lib.seq.axiom_seq_subrange_len
  have _tactus_bc_11 := @lib.seq.axiom_seq_subrange_index
  have _tactus_bc_12 := @lib.seq.lemma_seq_two_subranges_index
  subst _h_tmp__1_hoist1
  simp only [lib.poly.coeff]
  split
  · -- 0 <= i < len(empty): contradiction via len(empty)=0
    rename_i hcond
    have hlen := lib.seq.axiom_seq_empty T
    omega
  · exact _h_hoist_3
