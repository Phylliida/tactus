import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_assert_poly_ring.lemma_pmul_empty_right_at_poly_ring_493_16_3 (T : Type) [lib.traits.ring.Ring T] [Nonempty T] (q : lib.seq.Seq T) :
    let decrease_init0 := Int.ofNat (lib.seq.Seq.len T q);
    ¬(lib.seq.Seq.len T q = 0) → (let t := lib.seq.Seq.subrange T q 1 (Int.ofNat (lib.seq.Seq.len T q));
                                                                     let tmp__1 := lib.poly.pmul T q (lib.seq.Seq.empty T) = lib.poly.padd T (lib.poly.scale T (lib.seq.Seq.index T q 0) (lib.seq.Seq.empty T)) (lib.poly.shiftk T (lib.poly.pmul T t (lib.seq.Seq.empty T)) 1);
                                                                     tmp__1) := by
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
  intro _ h_nonempty
  intro t
  rw [lib.poly.pmul]
  simp only [h_nonempty, if_false, reduceIte]
  rfl
