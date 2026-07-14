import TactusDefs_lib_exec
import lib__expr_mirror_kernel_computes
import lib__skeleton_kernel_computes
import lib__seq_size_unfolds
import lib__probe_goal_eq_leaf
import lib__probe_goal_eq_nested
import lib__probe_goals_eq_lit
import lib__probe_close
import lib__probe_close_e
import lib__probe_wp_stm
import lib__probe_ref_wp
import lib__ref_wp_seed_and_assert
import lib__ref_wp_seq_threads_frame
import lib__ref_wp_add_capped_seed_spine
import lib__ref_wp_ret_return_binding
import lib__ref_wp_sum_to_loop
import lib__ref_wp_nested_loop_nonleading
import lib__ref_wp_if_fallthrough_divergence
import lib__ref_wp_if_twoway_join
import lib__ref_wp_call_pass_through
import lib__goal_eq_strictness
import lib__leafe_goal_bridge_kernel_computes
import lib__amended_shapes_kernel_compute
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable def lib.expr_mirror_kernel_computes_closed : lib.expr_mirror_kernel_computes_stmt :=
  lib.expr_mirror_kernel_computes
#tactus_check_axioms lib.expr_mirror_kernel_computes_closed []
noncomputable def lib.skeleton_kernel_computes_closed : lib.skeleton_kernel_computes_stmt :=
  lib.skeleton_kernel_computes
#tactus_check_axioms lib.skeleton_kernel_computes_closed []
noncomputable def lib.seq_size_unfolds_closed : lib.seq_size_unfolds_stmt :=
  lib.seq_size_unfolds
#tactus_check_axioms lib.seq_size_unfolds_closed []
noncomputable def lib.probe_goal_eq_leaf_closed : lib.probe_goal_eq_leaf_stmt :=
  lib.probe_goal_eq_leaf
#tactus_check_axioms lib.probe_goal_eq_leaf_closed []
noncomputable def lib.probe_goal_eq_nested_closed : lib.probe_goal_eq_nested_stmt :=
  lib.probe_goal_eq_nested
#tactus_check_axioms lib.probe_goal_eq_nested_closed []
noncomputable def lib.probe_goals_eq_lit_closed : lib.probe_goals_eq_lit_stmt :=
  lib.probe_goals_eq_lit
#tactus_check_axioms lib.probe_goals_eq_lit_closed []
noncomputable def lib.probe_close_closed : lib.probe_close_stmt :=
  lib.probe_close
#tactus_check_axioms lib.probe_close_closed []
noncomputable def lib.probe_close_e_closed : lib.probe_close_e_stmt :=
  lib.probe_close_e
#tactus_check_axioms lib.probe_close_e_closed []
noncomputable def lib.probe_wp_stm_closed : lib.probe_wp_stm_stmt :=
  lib.probe_wp_stm
#tactus_check_axioms lib.probe_wp_stm_closed []
noncomputable def lib.probe_ref_wp_closed : lib.probe_ref_wp_stmt :=
  lib.probe_ref_wp
#tactus_check_axioms lib.probe_ref_wp_closed []
noncomputable def lib.ref_wp_seed_and_assert_closed : lib.ref_wp_seed_and_assert_stmt :=
  lib.ref_wp_seed_and_assert
#tactus_check_axioms lib.ref_wp_seed_and_assert_closed []
noncomputable def lib.ref_wp_seq_threads_frame_closed : lib.ref_wp_seq_threads_frame_stmt :=
  lib.ref_wp_seq_threads_frame
#tactus_check_axioms lib.ref_wp_seq_threads_frame_closed []
noncomputable def lib.ref_wp_add_capped_seed_spine_closed : lib.ref_wp_add_capped_seed_spine_stmt :=
  lib.ref_wp_add_capped_seed_spine
#tactus_check_axioms lib.ref_wp_add_capped_seed_spine_closed []
noncomputable def lib.ref_wp_ret_return_binding_closed : lib.ref_wp_ret_return_binding_stmt :=
  lib.ref_wp_ret_return_binding
#tactus_check_axioms lib.ref_wp_ret_return_binding_closed []
noncomputable def lib.ref_wp_sum_to_loop_closed : lib.ref_wp_sum_to_loop_stmt :=
  lib.ref_wp_sum_to_loop
#tactus_check_axioms lib.ref_wp_sum_to_loop_closed []
noncomputable def lib.ref_wp_nested_loop_nonleading_closed : lib.ref_wp_nested_loop_nonleading_stmt :=
  lib.ref_wp_nested_loop_nonleading
#tactus_check_axioms lib.ref_wp_nested_loop_nonleading_closed []
noncomputable def lib.ref_wp_if_fallthrough_divergence_closed : lib.ref_wp_if_fallthrough_divergence_stmt :=
  lib.ref_wp_if_fallthrough_divergence
#tactus_check_axioms lib.ref_wp_if_fallthrough_divergence_closed []
noncomputable def lib.ref_wp_if_twoway_join_closed : lib.ref_wp_if_twoway_join_stmt :=
  lib.ref_wp_if_twoway_join
#tactus_check_axioms lib.ref_wp_if_twoway_join_closed []
noncomputable def lib.ref_wp_call_pass_through_closed : lib.ref_wp_call_pass_through_stmt :=
  lib.ref_wp_call_pass_through
#tactus_check_axioms lib.ref_wp_call_pass_through_closed []
noncomputable def lib.goal_eq_strictness_closed : lib.goal_eq_strictness_stmt :=
  lib.goal_eq_strictness
#tactus_check_axioms lib.goal_eq_strictness_closed []
noncomputable def lib.leafe_goal_bridge_kernel_computes_closed : lib.leafe_goal_bridge_kernel_computes_stmt :=
  lib.leafe_goal_bridge_kernel_computes
#tactus_check_axioms lib.leafe_goal_bridge_kernel_computes_closed []
noncomputable def lib.amended_shapes_kernel_compute_closed : lib.amended_shapes_kernel_compute_stmt :=
  lib.amended_shapes_kernel_compute
#tactus_check_axioms lib.amended_shapes_kernel_compute_closed []
