import TactusDefs_lib_exec
import lib__skeleton_kernel_computes
import lib__seq_size_unfolds
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable def lib.skeleton_kernel_computes_closed : lib.skeleton_kernel_computes_stmt :=
  lib.skeleton_kernel_computes
#tactus_check_axioms lib.skeleton_kernel_computes_closed []
noncomputable def lib.seq_size_unfolds_closed : lib.seq_size_unfolds_stmt :=
  lib.seq_size_unfolds
#tactus_check_axioms lib.seq_size_unfolds_closed []
