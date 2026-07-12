//! Golden tripwire for the bootstrap mirror types (tactus-core, N2):
//! `covered_by_tactus_core_stage_a` must match EVERY `vir::sst::StmX`
//! variant — when vir::sst grows one, this file stops compiling, which
//! is the loud reminder to extend `tactus-core/lib.rs`'s `StmData` (or
//! record the variant as deliberately uncovered) and the serializer.
//! See DESIGN-bootstrap.md §12 N2.

/// Never called — the exhaustive match IS the test (compile-time).
#[allow(dead_code)]
fn covered_by_tactus_core_stage_a(s: &vir::sst::StmX) -> bool {
    match s {
        // Covered by tactus-core StmData (stage A):
        vir::sst::StmX::Call { .. } => true,      // StmData::Call (contract view)
        vir::sst::StmX::Assert(..) => true,       // StmData::Assert
        vir::sst::StmX::Assume(..) => true,       // StmData::Assume
        vir::sst::StmX::Assign { .. } => true,    // StmData::Assign
        vir::sst::StmX::DeadEnd(..) => true,      // StmData::DeadEnd
        vir::sst::StmX::Return { .. } => true,    // StmData::Ret
        vir::sst::StmX::If(..) => true,           // StmData::If
        vir::sst::StmX::Loop { .. } => true,      // StmData::Loop
        vir::sst::StmX::Block(..) => true,        // StmData::Seq/Skip (right-nested)
        // Deliberately uncovered (stage B+):
        vir::sst::StmX::AssertBitVector { .. } => false,
        vir::sst::StmX::AssertQuery { .. } => false,
        vir::sst::StmX::AssertCompute(..) => false,
        vir::sst::StmX::Fuel(..) => false,
        vir::sst::StmX::RevealString(..) => false,
        vir::sst::StmX::BreakOrContinue { .. } => false,
        vir::sst::StmX::OpenInvariant(..) => false,
        vir::sst::StmX::ClosureInner { .. } => false,
        vir::sst::StmX::Air(..) => false,
    }
}

#[test]
fn stage_a_coverage_is_pinned() {
    // The fn above compiling exhaustively IS the tripwire; this test
    // just keeps the file visibly in the run (no StmX is constructed —
    // the variants carry Arc'd payloads with no cheap dummies).
    let _ = covered_by_tactus_core_stage_a as fn(&vir::sst::StmX) -> bool;
}
