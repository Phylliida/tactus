//! Golden tripwire for the bootstrap mirror types (tactus-core, N2):
//! `covered_by_tactus_core_stage_a` must match EVERY `vir::sst::StmX`
//! variant — when vir::sst grows one, this file stops compiling, which
//! is the loud reminder to extend `tactus-core/lib.rs`'s `StmData` (or
//! record the variant as deliberately uncovered) and the serializer.
//! See DESIGN-bootstrap.md §12 N2.
//!
//! Scope note: this tripwire tracks StmX *variant* coverage only. The
//! stage-A *field* shapes within the covered variants (If's ¬cond leaf,
//! Loop's neg_cond/binders, Call's dest/dest_typ, Return's ensures
//! leaves) were enriched by N2.1 — specced in DESIGN-W2-refwp.md §0/§2.1
//! and pinned by `tactus-core/lib.rs`'s in-crate `decide` sanity proofs,
//! not here (no StmX is constructed below).
//!
//! Milestone-D column (endgame §5, bootstrap-77): `in_w5_model` is the
//! SECOND exhaustive match — does the mirrored construct have a
//! `wp_stm_sound` arm (the operational-soundness claim covers it)?
//! Growing the mirrored set without the model is a REVIEWED decision:
//! this fn is where it becomes compile-visible.
//! `VERIFICATION-PATH.md` §4 rung 5's scope paragraph states "the model
//! covers exactly the in-model column" — keep them synchronized.

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
        vir::sst::StmX::Return { .. } => true,    // StmData::Ret (+ IfCtor/If forks, b77)
        vir::sst::StmX::If(..) => true,           // StmData::If
        vir::sst::StmX::Loop { .. } => true,      // StmData::Loop
        vir::sst::StmX::Block(..) => true,        // StmData::Seq/Skip (right-nested)
        // Mode-split (a variant-level bool cannot express it):
        // NonLinear → StmData::AssertQueryNl (b69); Tactus →
        // StmData::AssertQueryTactus / prefix-Skip (b77); BitVector is
        // unreachable at SST (ast_to_sst converts to AssertBitVector).
        vir::sst::StmX::AssertQuery { .. } => true,
        // Deliberately uncovered (stage B+):
        vir::sst::StmX::AssertBitVector { .. } => false,
        vir::sst::StmX::AssertCompute(..) => false,
        vir::sst::StmX::Fuel(..) => false,
        vir::sst::StmX::RevealString(..) => false,
        vir::sst::StmX::BreakOrContinue { .. } => false,
        vir::sst::StmX::OpenInvariant(..) => false,
        vir::sst::StmX::ClosureInner { .. } => false,
        vir::sst::StmX::Air(..) => false,
    }
}

/// Milestone-D in-model column: every `true` here asserts the mirrored
/// construct has a `wp_stm_sound` arm in tactus-core (the W5 claim
/// covers it). As of bootstrap-77 EVERY mirrored StmData constructor is
/// in the model (Assert/Assume/Assign[H/R]/Call/DeadEnd/AssertQueryNl/
/// AssertQueryTactus/Ret/If/IfCtor/Loop/Skip/Seq — `wp_stm_sound` is
/// total on StmData), so this match mirrors the one above. If a future
/// mirror arm lands WITHOUT a soundness arm, flip its row to false HERE
/// and census it out of the rung-5 scope statement — that divergence is
/// the thing this column exists to make visible.
#[allow(dead_code)]
fn in_w5_model(s: &vir::sst::StmX) -> bool {
    match s {
        vir::sst::StmX::Call { .. } => true,
        vir::sst::StmX::Assert(..) => true,
        vir::sst::StmX::Assume(..) => true,
        vir::sst::StmX::Assign { .. } => true,
        vir::sst::StmX::DeadEnd(..) => true,
        vir::sst::StmX::Return { .. } => true,
        vir::sst::StmX::If(..) => true,
        vir::sst::StmX::Loop { .. } => true,
        vir::sst::StmX::Block(..) => true,
        vir::sst::StmX::AssertQuery { .. } => true,
        vir::sst::StmX::AssertBitVector { .. } => false,
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
    // The fns above compiling exhaustively ARE the tripwire; this test
    // just keeps the file visibly in the run (no StmX is constructed —
    // the variants carry Arc'd payloads with no cheap dummies).
    let _ = covered_by_tactus_core_stage_a as fn(&vir::sst::StmX) -> bool;
    let _ = in_w5_model as fn(&vir::sst::StmX) -> bool;
}
