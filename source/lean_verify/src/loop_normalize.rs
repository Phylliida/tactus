//! Loop-condition normalization (decision #2, 2026-07-26): rewrite
//! every `while`-with-SETUP loop — `StmX::Loop { cond: Some((setup,
//! exp)), .. }` where `setup` is a non-empty statement — into the
//! loop+break form Verus itself lowers complex whiles to:
//!
//! ```text
//! loop { <setup…>; if !exp { break; } <body…> }
//! ```
//!
//! with the original `(setup, exp)` moved to `original_cond` so
//! `build_wp_loop` can still wrap the post-loop continuation with the
//! `setup; ¬exp` exit facts.
//!
//! ## Why
//!
//! The cond-slot setup `Stm` was invisible to every body walker —
//! `collect_borrow_mut_links`, `collect_modifications`, iteration
//! havoc — because they all (correctly) walk the loop BODY and nothing
//! else. The 2026-07-25 audit turned that structural blind spot into a
//! verified-false-ensures soundness hole (`while set_zero(&mut y) {}`
//! then `y == 5` post-loop VERIFIED; interim fix was the
//! `cond_setup_user_mutation` reject gate, now retired). Normalizing
//! to one loop encoding means one set of walkers sees everything, by
//! construction — the bug class is structural, so the fix is too.
//!
//! Empty-setup whiles keep `cond: Some`: their condition is a pure
//! `Exp` with no statements for a walker to miss, and `walk_loop`
//! renders the classical cond hypotheses for them.
//!
//! ## Soundness of the synthesized break
//!
//! Verus's own invariant for `cond: Some` loops (vir `sst.rs`, Loop
//! doc): "simple while loop … no break statements". The synthesized
//! unlabeled `break` therefore becomes the loop's ONLY exit, which is
//! exactly the premise `build_wp_loop`'s exit-fact wrap re-checks via
//! `count_breaks_targeting_this_loop == 1`.
//!
//! ## Cert lane
//!
//! The bootstrap cert serializer snapshots the RAW `check.body` and
//! the reference WP recomputes the walker's pre-passes from the
//! literal (`sst_serialize.rs` header, anchor #1). Like the mut-ref
//! rewrite before it, this pre-pass must eventually be mirrored
//! refWp-side; until then, fns containing setup-carrying whiles
//! honestly fail cert certification (they had no certs before —
//! these loop shapes were rejected outright until 2026-07-25).

use std::sync::Arc;

use vir::ast::{SpannedTyped, TypX, UnaryOp};
use vir::def::Spanned;
use vir::sst::{Exp, ExpX, Stm, StmX};

/// Rewrite all setup-carrying `while` loops in `stm` (recursively,
/// innermost-first via the post-order visitor) into the break form.
/// Runs as a pre-pass on the OWNED body tree in
/// `exec_fn_theorems_to_ast`, BEFORE the mut-ref rewrite and the
/// BorrowMut/modification collectors — so by the time anything walks
/// the body, the former cond statements are ordinary body statements.
pub(crate) fn normalize_setup_loops(stm: &Stm) -> Stm {
    vir::sst_visitor::map_stm_visitor(stm, &mut |s: &Stm| {
        Ok(match &s.x {
            StmX::Loop {
                loop_isolation,
                is_for_loop,
                id,
                label,
                cond: Some((setup, exp)),
                original_cond,
                body,
                invs,
                decrease,
                typ_inv_vars,
                modified_vars,
                pre_modified_params,
            } if !matches!(&setup.x, StmX::Block(ss) if ss.is_empty()) => {
                // `cond: Some` loops carry no breaks (Verus invariant),
                // so they also carry no Verus-preserved original_cond.
                debug_assert!(
                    original_cond.is_none(),
                    "cond:Some loop with original_cond already set — \
                     Verus encoding-shape change worth investigating"
                );
                // Synthesized guard: `if !exp { break; }`. The
                // unlabeled break targets the innermost loop — this
                // one, since it sits at the transformed body's top
                // level.
                let not_exp: Exp = SpannedTyped::new(
                    &exp.span,
                    &Arc::new(TypX::Bool),
                    ExpX::Unary(UnaryOp::Not, exp.clone()),
                );
                let break_stm: Stm = Spanned::new(
                    exp.span.clone(),
                    StmX::BreakOrContinue { label: None, is_break: true },
                );
                let guard: Stm =
                    Spanned::new(exp.span.clone(), StmX::If(not_exp, break_stm, None));
                let new_body: Stm = Spanned::new(
                    body.span.clone(),
                    StmX::Block(Arc::new(vec![setup.clone(), guard, body.clone()])),
                );
                Spanned::new(
                    s.span.clone(),
                    StmX::Loop {
                        loop_isolation: *loop_isolation,
                        is_for_loop: *is_for_loop,
                        id: *id,
                        label: label.clone(),
                        cond: None,
                        original_cond: Some((setup.clone(), exp.clone())),
                        body: new_body,
                        invs: invs.clone(),
                        decrease: decrease.clone(),
                        typ_inv_vars: typ_inv_vars.clone(),
                        modified_vars: modified_vars.clone(),
                        pre_modified_params: pre_modified_params.clone(),
                    },
                )
            }
            _ => s.clone(),
        })
    })
    .expect("normalize_setup_loops is structural and cannot fail")
}
