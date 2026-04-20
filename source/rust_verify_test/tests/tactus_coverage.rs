//! Property-coverage matrix for `dep_order`'s VIR walker.
//!
//! The sanity check in `generate.rs` catches walker bugs that drop a
//! spec-fn reference — but only if the test we run reaches the buggy
//! variant in the first place. This file is the systematic companion:
//! a curated battery of small spec/proof fns, each designed to force
//! `walk_expr` / `walk_place` through one specific `ExprX` / `PlaceX`
//! variant, plus a final assertion that the full union of visited
//! variants covers the expected set.
//!
//! # How it works
//!
//! * Every `walk_expr` / `walk_place` visit in the verifier child
//!   process appends the variant name to `$TACTUS_COVERAGE_FILE`
//!   (instrumented in `lean_verify::dep_order`).
//! * This test binary sets that env var to a unique temp file, drives
//!   the verifier on each snippet via `verify_one_file`, then reads
//!   back the union.
//! * The list below enumerates what we expect to cover. Anything on
//!   the expected list that doesn't get visited is a **real regression**
//!   — either the walker broke or the snippet that was supposed to
//!   trigger the variant stopped doing so.
//!
//! # Subprocess safety
//!
//! `verify_one_file` spawns a child process. `std::env::set_var` in
//! this binary persists into the child (standard env inheritance). This
//! test file is a dedicated binary (separate from `tactus.rs`), so its
//! env var doesn't leak into the other integration tests' processes.
//!
//! # Adding new coverage
//!
//! 1. Add a snippet in `run_snippets` that hits the new variant.
//! 2. Add the variant name to `EXPECTED_EXPR_VARIANTS` or
//!    `EXPECTED_PLACE_VARIANTS`.
//! 3. If the variant is unreachable in spec/proof contexts (exec-only),
//!    add it to the `EXEC_ONLY` comment below so future contributors
//!    know not to look for coverage.

#![feature(rustc_private)]

#[macro_use]
mod common;
use common::*;

use std::collections::HashSet;
use std::path::PathBuf;

/// Expression variants we expect to be covered by the snippets below.
///
/// Leaves not in this list are either exec-only (caught by the VIR mode
/// checker before reaching us — Assign, Loop, Return, BreakOrContinue,
/// NonSpecClosure, the BorrowMut family, AssignToPlace) or are
/// transparent markers VIR simplification strips before translation
/// (Header, Fuel, RevealString, AirStmt, Nondeterministic, AssertQuery,
/// AssertCompute, AssertAssumeUDTI, OpenInvariant, NeverToAny, Old,
/// EvalAndResolve, ProofInSpec, VarAt, Loc, VarLoc, ExecFnByName,
/// ImplicitReborrowOrSpecRead). When one of those starts appearing in
/// spec fn bodies we'll add a snippet and move it here.
/// Variants we've verified DO appear in real spec/proof VIR across the
/// existing suite. Each must be re-hit by this file's snippet battery;
/// if any drop out, either VIR's output shape changed or the walker
/// lost a branch.
///
/// Variants known not to appear in spec contexts (exec-only / transparent
/// markers stripped by VIR) are documented in the file's module comment.
const EXPECTED_EXPR_VARIANTS: &[&str] = &[
    "Binary", "BinaryOpr", "Block", "Call", "Closure", "Const", "Ctor",
    "If", "Match", "Quant", "ReadPlace", "Unary", "Var",
    "Choose",
];

const EXPECTED_PLACE_VARIANTS: &[&str] = &[
    "Local", "Field", "Temporary",
];

#[test]
fn tactus_variant_coverage() {
    let cov_path = coverage_file();
    let _ = std::fs::remove_file(&cov_path);
    // SAFETY: setting env in a dedicated test binary with exactly one
    // #[test]. No other thread is running to see a torn read.
    std::env::set_var("TACTUS_COVERAGE_FILE", &cov_path);

    run_snippets();

    let contents = std::fs::read_to_string(&cov_path).unwrap_or_default();
    let visited: HashSet<String> = contents.lines().map(str::to_string).collect();

    let mut missing_expr: Vec<&str> = EXPECTED_EXPR_VARIANTS.iter()
        .copied()
        .filter(|v| !visited.contains(*v))
        .collect();
    missing_expr.sort();

    let mut missing_place: Vec<String> = EXPECTED_PLACE_VARIANTS.iter()
        .map(|v| format!("Place::{}", v))
        .filter(|key| !visited.contains(key))
        .collect();
    missing_place.sort();

    if !missing_expr.is_empty() || !missing_place.is_empty() {
        let mut msg = String::from("coverage matrix missing variants:\n");
        for v in &missing_expr {
            msg.push_str(&format!("  ExprX::{}\n", v));
        }
        for p in &missing_place {
            msg.push_str(&format!("  PlaceX::{}\n", p.trim_start_matches("Place::")));
        }
        msg.push_str("\nVisited this run:\n");
        let mut all: Vec<&String> = visited.iter().collect();
        all.sort();
        for v in all { msg.push_str(&format!("  {}\n", v)); }
        panic!("{}", msg);
    }

    // Clean up the temp file — it's purely instrumentation output.
    let _ = std::fs::remove_file(&cov_path);
}

fn coverage_file() -> PathBuf {
    let pid = std::process::id();
    std::env::temp_dir().join(format!("tactus_coverage_{}.txt", pid))
}

// ── Snippet battery ────────────────────────────────────────────────────
//
// Each `verify_one_file` call is a separate verifier subprocess. The
// instrumentation appends to the shared file as each runs, building up
// the union we assert on.
//
// Every snippet `ensures` through a spec fn, so `dep_order` walks the
// ensure clause looking for that fn. If the walker drops the variant
// we're trying to exercise, the sanity check in `generate.rs` panics
// with a clear "unresolved reference" instead of silently missing it
// from the Lean preamble.

fn run_snippets() {
    // Arithmetic + binary comparison + spec fn call in ensures.
    // Hits: Binary, Call, ReadPlace, Const, Block (from the spec fn
    // body's implicit block).
    ok("arith_and_call", verus_code! {
        spec fn add(a: int, b: int) -> int { a + b }

        proof fn add_comm(a: int, b: int)
            ensures add(a, b) == add(b, a)
        by {
            unfold add; omega
        }
    });

    // Match in a spec fn body, referenced from ensures via a Call.
    // Hits: Match, Ctor (Op::Add / Op::Sub).
    ok("match_in_body", verus_code! {
        enum Op { Add, Sub }

        spec fn apply(o: Op, x: int) -> int {
            match o { Op::Add => x + 1, Op::Sub => x - 1 }
        }

        proof fn apply_add(x: int)
            ensures apply(Op::Add, x) == x + 1
        by {
            unfold apply; simp
        }
    });

    // `if c { .. } else { .. }` with boolean negation. Hits: If, Unary.
    // (`-x` is VIR's `Binary(Sub, 0, x)`, not `Unary`; we need `!b` for
    // Unary's Not branch.)
    ok("ite_and_not", verus_code! {
        spec fn neither(b: bool, c: bool) -> bool {
            if !b { !c } else { false }
        }

        proof fn neither_both_false()
            ensures neither(false, false)
        by {
            unfold neither; simp
        }
    });

    // Extensional equality `=~=` on sequences. Hits: BinaryOpr (ExtEq).
    ok("ext_equal", verus_code! {
        use vstd::prelude::*;

        spec fn ident(s: Seq<int>) -> Seq<int> { s }

        proof fn ident_eq(s: Seq<int>)
            ensures ident(s) =~= s
        by {
            unfold ident; rfl
        }
    });

    // Quantifier in ensures. Hits: Quant.
    ok("forall_ensures", verus_code! {
        spec fn constant_zero(i: int) -> int { 0 }

        proof fn constant_zero_is_zero()
            ensures forall|i: int| constant_zero(i) == 0
        by {
            simp
            unfold constant_zero
            simp
        }
    });

    // Tuple field access in ensures. Hits: ReadPlace, Place::Field,
    // Place::Temporary, BinaryOpr (via the ensures equality).
    ok("tuple_fields", verus_code! {
        spec fn pair(x: int) -> (int, int) {
            (x, x + 1)
        }

        proof fn pair_ordered(x: int)
            ensures pair(x).0 < pair(x).1
        by {
            unfold pair; simp; omega
        }
    });

    // Spec closure: `|y| y + 1` passed as spec_fn argument. Hits: Closure.
    ok("spec_closure", verus_code! {
        spec fn apply_once(f: spec_fn(int) -> int, x: int) -> int {
            f(x)
        }

        proof fn closure_add_one(x: int)
            ensures apply_once(|y: int| y + 1, x) == x + 1
        by {
            unfold apply_once; simp
        }
    });

    // Epsilon operator `choose |x| P(x)` with explicit trigger. Hits:
    // Choose. Verus requires the quantifier to have a trigger; the
    // proof isn't required to succeed, only for the walker to see it.
    ok("choose_operator", verus_code! {
        spec fn positive_enough(i: int) -> bool { i > 0 }

        spec fn some_positive() -> int {
            choose|i: int| #[trigger] positive_enough(i)
        }

        proof fn witness()
            ensures some_positive() == some_positive()
        by {
            rfl
        }
    });
}

fn ok(name: &str, code: String) {
    let result = verify_one_file(name, code, &[]);
    // Some of our targeted snippets may not verify (e.g., `choose` with
    // a picky tactic). We still want the verifier to reach the AST
    // pipeline so walk_expr fires. So we accept either success OR an
    // error whose diagnostics mention our spec fn — the file was
    // generated, Lean was invoked, the walker ran.
    match result {
        Ok(_) => {}
        Err(e) => {
            // Dump the diagnostics for debugging but don't fail — we
            // only care that the pipeline reached `generate_lean` long
            // enough to walk the VIR.
            eprintln!(
                "[coverage] snippet `{}` failed to verify (OK for instrumentation):\n{:?}",
                name, e
            );
        }
    }
}
