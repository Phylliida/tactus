# Tactus Handoff Document

## What is Tactus?

Tactus is a fork of Verus that replaces Z3 (SMT solver) with Lean 4's proof kernel for verification. Users write Rust code with specs (`requires`/`ensures`/`invariant`) and Lean-style tactic proofs (`by { ring }`, `by { nlinarith [...] }`). The `.rs` files are the single source of truth.

See `DESIGN.md` for the full design rationale and decisions.

## Repository layout

```
tactus/
  DESIGN.md                    ← comprehensive design document (read this first)
  HANDOFF.md                   ← this file
  source/
    lean_verify/               ← NEW: Lean generation + invocation crate
      src/
        ir.rs                  ← simplified IR (Typ, Expr, SpecFn, ProofFn)
        to_lean_type.rs        ← VIR types → Lean types
        to_lean_expr.rs        ← VIR expressions → Lean expressions
        to_lean_fn.rs          ← spec fn → def, proof fn → theorem, file generation
        lean_process.rs        ← invoke `lean --stdin --json`, parse JSON diagnostics
        prelude.rs             ← TactusPrelude.lean content
        lib.rs
      tests/
        integration.rs         ← 5 end-to-end tests (generate Lean, invoke Lean, verify)
    builtin_macros/src/
      syntax.rs                ← MODIFIED: tactic mode for proof fns (lines ~4036-4085)
    rust_verify/src/
      attributes.rs            ← MODIFIED: Attr::TacticProof + VerifierAttrs.tactic_proof
      rust_to_vir_func.rs      ← MODIFIED: threads tactic_proof to FunctionAttrsX
      verifier.rs              ← MODIFIED: routing stub at line ~1575 (skips Z3 for tactic fns)
    vir/src/
      ast.rs                   ← MODIFIED: FunctionAttrsX.tactic_proof: bool
    air/                       ← UNCHANGED (will be removed after Lean backend is complete)
    Cargo.toml                 ← MODIFIED: added lean_verify to workspace
  tree-sitter-tactus/          ← sibling dir in verus-cad: tree-sitter grammar
```

## What works today

### Lean generation pipeline (fully tested)

The `lean_verify` crate generates valid Lean 4 from a simple IR and invokes Lean to verify it.

```
IR (SpecFn, ProofFn) → to_lean_fn → Lean text → lean --stdin --json → parsed diagnostics
```

**30 tests pass** (25 unit + 5 integration). Integration tests actually invoke Lean 4 and verify:
- `double` spec fn + `lemma_double_pos` proof fn with `unfold double; omega`
- `add_comm` with `omega`
- Intentionally wrong proof (correctly rejected)
- Recursive `factorial` with `termination_by` + induction proof
- Multiple requires/ensures with conjunction

Run tests:
```bash
cd tactus/source
cargo test -p lean_verify                          # unit tests (no Lean needed)
nix-shell -p lean4 --run "cargo test -p lean_verify --test integration"  # needs Lean 4
```

### Verus pipeline modifications (compiles, not yet end-to-end tested)

The tactic_proof attribute flows through the entire pipeline:

```
proof fn body detected in builtin_macros
  → #[verus::internal(tactic_proof)] attribute emitted
  → body replaced with unimplemented!() dummy
  → Attr::TacticProof parsed in attributes.rs
  → VerifierAttrs.tactic_proof = true
  → FunctionAttrsX.tactic_proof = true (in VIR)
  → verifier.rs intercepts at OpKind::Query dispatch
  → skips Z3, currently stubs as "verified" with eprintln
```

Build everything:
```bash
cd tactus/source
RUSTC_BOOTSTRAP=1 cargo build -p rust_verify    # needs RUSTC_BOOTSTRAP for rustc_private
cargo build -p lean_verify -p vir -p verus_builtin_macros  # these build without it
```

## What needs to be done next

### Immediate: Wire Lean into the verifier (the "last mile")

**The stub in `verifier.rs` (~line 1586) needs to call `lean_verify` instead of just printing and continuing.**

The function at that point is a `FunctionSst` (SST-level). To call lean_verify, we need:

1. **Collect all spec fns** that this proof fn references (from `krate.functions`)
2. **Convert VIR/SST types and expressions** to `lean_verify::ir` types
   - This is the missing glue code: `FunctionSstX` → `lean_verify::ir::SpecFn`/`ProofFn`
   - Needs a conversion module, roughly: walk the VIR `Expr` tree and emit `lean_verify::ir::Expr`
3. **Extract tactic body** from the source file using tree-sitter-tactus (by source span)
   - The span is available from `function.span`
   - tree-sitter-tactus parses the file and extracts the text between `by {` and `}` (or the block body for now)
4. **Generate Lean, invoke, parse results** — `lean_verify` already does this
5. **Convert `LeanResult` to `ValidityResult`** — map Lean success/failure to Verus's result enum
6. **Report errors** — map Lean diagnostic positions back to `.rs` source locations

The pieces exist, they just need connecting.

### Immediate: Full Verus build environment

The modified `rust_verify` binary needs the full Verus build environment to run (vstd, builtin crate, etc.). To test end-to-end:

1. **Set up Z3** (still needed during transition for non-tactic functions):
   ```bash
   cd tactus/source
   ./tools/get-z3.sh  # downloads Z3 to source/z3
   ```

2. **Build with vargo** (Verus's custom cargo wrapper):
   ```bash
   # From tactus/source:
   cargo install --path cargo-verus
   vargo build --release   # or just: vargo build
   ```

3. **Run on test file**:
   ```bash
   ./target-verus/release/verus test.rs
   ```

I haven't done this step yet — it requires Z3 to be present and vstd to compile.

### Short-term: VIR → lean_verify::ir conversion

The `lean_verify::ir` types (`Typ`, `Expr`, `SpecFn`, `ProofFn`) are simplified versions of VIR's types. A conversion module is needed:

```rust
// New file: lean_verify/src/from_vir.rs (or vir/src/to_lean_ir.rs)

fn convert_typ(vir_typ: &vir::ast::Typ) -> lean_verify::ir::Typ {
    match &**vir_typ {
        vir::ast::TypX::Bool => lean_verify::ir::Typ::Bool,
        vir::ast::TypX::Int(range) => lean_verify::ir::Typ::Int(convert_int_range(range)),
        vir::ast::TypX::TypParam(name) => lean_verify::ir::Typ::TypParam(name.to_string()),
        // ... etc
    }
}

fn convert_expr(vir_expr: &vir::ast::Expr) -> lean_verify::ir::Expr {
    match &vir_expr.x {
        vir::ast::ExprX::Const(c) => match c {
            vir::ast::Constant::Bool(b) => lean_verify::ir::Expr::Bool(*b),
            vir::ast::Constant::Int(n) => lean_verify::ir::Expr::IntLit(n.to_string()),
            // ...
        },
        vir::ast::ExprX::Var(ident) => lean_verify::ir::Expr::Var(ident.0.to_string()),
        vir::ast::ExprX::Binary(op, l, r) => {
            lean_verify::ir::Expr::Binary(
                convert_binop(op),
                Box::new(convert_expr(l)),
                Box::new(convert_expr(r)),
            )
        },
        // ... etc (Call, Quant, If, Bind, Unary, ...)
    }
}

fn convert_function(func: &vir::ast::FunctionX, tactic_text: &str) -> lean_verify::ir::ProofFn {
    lean_verify::ir::ProofFn {
        name: func.name.path.segments.iter().map(|s| s.to_string()).collect(),
        params: func.params.iter().map(|p| convert_param(p)).collect(),
        requires: func.require.iter().map(|e| convert_expr(e)).collect(),
        ensures: func.ensure.0.iter().map(|e| convert_expr(e)).collect(),
        tactic_body: tactic_text.to_string(),
        // ...
    }
}
```

This is mostly mechanical — walk the VIR tree and emit the lean_verify IR equivalent. The VIR types are well-documented in `vir/src/ast.rs`.

### Short-term: Tree-sitter tactic extraction

The proc macro records the source span of the proof fn body. We need tree-sitter-tactus to extract the actual tactic text:

```rust
// lean_verify/src/tactic_extractor.rs

pub fn extract_tactic_body(source: &str, span: &Span) -> Option<String> {
    let mut parser = tree_sitter::Parser::new();
    parser.set_language(&tree_sitter_tactus::LANGUAGE.into()).ok()?;
    let tree = parser.parse(source.as_bytes(), None)?;
    // Walk tree to find tactic_block or block at the given span
    // Extract the text between { and }
    // Return trimmed tactic text
}
```

This requires adding `tree-sitter` and `tree-sitter-tactus` as dependencies of `lean_verify`. The `tree-sitter-tactus` crate is at `../../tree-sitter-tactus` (path dependency).

**For initial testing**, you can skip this and hardcode the tactic text or extract it with a simpler regex on the source span. tree-sitter is the clean solution for Unicode support.

### Medium-term: The `by { }` syntax

Currently, proof fn bodies in Tactus are regular Rust blocks (because the proc macro captures them as TokenStream). The `by { }` syntax (where `by` appears OUTSIDE the block, after the signature) needs grammar support:

```rust
// This is the target syntax:
proof fn lemma() ensures P
by {
    omega
}

// Currently, the proc macro sees this as a regular block body:
proof fn lemma() ensures P
{
    // tactic text here
}
```

Both syntaxes work with the current proc macro (it just detects `FnMode::Proof` and marks it as tactic). The `by` prefix is syntactic sugar that tree-sitter-tactus already handles. The proc macro doesn't need `by` — it treats ALL proof fn bodies as tactic blocks.

The syn parser (`dependencies/syn/src/verus.rs`) would need modification to accept `by` before the body brace if we want that specific syntax through the proc macro path. But since we extract tactic text via tree-sitter (not the proc macro), the proc macro just needs to see a valid Rust block.

### Medium-term: Track C — vstd translation

Verus programs depend on `vstd` (verified standard library). The `lean_verify` VIR path mapper needs entries for vstd built-in functions. Start with:

1. `vstd::seq::Seq` operations → `Seq.*` in TactusPrelude
2. `vstd::set::Set` operations → `VerusSet.*` in TactusPrelude
3. `vstd::arithmetic::*` lemmas → Mathlib equivalents

The path mapping lives in `lean_verify/src/builtin_paths.rs` (not yet created):
```rust
pub fn vir_path_to_lean(path: &str) -> Option<&str> {
    match path {
        "vstd::seq::Seq::len" => Some("Seq.len"),
        "vstd::seq::Seq::index" => Some("Seq.index"),
        "vstd::seq::Seq::push" => Some("Seq.push"),
        // ...
        _ => None,
    }
}
```

### Long-term: Track B — exec fn VC generation (`sst_to_lean`)

This is the biggest piece of work (3-6 months). See DESIGN.md "VC generation for exec functions" section.

The approach: implement weakest-precondition VC generation from SST, targeting Lean directly. This is a new module `vir/src/sst_to_lean.rs` parallel to the existing `sst_to_air.rs`.

Key WP rules:
- `let x = e; rest` → `let x := e; wp(rest, Q)`
- `if c { s1 } else { s2 }` → `(c → wp(s1, Q)) ∧ (¬c → wp(s2, Q))`
- `while cond inv I { body }` → three theorems: init, maintain, use
- `x = e` (mutation) → SSA: `let x' := e; wp(rest[x→x'], Q)`
- Pattern matching, closures, borrows, control flow...

This is comparable in scope to `sst_to_air.rs` (~3000 lines). Start with straight-line code, then add loops, then mutation, then the rest.

### Long-term: Mathlib integration

Phase 1 uses `lean --stdin` (core Lean only). For Mathlib tactics (`ring`, `nlinarith`, `field_simp`, `positivity`):

1. Create `~/.tactus/lean-project/` with `lakefile.lean` importing Mathlib
2. Download precompiled oleans via `lake exe cache get` (~2 GB, ~5 min)
3. Change invocation from `lean --stdin` to `lake env lean <file> --json`
4. User specifies imports explicitly via `import` declarations

### Long-term: Remove Z3/AIR

Once `sst_to_lean` is complete:
1. Remove `air/` crate
2. Remove `sst_to_air.rs` and `sst_to_air_func.rs`
3. Remove Z3 subprocess code
4. Rename tool from `verus` to `tactus`

## Key files to understand

| File | What it does | Relevance |
|------|-------------|-----------|
| `lean_verify/src/ir.rs` | Simplified IR types | The interface between VIR and Lean generation |
| `lean_verify/src/to_lean_fn.rs` | Generates complete .lean files | The core Lean output generator |
| `lean_verify/src/lean_process.rs` | Invokes `lean --stdin --json` | The Lean subprocess interface |
| `builtin_macros/src/syntax.rs:4036` | `visit_item_fn_mut` | Where proof fns are detected + marked |
| `rust_verify/src/attributes.rs` | Attribute parsing | Where `tactic_proof` is read from rustc attrs |
| `rust_verify/src/verifier.rs:1575` | Query dispatch loop | Where tactic fns are routed (currently stub) |
| `vir/src/ast.rs:1436` | `FunctionAttrsX` struct | Where `tactic_proof` flag lives in VIR |
| `vir/src/ast.rs:1027` | `ExprX` enum | All VIR expression types (need conversion to IR) |
| `vir/src/ast.rs:258` | `TypX` enum | All VIR type variants (need conversion to IR) |
| `DESIGN.md` | Full design document | All architectural decisions and rationale |

## How to build and test

```bash
# Build lean_verify (no special toolchain needed):
cd tactus/source
cargo build -p lean_verify
cargo test -p lean_verify

# Run integration tests (needs Lean 4):
nix-shell -p lean4 --run "cargo test -p lean_verify --test integration -- --nocapture"

# Build everything including rust_verify (needs RUSTC_BOOTSTRAP):
RUSTC_BOOTSTRAP=1 cargo build -p rust_verify

# Build for actual use (needs vargo + Z3):
./tools/get-z3.sh
cargo install --path cargo-verus
vargo build
```

## Architectural decisions (summary from DESIGN.md)

1. **No Z3** — Lean only, no dual backend
2. **Cut at SST** — fresh WP-based VC generation, not reusing AIR
3. **Dual parser** — tree-sitter-tactus for Unicode tactic extraction, rustc proc macro for VIR construction
4. **All spec fns `@[irreducible]`** by default, `open spec fn` for transparent
5. **Explicit imports** — user writes `import Mathlib.Tactic.Ring`, no auto-detection
6. **Precompiled Mathlib** — `lake exe cache get`, not compiled from source
7. **`Seq.index` is opaque** — out-of-bounds truly unspecified (matches Verus semantics)
8. **`tactus_auto` uses `fail`** not `sorry` — auto-tactic failures are real errors
9. **`arch_word_bits` is axiom** — sound for cross-compilation
10. **`proof { }` in exec fns** — keeps syntax, body is tactics, results thread into VC context

## Git log (work done)

```
98f5f68 Tactus: verifier routing for tactic proof fns (stub)
ff06399 Thread tactic_proof through VIR: attribute flows from proc macro to FunctionAttrsX
284ac88 Tactus tactic_proof: proc macro + attribute detection
8a316ab lean_verify: end-to-end pipeline working — IR → Lean → verified
59b7db8 lean_verify: IR types + Lean type/expression translators
4ae01c2 lean_verify crate: Lean 4 subprocess invocation working
bb18bff DESIGN.md: comprehensive design after 4 critique rounds
```

Plus in the parent `verus-cad/` repo:
```
0c14995 tree-sitter-tactus: initial grammar for Tactus language
```
