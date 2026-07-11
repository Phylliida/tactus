# Routing plain proof fns to Lean — findings & the `--lean-all-proofs` flag

**Date:** 2026-07-09
**Status:** experimental flag landed (commit `1cb9131`); translator coverage is the open work.
**Scope:** why plain `proof fn`s in a `--lean-backend` crate are verified by Z3 (not Lean),
what it takes to change that, and a crate-wide measurement of the gap.

---

## TL;DR

- A `--lean-backend` crate is a **hybrid**: `exec` fns and proof fns with an explicit Lean
  **tactic block** go to Lean; **plain `proof fn`s** (assert/lemma-call bodies, no `by { }`
  tactic block) fall through to **Z3**. This is a routing gate, not a translation limitation.
- The per-fn Lean codegen (`emit_exec_fn` / `check_exec_fn`) is a **general SST→WP→Lean
  translator that already accepts `Mode::Proof`** — it is only misleadingly named "exec".
- Added **`--lean-all-proofs`** (off by default): under `--lean-backend`, also routes plain
  proof fns through the Lean WP path. `#[verifier::z3]` remains the per-fn opt-out.
- Crate-wide on **tactus-group-theory** (emit-only, no Lean run): **1338 fns translate,
  1409 reject.** The rejections are dominated by **`StmX::DeadEnd` (~90%)** — Verus-style
  scoped proof blocks `assert(P) by { <proof> }` / `assert forall|..| .. by { }` — with
  **multi-element `seq![a, b]` array literals (~10%)** a distant second.
- Consequence for `docs/…/m4-qpow-cliff-handoff.md`: those functions are **plain proof fns →
  Z3**, so the "Lean `maxHeartbeats` cliff" framing is suspect; the slowness is more likely a
  Z3 quantifier/fuel storm.

---

## 1. Where `--emit-lean` writes, and why it can look like "nothing happened"

`--emit-lean` (config.rs `OPT_EMIT_LEAN`) emits per-fn `.lean` files + a `sourcemap.json`
sidecar and **skips the Lean run** (codegen only). Output root is `lean_out_root()`
(`lean_verify/src/generate.rs`), resolved in priority order:

1. `$TACTUS_LEAN_OUT`
2. `$CARGO_TARGET_DIR/tactus-lean`
3. `./target/tactus-lean` — **relative to the cwd where `verus` runs**, then made absolute.

Files land in `<root>/<crate-name>/`:
- per-fn: `<module>__<fn>.lean`
- sidecar: `sourcemap.json`

**Two gotchas that make output look missing:**
- It is **cwd-relative** by default. Running `check.sh` from the repo root vs. from the crate
  dir puts the files in different `target/tactus-lean` trees. Set `$TACTUS_LEAN_OUT` to pin it.
- The crate name is inferred from the source filename. `check.sh` passes `src/lib.rs` with no
  `--crate-name`, so the folder is **`lib/`**, *not* a folder named after the crate. Looking
  for `verus_group_theory/` or `tactus-group-theory/` finds nothing; the files are in `lib/`.

Note: the per-fn `.lean` is written on **every** `--lean-backend` run (codegen precedes the
Lean run). `--emit-lean` only *adds* `sourcemap.json` and *skips* the Lean invocation.

---

## 2. The routing architecture (the actual finding)

In `rust_verify/src/verifier.rs`, per-fn verification dispatches as follows:

| Function kind | Routed to | Path |
|---|---|---|
| proof fn **with** a tactic block (`tactic_span`) | Lean | `emit_proof_fn` / `check_proof_fn` (verbatim tactic text) |
| `exec` fn (under `--lean-backend`, no `#[verifier::z3]`) | Lean | `emit_exec_fn` / `check_exec_fn` (SST→WP) |
| **plain `proof fn`** (no tactic block) | **Z3** | general query path (`spinoff_z3_context`) |
| `spec` fn | — | definition, no body obligation |

The deciding gate was (pre-flag):

```rust
let route_to_lean = if self.args.lean_backend {
    function.x.mode == vir::ast::Mode::Exec && !function.x.attrs.tactus_z3
} else {
    function.x.attrs.tactus_auto
};
```

Only `Mode::Exec` is routed. Plain proof fns fall through. Confirming evidence that they end
up on **Z3**, not Lean:
- The SMT solver enum (`air/src/context.rs`) has only `Z3` and `Cvc5`; there is **no Lean
  variant** and no AIR→Lean path.
- `lean_backend` is consulted in only three places in `verifier.rs`: this exec gate and two
  file-loader (source-sanitization) call sites. Nothing intercepts the general query run.
- Empirically: `--emit-lean --verify-module m4_qpow` reports `8 verified, 0 errors` but
  `--emit-lean wrote sourcemap.json (0 fns)` — the 8 plain proof fns verify yet emit nothing,
  because they never touch the Lean codegen.

**Why the "exec" translator already handles proof fns.** Inside `emit_exec_fn`
(`lean_verify/src/generate.rs`):

```rust
let defs = crate::crate_defs::for_crate(pre_inline_krate, crate_name, tactic_bodies, false)
    .filter(|d| d.covers_exec || matches!(vir_fn.mode, vir::ast::Mode::Proof));
// comment: "WP-style PROOF fns (Verus proof bodies routed through this same WP path)
//           are covered by the proof roots and keep the import."
```

The translator is a general WP-obligation lowering; `Mode::Proof` is explicitly anticipated.
The routing gate was the only thing keeping plain proof fns off it.

---

## 3. The `--lean-all-proofs` flag

Landed in commit `1cb9131`. Off by default; no behavior change unless set.

- **config.rs**: `OPT_LEAN_ALL_PROOFS = "lean-all-proofs"`, `Args.lean_all_proofs: bool`,
  plus doc/default/parse plumbing (mirrors `--lean-backend`).
- **verifier.rs**: the gate becomes

```rust
let route_to_lean = if self.args.lean_backend {
    (function.x.mode == vir::ast::Mode::Exec
        || (self.args.lean_all_proofs
            && function.x.mode == vir::ast::Mode::Proof))
        && !function.x.attrs.tactus_z3
} else {
    function.x.attrs.tactus_auto
};
```

Proof fns with a tactic block are handled by an earlier branch that `continue`s, so anything
reaching this gate in `Mode::Proof` is a *plain* proof fn — exactly the target. `#[verifier::z3]`
opts an individual fn back onto Z3.

Build: `cd tactus/source && vargo build --release` (incremental; only `rust_verify` changed).

---

## 4. Crate-wide characterization (tactus-group-theory)

Command (emit-only — codegen success, **no** Lean run):

```bash
env TACTUS_LEAN_OUT=/tmp/allproofs \
  target-verus/release/verus --lean-backend --lean-all-proofs --emit-lean \
  --crate-type=lib src/lib.rs
```

Result: `--emit-lean wrote sourcemap.json (1338 fns)` / `1544 verified, 1409 errors`.

| Outcome | Count | Share of all |
|---|---:|---:|
| **Translate & emit `.lean`** | 1338 | 49% |
| **Reject — `DeadEnd`** | 1267 | 45% |
| **Reject — multi-element array literal** | 142 | 5% |

Roughly **half** the crate's proof-obligation fns already codegen to Lean. The rest is blocked
on two translator features, one dominant.

### 4.1 `DeadEnd` (1267 rejections, ~90% of failures)

`StmX::DeadEnd` (`vir/src/sst.rs:203`) is Verus's desugaring of a **scoped proof block** whose
state effects are discarded — `assert(P) by { <proof body> }` and `assert forall|i| P(i) by { }`
(`vir/src/ast_to_sst.rs:2296`). The Lean translator rejects it outright:

```rust
// lean_verify/src/sst_to_lean.rs:4873
StmX::DeadEnd(_) => Err(
    "Verus's internal `DeadEnd` marker reached the SST — this shouldn't \
     appear in user code. If you're seeing this, please open an issue.".into()),
```

The translator **does** handle the *raw-Lean-tactic* form of assert-by — `StmX::AssertQuery`
(`assert(P) by { <lean_tac> }`, `proof { }`, `assert by(nonlinear_arith)`) — but not the
*Verus-proof-body* form that becomes `DeadEnd`. Proof fns are built almost entirely out of
Verus-proof-body assert-by, so this is the wall.

Why exec fns rarely hit it: exec bodies express proof steps via `proof { <lean tactic> }`
blocks (→ `AssertQuery`), not `assert … by { <verus proof> }`.

### 4.2 Multi-element array literals (142 rejections, ~10%)

`seq![Symbol::Gen(0), Symbol::Gen(1)]` lowers to an array literal `[a, b]` that the WP renderer
rejects ("array literal `[a, b, c]` not yet supported in exec fns"). Single-element `seq![x]`
already works. Exec fns rarely hit this (Verus tends to reject multi-element array literals
upstream); proof fns use `seq!` pervasively.

---

## 5. Worked example: `src/m4_qpow.rs`

`--lean-all-proofs --emit-lean --verify-module m4_qpow`: **2 emit, 6 reject.**

- ✅ `lemma_pow_zero`, `qconj_step_generic` — translated; emitted `.lean` is complete (full
  preamble: Rust std → Lean, `seq.Seq` axioms, the theorem).
- ❌ 6 lemmas rejected on multi-element `seq![a, b]` literals (§4.2).

The commented-out recursive `lemma_qpow_conj` would *additionally* be in the `DeadEnd` bucket
(its body is all `assert … by`). So m4_qpow needs **both** translator features before its Lean
can even be produced — let alone before the documented "cliff" can be tested on Lean.

**Cliff re-diagnosis.** Because these are plain proof fns, under the current build they route to
**Z3**. `docs/m4-qpow-cliff-handoff.md` frames the >240s hang as a Lean `maxHeartbeats` cliff;
that framing is very likely wrong. The slowness is more consistent with a **Z3 quantifier/fuel
storm** — recursive `abpow`/`bapow` unfolding inside the `∃Derivation` existential of
`equiv_in_presentation`. Verify which solver the fn actually hits before pursuing a Lean-backend
fix. (`hide(abpow)`/`reveal_with_fuel(abpow, 1)`, opaque `equiv_in_presentation`, and
`verus_profile` are the Z3-side levers.)

---

## 6. Caveats on the 1338 that "translate"

- **Emit-only.** These numbers are *codegen* success (`--emit-lean` skips Lean). We have **not**
  confirmed the 1338 actually *verify* under a real Lean run. 1338 is an **upper bound**.
- **Perf cliffs live in the Lean run, not codegen.** A fn can translate cleanly and still time
  out / hang on `lake` (the m4_qpow phenomenon). A full `--lean-all-proofs` run without
  `--emit-lean` would surface those.
- **Cache + rebuild.** Flipping proof fns to Lean invalidates their verus-cache entries and
  re-verifies through Lean — expect a large batch of new rejections/timeouts to triage.

---

## 7. The unlock

Two independent translator features close the gap, dominated by the first:

1. **Lower `StmX::DeadEnd(block)`** (unblocks ~90% of failures). Recurse into the block,
   translate its inner Verus statements (lemma calls, `let`s, nested asserts) as a **scoped Lean
   sub-proof** whose state effect is discarded — structurally the existing
   `AssertQuery`/`have`-binding machinery, but with the body being *translated SST* rather than
   *raw tactic text*. Edit site: `lean_verify/src/sst_to_lean.rs:4873`.
2. **Multi-element array literals** — lower `seq![a, b, …]` in obligation position. Smaller,
   independent.

Recommended rollout: keep `--lean-all-proofs` as the measurement instrument and eventual
default switch; land (1), re-run the crate-wide count to measure the jump; then (2); then a real
(non-emit) Lean run to find the perf cliffs that codegen success hides.

---

## 8. Reproduction

```bash
# Build the fork (incremental after the flag change):
cd tactus/source && vargo build --release
VERUS=$PWD/target-verus/release/verus

# Scoped (m4_qpow), codegen only, pinned output dir:
cd ../../tactus-group-theory
env TACTUS_LEAN_OUT=/tmp/qpow-lean \
  "$VERUS" --lean-backend --lean-all-proofs --emit-lean \
  --crate-type=lib src/lib.rs --verify-module m4_qpow
ls /tmp/qpow-lean/lib/          # emitted .lean + sourcemap.json

# Crate-wide characterization:
env TACTUS_LEAN_OUT=/tmp/allproofs \
  "$VERUS" --lean-backend --lean-all-proofs --emit-lean \
  --crate-type=lib src/lib.rs > /tmp/allproofs.log 2>&1
grep -c "rejected this fn" /tmp/allproofs.log
grep "rejected this fn" /tmp/allproofs.log \
  | sed -E 's/.*rejected this fn: //; s/\(see DESIGN.*//; s/`[^`]*`/`X`/g' \
  | sort | uniq -c | sort -rn
```

---

## 9. Key file/line references

| What | Location |
|---|---|
| Flag definition + plumbing | `rust_verify/src/config.rs` (`OPT_LEAN_ALL_PROOFS`, `Args.lean_all_proofs`) |
| Routing gate | `rust_verify/src/verifier.rs` (`route_to_lean`, ~line 1949) |
| WP translator entry (proof-aware) | `lean_verify/src/generate.rs` (`emit_exec_fn` / `check_exec_fn`) |
| SST→WP theorem builder | `lean_verify/src/sst_to_lean.rs` (`exec_fn_theorems_to_ast`) |
| `DeadEnd` rejection | `lean_verify/src/sst_to_lean.rs:4873` |
| `DeadEnd` origin (assert-by desugar) | `vir/src/ast_to_sst.rs:2296`; def `vir/src/sst.rs:203` |
| Output dir resolution | `lean_verify/src/generate.rs` (`lean_out_root`) |
| Solver enum (Z3/Cvc5 only) | `air/src/context.rs` |

---

## 10. Real-run results (2026-07-09) — the codegen numbers were the wrong bottleneck

Full non-emit run on tactus-group-theory (`--lean-backend --lean-all-proofs -V cache`, run
from the crate dir, no `TACTUS_LEAN_OUT`, so Lean output lands in `target/tactus-lean/lib/`):
**229 verified, 24817 errors, 8 cached; ~91 min wall; 93 MB log** (`/tmp/tactus-gt-allproofs-real.log`).

Of the 1338 fns that codegen: **214 pass a real Lean run (16%), 1124 fail.** But the error mass
decomposes almost entirely into a handful of *translator bugs*, each amplified crate-wide — not
into proof-power failures:

| Family | Error blocks | Distinct fns | Root cause |
|---|---:|---:|---|
| Codegen rejections | 1,409 | 1,409 | Known: `DeadEnd` (1267) + `seq![a,b]` (142), §4 |
| `auto-tactic failed` | 5,666 | 1,024 | Closer can't close — the *real* migration bucket |
| Choose-body type mismatch | 2,596 | 440 | ONE renderer bug: `choose\|j\| P(j)` in hypothesis position renders as `(P j) ∧ j` (an `Int` conjunct). Epsilon form (`Classical.epsilon`) is emitted elsewhere in the same file, so it's the Bind(Choose)-with-body statement path |
| Termination of recursive defs | 2,131 | 841 | TWO missing decreasing facts: `len (drop_first w) < len w` (+`drop_last`) ≈ 93% of goals; `a / m < a` (Nat div) the rest. Hits recursive spec-fn *preamble defs* and recursive proof fns alike |
| Namespace shadow / missing def | 2,235 | 552 | Locals named `symbol` shadow the `symbol` *module* under Lean dot-notation → `symbol.generator_index` resolves as field lookup on `lib.symbol.Symbol` (2,203); missing `Option.deref` std spec def (28) |
| `Inhabited T` synthesis | 713 | 569 | Typeclass gap in generic contexts |
| Lean keyword collision | 182 | (in tail) | Verus locals named `prefix` hit Lean's reserved keyword — same identifier-hygiene family as the shadowing bug |
| Heartbeats timeouts | ~26 | ~11 | **Perf cliffs are NOT the story** at this stage |

(Families overlap per-fn; a fn typically hits several.)

**Consequences for §7's rollout order.** Codegen coverage (`DeadEnd`, `seq!`) is no longer the
top unlock. By leverage on *verified* fns:

1. **Identifier hygiene** — sanitize binder names that collide with module namespaces or Lean
   keywords (or emit `_root_.`-qualified names). Pure bug, mechanical, kills the
   namespace-shadow + `prefix` families (~550 fns' spurious errors).
2. **Choose-body rendering** — fix the `(P j) ∧ j` statement-path lowering (440 fns). Note:
   until fixed, downstream `auto-tactic failed` goals in those fns are *undercounted victims* —
   the choose witness fact arrives malformed, so goals that should close don't.
3. **Two decreasing facts** — teach the emitted `decreasing_by` (or preamble `@[simp]` set)
   `len (drop_first w) < len w` / `drop_last` / `Nat.div_lt_self` (841 fns).
4. **`Inhabited`/`Nonempty` synthesis** in generic contexts (569 fns).
5. *Then* re-run: the `auto-tactic failed` bucket (5,666 goals / 1,024 fns) is the true
   closer-vs-Z3-idiom migration workload, and it will shrink once (1)–(4) stop corrupting
   hypotheses. Only after that is the §7 `DeadEnd`/`seq!` codegen work the frontier again.

**Gate hygiene note.** The working-tree `check.sh` (uncommitted edit) passes `--emit-lean`
unconditionally, which *skips the Lean run* — it currently reports `3116 verified, 0 errors —
Lean run skipped`, i.e. the standing gate is codegen-only for every Lean-routed fn. The
`-V cache` + tee-to-log additions are keepers; the `--emit-lean` should be dropped from the
default line (still passable via `"$@"`) once experimentation settles.

### 10.1 Post-fix re-measurement (2026-07-09, same day — after B1–B4 of the bugs doc)

Same command, after `DESIGN-lean-all-proofs-bugs.md` B1–B4 landed (`dbc77e5`,
`00534c9`): **8,950 errors (was 24,817 — −64%); 253 of 1,338 codegen'd fns pass
(was 214)**. Exec gate green throughout (24 verified, 0 errors — better than its
own pre-existing baseline: `apply_hom_symbol_exec` came unstuck).

| Family | Before | After | Notes |
|---|---:|---:|---|
| Codegen rejections | 1,409 | 1,409 | §7 features (`DeadEnd`, `seq![a,b]`) — untouched by design |
| auto-tactic failed | 5,666 | 5,987 | GREW because walls fell — goals that never elaborated now reach the closer. This is the honest migration bucket. |
| Type mismatch | 2,596 | 1,145 | Choose family = **0**. Residual is a DIFFERENT family: multi-element seq literals rendered as `List` where `Vector n` is expected (`{ deref := [a, b, c] }`) — §7-adjacent, previously hidden behind rejections. |
| Namespace shadow / unknown ident | 2,235 | **0** | |
| Termination | 2,131 | 81 | 68/81 are `drop_first` goals in files whose dep-walk lacks `axiom_seq_subrange_len`, so the measure companion can't emit — fix = extend the dep-walk to pull the axiom in whenever `Seq.drop_first` emits. Rest: `sizeOf (if …)` Int-abs measures. |
| Inhabited synthesis | 713 | 3 | |
| Keyword collisions | 182 | 0 | 39 NEW `unexpected token '('` parse errors — a structural renderer shape, not identifier collisions; small, untriaged. |
| Heartbeats timeouts | ~26 | 71 | More fns reach real proving — expected growth. |

**Reading the fn-level pass number correctly:** +39 fns looks modest because a fn
passes only when EVERY goal closes, and the auto bucket (5,987 goals across ~1,000
fns) now gates almost everything — exactly the measurement the bug-fixes were
supposed to make honest. The error-mass collapse (−64%, with translator-bug
families down from ~60% of errors to ~15%) is the real before/after.

**Next frontiers, in order of leverage:** (1) the auto bucket — closer-vs-explicit-
tactic migration policy (per-goal, this is now genuine proof work, not bugs);
(2) §7 codegen: `StmX::DeadEnd` lowering (1,267 rejections) + multi-element seq
literals (142 rejections + the 1,145 List/Vector mistypes); (3) the small residuals
above (companion dep-walk, `'('` parse shape, B5 typed-spine deref).

### 10.2 Post-F1–F4 re-measurement (2026-07-11, overnight)

Same command, after `DESIGN-lean-all-proofs-followons.md` F1–F4 landed (`25970a5`,
`2e203dc`, `8171498`, `95c5b1b` + the two B1a-regression fixes `1d88162`/`719733e`).
Binary = F1–F4 exactly; the follow-on batch (`62f8bb0`: F2b/F2c/DoneEmpty) is NOT in this
measurement (committed mid-run, deliberately not rebuilt). Wall: ~14 h across two legs
(6 h timeout + `-V cache` resume) — the crate now emits 2,747 files (was 1,338), and
F4-unlocked assert-by proofs multiply goals per fn.

**Results: 0 codegen rejections (was 1,409) — 100% of 2,953 proof-obligation fns attempt
Lean. 723 fns pass fully (24.5%, was 253/8.6%) — 2.9× the §10.1 pass count. Error blocks
26,216 (was 8,950) — the predicted walls-fell growth: 1,409 formerly-silent fns now
contribute goals.**

| Family | §10.1 | Now | Notes |
|---|---:|---:|---|
| Codegen rejections | 1,409 | **0** | F3 + F4 |
| Parse errors (`unexpected token`) | 39 | **0** | F1 |
| Namespace/unknown-identifier | 0 | **0** | holds (incl. 2 regression fixes) |
| Type mismatch | 1,145 | **61** | F3 killed List/Vector. Residual = the `tmp__ : Int` tuple-projection family (B5-adjacent, was 10 pre-F4; concentrated in 3 fns) |
| Termination | 81 | 199 | 120 = drop_first goals of the F2c Prop-connective family + Int-abs (F2b) — **both addressed by the `62f8bb0` batch pending validation**; growth = F4-unlocked recursive proof fns |
| `Invalid field deref` | 55 | 122 | B5's typed-spine family, more visible now (its arc is specced + in progress separately) |
| Heartbeats (`maxHeartbeats`) | 71 | 998 | more fns reach real proving + more goals per fn; perf triage after the bug families |
| **auto-tactic failed** | 5,987 | **24,080** | **the honest F7 workload** across ~2,230 fns — taxonomy next |

**Reading it:** every structural translator family we targeted is at zero; what remains
is (a) the two termination families the already-drafted batch addresses, (b) B5's deref
family, (c) a 61-error B5-adjacent tuple residual, and (d) the auto bucket — now finally
an honest, complete number. F7's taxonomy starts from these 24,080 goals.
