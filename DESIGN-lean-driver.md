# DESIGN: per-crate persistent Lean driver (snapshot-branching checks)

Status: DESIGN VALIDATED end-to-end by probes (2026-07-17, e2e-speed
session); build not started. Probe scripts preserved in the session
scratchpad; numbers below are from the live prelude cache on hera.

## Problem

After the e2e-speed work (slim prelude import, parallel per-fn checks,
defs collapse), the remaining lean-backend cost is per-PROCESS fixed
cost: every module check spawns `lean`, and ~1s of each spawn is
process start + prelude olean import. A crate pays 1+2N processes.
tactus-core cold ≈ 91s, suite ≈ 77s — the floor is process count ×
~1s, not proof work.

## Measured foundation (the three probes)

1. `importModules #[TactusDefs] (loadExts := true)` in a `lean --run`
   driver process: **~1.0-1.4s**, once. (`loadExts := true` is
   REQUIRED — without it constants load but notations/parser
   extensions don't; symptom is `expected token` on `≤`/`+`.)
2. Elaborating a real theorem (`by omega`) against a
   `Command.mkState env` snapshot of that import: **17-35ms**, and
   environments are immutable values — every check branches from the
   same snapshot with exact isolation. ~50-100x the process path.
   (Parse via `Parser.parseHeader` first even for header-less source.)
3. `writeModule` from the branched env after `env.setMainModule`:
   produces a VALID olean containing only the branch's local decls;
   re-importing it next to TactusDefs works and
   `CollectAxioms.collect` on the reloaded theorem returns
   `[propext, Quot.sound]` — i.e. the Link gate's closure check works
   unchanged on driver-produced artifacts.

## Architecture

One driver process per verus run (per crate), spawned lazily by
lean_process.rs, speaking JSON-lines on stdin/stdout:

    → {"op":"import","modules":[...]}            (rebuild base snapshot)
    → {"op":"check","file":...,"olean":...,"module":...}
    ← {"ok":bool,"diags":[{severity,pos,msg}...]}

Driver = a .lean program run with `lean --run` (interpreted; the heavy
machinery is compiled Lean core). It strips the emitted file's import
header and elaborates the body against the current snapshot; the
snapshot must be an importModules-backed env whose modules are a
SUPERSET of the file's header imports (statements-visible supersets
are sound — see Isolation below).

Per-crate orchestration (who calls what, in generate.rs terms):

    S0 = importModules([prelude])                    ~1s
    defs modules elaborated as branches of S0        ~ms each
      → oleans via writeModule (probe 3)
    S1 = importModules([prelude, defs])              ~1s
    all TactusStmts_* elaborated as branches of S1   ~ms each → oleans
    S2 = importModules([prelude, defs, all stmts])   ~1s
    all pkg checks as branches of S2                 ~ms + proof time
      → oleans (imports recorded = S2's set)
    Link: keep as ONE ordinary `lean` process (imports pkg oleans),
      exactly as today — zero trust-story change.

Fixed cost ≈ 3 importModules + 1 Link process ≈ ~4s/crate; marginal
cost per fn ≈ elaboration only. Estimated: tactus-core cold 91s →
~20-40s (with K driver workers each paying the fixed imports once);
e2e suite 77s → ~55-60s (front-end-bound after this).

## Isolation / trust notes

- Branching from S2 means a pkg sees sibling fns' STATEMENTS (abbrevs,
  no proofs) — same information class as today's callee-stmt imports;
  sibling THEOREMS are not in the env, so per-fn proof isolation is
  preserved where it matters.
- Pkg oleans record S2's module set as imports (wider than today's
  [own stmt, defs] but the same modules Lean dedups on import) — Link
  stays an ordinary Lean elaboration of ordinary artifacts. No change
  to what a third party re-runs for audit.
- Files with user `import Mathlib.*` / TactusSearch: fall back to the
  process-per-file path (snapshot lacks those modules). Search-ladder
  files could get their own S2' = importModules(S2 + TactusSearch) if
  they cluster.

## Build plan (the follow-on card)

1. `lean_verify/driver.lean` + protocol structs; validate standalone
   against real emitted files from an e2e temp tree.
2. lean_process.rs: driver lifecycle (spawn on first use, kill on
   drop), route `run_lean`/`check_lean_file`/`build_olean`; per-file
   set_options (maxHeartbeats) via cmdState options.
3. Flag-gate `--tactus-driver` (default off); crash → transparent
   fallback to process-per-file.
4. Gates: e2e suite parity (550/1), tactus-core 141/0 + 3-rep hash
   determinism, Link/census byte-parity vs process path on a fixture,
   gt gate cold run.
