# rung-attrib — Brick 1 per-theorem rung attribution

Measures which minimal tactic prefix closes each currently-passing
obligation theorem (`rfl` → `+decide` → `+omega` → `+tactus_peel∘T1` →
full `tactus_auto`). The T2 tail (goals needing default-set `simp_all`
/ case-split) is the squeeze-and-pin workload of
`DESIGN-transparent-automation.md` (§3; decision table §6; first
measured result recorded at the bottom of that doc: T2 = 64% on 75
theorems, 2026-07-11).

## Typical run

```bash
# 1. Emit artifacts (codegen only, no Lean run):
cd ../tactus-group-theory
TACTUS_LEAN_OUT=/tmp/attrib-emit \
  verus --lean-backend --lean-all-proofs --emit-lean --crate-type=lib src/lib.rs

# 2. (Optional) failing-fn list from a full real run's log:
grep -oE "failed for [a-zA-Z0-9_]+" real-run.log | awk '{print $3}' | sort -u > failing.txt

# 3. Attribute:
python3 tools/rung-attrib/fast_attrib.py \
  --lib /tmp/attrib-emit/lib --failing failing.txt --sample 40
```

Speed comes from three things (see the module docstring): one combined
file per fn (preamble elaborated once, obligation theorems duplicated
per variant with suffixed names), bare `lean` via the prelude-cache
`LEAN_PATH` (no `lake env` lock), and N-way parallelism. A 40-file
sample runs in ~2 minutes.

Caveats are in the module docstring — notably, theorems whose tactic
composes `tactus_auto` with user text (`first | tactus_auto | ...`)
are skipped by design: they already carry explicit proofs and are not
part of the default closer's load.
