# probe39 — the b77 fork-gate evidence probe (VENDORED)

The step-0 discriminating probe behind bootstrap-77's E1 finding (the
card's "fork gate" section). Three default-closer shapes:

* `probe_if_ret`     — plain-cond value-if in RETURN position → production
                       FORKS (4 goals = 2 ens × 2 branches, per-branch
                       `_h_hoist_1 : cond` + `r = <branch>` FLetH pairs).
* `probe_if_assign`  — the same if behind `let m = …; m` → NOT forked
                       (2 goals; the if stays opaque inside
                       `_h_m_hoist1 : m = (if …)`). Root cause: the raw
                       SST has NO Assign — the body folds into
                       `Return(Bind(Let(m := If …), Var m))` and
                       `walk_let`'s Bind arm renders binder RHSs opaque.
* `probe_match_assign` — match in assign position → NOT forked (1 goal).

Regen + inspect:
  OUT=$(mktemp -d)
  TACTUS_LEAN_OUT=$OUT ./source/target-verus/release/verus \
    --crate-type=lib --lean-backend --tactus-emit-cert \
    probe-w0/probe39_b77_fork_gate/fork_probe.rs
  grep '^-- goal' $OUT/fork_probe/cert/*.cert.lean

The fixture twins (pick_max / head_via_let, F22/F23) pin the same facts
in the live probe9 bridge; this file preserves the original three-way
discriminator for reproducibility.
