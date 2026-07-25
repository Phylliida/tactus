# W3 — differential gate over tgt: results (bootstrap-08)

The first run of the refWp↔production bridge over certs emitted from **real
corpus code** (tactus-group-theory), not the hand-authored bootstrap-fixture
family. This is the differential gate's bug-finding payoff.

## Corpus (N4 census, DESIGN-W2-refwp.md §1.1), independently reconfirmed here

Stage-A cert emission is **exec-fn-only**. tgt is proof/spec-heavy: **9 exec fns
crate-wide**. Targeted cold emits (`--verify-module`, `--tactus-emit-cert`, no
cache) over the two modules that hold them reproduce the census buckets exactly:

| module | exec fns | certified | rejected (loud, no cert) |
|---|---|---|---|
| `runtime` | 7 | **1** (`impl__4::clone`) | 5 `call` + 1 `assert-query` |
| `todd_coxeter_rt` | 2 | 0 | 2 `assert-query` |
| **crate** | **9** | **1/9** | 5 `call` + 3 `assert-query` = **8/9** |

- 5 `call` (bootstrap-02b): `find_cancellation_exec`, `copy_word`,
  `apply_hom_gen`, `apply_hom_inv`, `apply_hom_symbol_exec`.
- 3 `assert-query`: `runtime::is_inverse_pair_exec`,
  `todd_coxeter_rt::symbol_to_column_exec`, `todd_coxeter_rt::inverse_column_exec`.

The 8 rejections emit **no cert** and are therefore **not bridge subjects** —
they are stage-A scope gaps (feed the Call arm + an assert-query arm), not
divergences. So the differential gate has exactly **one** bridgeable subject
today: `runtime::impl__4::clone`. Verdict-neutrality held throughout
(`24 verified, 0 errors` runtime run; flag on, cold).

## The one bridgeable cert DIVERGES — and the divergence is triaged to a single leaf

`runtime::impl__4::clone` = `fn clone(self: &RuntimeSymbol) -> RuntimeSymbol`
(derived `Copy`-clone; trivial WP, hence the only exec fn clearing stage-A scope).

Its bridge `goals_eq (ref_wp ctx sst) production = 1` is **FALSE**
(`decide` reduces it to `0`). Pinpoint-proved (`Pinpoint.lean`, 4 decides pass):

| slot | SST (serializer) | production goal | match? |
|---|---|---|---|
| telescope | seed `FBind 0 1` → `All 0 1` | `All 0 1` | ✓ |
| RetLet name | `RetLet(4, ·)` | `Let 4 ·` | ✓ |
| obligation leaf | Ret leaf `3` (annotated `_return = self.deref`) | `Leaf 3` | ✓ |
| **RetLet value** | **leaf `0` = `⟦self⟧`** | **leaf `5` = `⟦self.deref⟧`** | **✗** |

Patching **only** the RetLet-value leaf `5 → 0` closes the bridge
(`goals_eq refWp goals_patched = 1`), so that leaf is the **sole** divergence.

### Classification: serializer faithfulness gap (NOT refWp / NOT production)

- **refWp is faithful.** `ret_frame(f, RetLet(name,val)) = f ++ FLet(name,val)`
  (tactus-core/lib.rs:777) folds exactly the SST's `val` leaf (0 = `self`).
- **production is correct.** The return-var let binds `self.deref` (leaf 5) —
  the `&`-param `*self` rendered with the deref subst applied.
- **the serializer is the gap.** When it builds `RetBind.RetLet(name, val)`, it
  renders `val` as bare `self` (leaf 0) — the `*p → p.deref` subst production
  uses is **not** applied at the RetBind-value render site. Everywhere else in
  this fn the deref IS applied (ens leaf 2, oblig leaf 3, prod let leaf 5 all say
  `self.deref`). So the miss is site-specific: the RetBind-value leaf.

This is the **reference-parameter sibling of head_exec (bootstrap-18)** — same
class (empty/wrong RenderCtx does not replicate the `&`-param deref subst), a
**NEW site** (RetBind value, vs head_exec's obligation leaf). Together the two
findings show the deref-subst gap is systemic across leaf-render sites, so the
bootstrap-18 fix must thread production's deref RenderCtx through **both** the
`oblig_leaf`/ens path **and** the RetBind-value path. Batched onto bootstrap-18
(whose scope note already anticipated "any other RenderCtx-subst faithfulness
gaps W3 surfaces on tgt").

Stage A does not certify leaf rendering (DESIGN §2.5), so the bridge **soundly**
does not close. `run.sh` classifies it `HONEST-FAIL` with this recorded reason; a
honest-fail that later CLOSES (i.e. the serializer is fixed) is treated as a
regression to reclassify.

## Acceptance (task bootstrap-08 "done when")

- **tgt divergences = 0 UNEXPLAINED** ✓ — 1 divergence, fully triaged (serializer
  RetBind-value deref gap); 8 non-certs all have a known census bucket.
- **certified fraction reported** ✓ — 1/9 exec fns crate-wide (census-limited;
  8/9 are scope-rejections awaiting the Call + assert-query arms).
- **triage table complete** ✓ — DESIGN-W2-refwp.md §5 W3 entry + this REPORT.
- **production bugs pinned with e2e tests** — none found (the sole divergence is
  a serializer gap, spun/batched onto bootstrap-18, not a production bug).
- **bridge wall-clock ≤ package-gate cost** ✓ — ~1.2 s/fn (olean-import bound),
  far under the P2 2.8 s/600-stm baseline.

## Re-run when scope grows

When bootstrap-02b (`StmData::Call`) and the assert-query arm land, the other 8
tgt exec fns emit certs; re-run the cold emit + `run.sh` to bridge them. That is
where a broader bug-finding payoff (more real-corpus certs) will come from.

## Reproduce

    # regen the cert (cold, cert on, targeted; ~80s) — see run.sh header
    LEAN=<lean-v4.25.0> bash probe-w0/probe11_w3_tgt/run.sh   # bridges on-disk certs
    LEAN_PATH=tactus-core/out/lib:<prelude> lean probe-w0/probe11_w3_tgt/Pinpoint.lean

## Update 2026-07-24 (endgame A2, bootstrap-75): 3/3 CLOSE

apply_hom_gen + apply_hom_inv reclassified honest-fail → **CLOSE** (the
runner's LAX-REGRESS tripwire fired on the stale classification — the
discipline works). Root cause was the CLOSER GATE, not arg-temp LetRaw:
production never hoists user-`tactus_tactic` fns; the serializer now
mirrors the shared `closer_is_default` gate (wrap-mode plain lets),
renders ctx reqs via production's `build_req_binders`, and threads its
let-binder ledger into `cert_call_leaves`. Current table: 3 CLOSE
(clone, apply_hom_gen, apply_hom_inv) + 2 documented assert-forall
honest-fails (endgame A6). ALL CLASSIFIED ✓. Full writeup:
`board/bootstrap-75-a2-user-closer-wrap-mode.md`.
