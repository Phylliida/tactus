# probe38 — b70/b71 close-out (endgame A1)

Post-b74 closing evidence for the two serializer-arm cards, regenerated
from the LIVE fixture certs on every run (`run.sh`).

| claim | example | result 2026-07-24 |
|---|---|---|
| b71 ∀-path caller bridges (use_clamped, F21) | `goals_eq (ref_wp …) goals = 1` | close |
| b71 kill A: drop ret-bound FHyp from Call post frame | `… = 0` | flips |
| b71 kill B: swap ret-bound ↔ ens FHyps | `… = 0` | flips |
| b70 generic Call precondition goal closes (vec_read goal 0) | `gl_nth_eq … 0 = 1` | close |
| b70 kill: perturb transcribed req atom | `gl_nth_eq … 0 = 0` | flips |
| A7 tripwire: vec_read goal 1 = documented stage-B honest-fail | `gl_nth_eq … 1 = 0` | holds |

The A7 tripwire fires (run goes red) the day the stage-B
callee-signature vocabulary lands and vec_read's Ret goal closes —
replace it with a close+kill pair then. Never a silent cap (P2,
`DESIGN-bootstrap-endgame.md` §1).

`gl_nth`/`gl_nth_eq` are probe-local noncomputable defs over the
emitted mirror vocabulary (Nat-structural recursion, Box via `.deref`)
— the per-goal probing idiom from the b74 triage, made a standing
artifact.
