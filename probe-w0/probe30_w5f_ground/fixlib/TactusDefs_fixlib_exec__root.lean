-- ══════════════════════════════════════════════════════════════════════
-- fixlib — the RENAMED bootstrap-fixture def cone (board bootstrap-57, obstacle D).
--
-- The bootstrap-fixture emits its user spec fns into module `TactusDefs_lib_exec__root`
-- under namespace `lib` — the SAME module name + namespace tactus-core uses for
-- `lib.render_exp`/`lib.ExprData`/… . The Lean loader resolves ONE olean per module
-- name, so a probe cannot put both on LEAN_PATH: importing the fixture's `lib.sq`
-- shadows tactus-core's `lib.render_exp`. Rung 1 pays the one-time "plumbing tax":
-- re-emit the fixture's def cone under a DISTINCT module prefix (`TactusDefs_lib_exec`
-- → `TactusDefs_fixlib_exec`) and a DISTINCT namespace (`lib.` → `fixlib.`) so the two
-- crates are importable TOGETHER.
--
-- HONESTY NOTE (the bootstrap claim): the def BODIES below are VERBATIM from the
-- emitter's output `bootstrap-fixture/out/lib/TactusDefs_lib_exec__root.lean:7-8,15-22`
-- — `x * x` / `a + b` / `a + b + c` character-for-character, including the emitter's
-- blanket `noncomputable` and the `set_option` header. ONLY the module name and the
-- `lib.` → `fixlib.` symbol prefix are rewritten. This is a rename of emitter OUTPUT,
-- not a probe-local hand-authored fn (which would bypass the emitter-output pin and
-- invalidate the grounding — Danielle's model, recon point D). sq/g2/g3 have no
-- dependency beyond Nat, so this module imports only `TactusPrelude` (the fixture's
-- `__base` cone — Seq/Set/Tree machinery — is not needed for the rung-1 fns; rung 3's
-- `fixlib.tree_head`/`fixlib.Tree` will pull it in when that rung lands).
--
-- RUNG 2 addition (board bootstrap-57): the `Point` record, VERBATIM-renamed from the
-- emitter's `bootstrap-fixture/out/lib/TactusDefs_lib_exec__base.lean:40-43`
-- (`structure lib.Point where x : Int; y : Int deriving Inhabited`) — only `lib.` →
-- `fixlib.`. This is the REAL emitted datatype; rung-2 grounds the `proj` leaf oracle
-- against its genuine `.x`/`.y` structure projections (not a hand-written pair), the
-- faithful analog of rung-1 grounding `fn` against `fixlib.sq`.
--
-- RUNG 3 addition (board bootstrap-57): the `Tree` ENUM + `tree_head` match-bodied fn,
-- VERBATIM-renamed from the emitter's
-- `bootstrap-fixture/out/lib/TactusDefs_lib_exec__base.lean:22-25` (the `inductive
-- lib.Tree | Leaf (val0 : Int) | Node (val0 val1 : Box Tree)`) and
-- `…__root.lean:13-14` (`def lib.tree_head (t:Tree):Int := match t with | Leaf v => v
-- | Node _l _r => 0`) — only `lib.` → `fixlib.`. This is the REAL emitted enum + the
-- ONLY real Match-carrying user fn on the slice (recon C); rung-3 grounds the
-- `ctorTag`/`ctorField` leaf oracles against a genuine encoding of this `Tree`, tied to
-- this `tree_head`. The emitted per-ctor accessor/`height` simp defs
-- (`Tree.isLeaf`/`Leaf_val0`/…, `__base.lean:26-39`) are NOT needed for the grounding
-- (the match denotes through `ctorTag`/`ctorField`, not the Lean projections) and — like
-- the unused sq/g2/g3 deps — are omitted; `Tree` needs only `Tactus.Box` (prelude).
-- ══════════════════════════════════════════════════════════════════════
import TactusPrelude
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
noncomputable def fixlib.sq (x : Nat) : Nat :=
  x * x
noncomputable def fixlib.g2 (a : Nat) (b : Nat) : Nat :=
  a + b
noncomputable def fixlib.g3 (a : Nat) (b : Nat) (c : Nat) : Nat :=
  a + b + c
structure fixlib.Point where
  x : Int
  y : Int
  deriving Inhabited
inductive fixlib.Tree where
  | Leaf (val0 : Int)
  | Node (val0 : Tactus.Box fixlib.Tree) (val1 : Tactus.Box fixlib.Tree)
  deriving Inhabited
noncomputable def fixlib.tree_head (t : fixlib.Tree) : Int :=
  match t with | fixlib.Tree.Leaf v => v | fixlib.Tree.Node _l _r => 0
