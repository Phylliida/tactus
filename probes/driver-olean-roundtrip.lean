import Lean
open Lean Elab

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{module := `TactusDefs}] {} (trustLevel := 0) (loadExts := true)
  -- elaborate a module body from the snapshot, as module `ProbeMod`
  let src := "theorem probe_thm (a b : Int) (h : 0 ≤ a) : a + b = b + a := by omega\n"
  let inputCtx := Parser.mkInputContext src "ProbeMod"
  let (_, parserState, _) ← Parser.parseHeader inputCtx
  let env := env.setMainModule `ProbeMod
  let cmdState := Command.mkState env {} {}
  let s ← IO.processCommands inputCtx parserState cmdState
  let errs := s.commandState.messages.toList.filter (·.severity == .error)
  IO.println s!"elab errors: {errs.length}"
  -- write the olean: local decls only (probe_thm), imports recorded from the base env
  let out := System.FilePath.mk "PROBE_OUT" / "ProbeMod.olean"
  writeModule s.commandState.env out
  IO.println s!"olean written: {← out.pathExists}"
  -- fresh import in the SAME process (fresh region): load it back next to TactusDefs
  let env2 ← importModules #[{module := `ProbeMod}] {} (trustLevel := 0) (loadExts := true)
  IO.println s!"reimport ok, probe_thm found: {(env2.find? `probe_thm).isSome}"
  -- axiom check on the reloaded theorem (what Link's closure check does)
  match env2.find? `probe_thm with
  | some ci =>
      let (_, st) := ((CollectAxioms.collect `probe_thm).run env2).run {}
      IO.println s!"axioms of probe_thm: {st.axioms.toList}"
      let _ := ci
  | none => IO.println "missing!"
