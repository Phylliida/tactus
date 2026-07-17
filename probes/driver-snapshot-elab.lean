import Lean
open Lean Elab

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let t0 ← IO.monoMsNow
  let env ← importModules #[{module := `TactusDefs}] {} (trustLevel := 0) (loadExts := true)
  let t1 ← IO.monoMsNow
  IO.println s!"importModules(loadExts): {t1-t0}ms"
  let src := "theorem probe_thm (a b : Int) (h : 0 ≤ a) : a + b = b + a := by omega\n"
  for i in [0:5] do
    let tA ← IO.monoMsNow
    let inputCtx := Parser.mkInputContext src s!"<probe{i}>"
    let (_, parserState, _) ← Parser.parseHeader inputCtx
    let cmdState := Command.mkState env {} {}
    let s ← IO.processCommands inputCtx parserState cmdState
    let tB ← IO.monoMsNow
    let errs := s.commandState.messages.toList.filter (·.severity == .error)
    IO.println s!"elab {i}: {tB-tA}ms errors={errs.length} thm={(s.commandState.env.find? `probe_thm).isSome}"
    for m in errs do IO.println s!"  [err] {← m.data.toString}"
