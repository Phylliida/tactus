/-
Tactus persistent Lean driver.

One process per verus run. Speaks JSON-lines on stdin/stdout:

  → {"op":"snapshot","key":"S1","modules":["TactusDefs", ...]}
  ← {"ok":true,"ms":1023}

  → {"op":"check","snapshot":"S1","file":"/abs/x.lean","module":"pkg_x",
     "olean":"/abs/x.olean"}          -- "olean" optional
  ← {"ok":false,"ms":31,"diags":[{"sev":"error","line":6,"col":2,"msg":"..."}]}

  → {"op":"exit"}

A snapshot is an `importModules (loadExts := true)` environment — built
once (~1s), then every `check` elaborates the file's post-header
commands against a fresh `Command.mkState` branch of it (~ms, exact
isolation: environments are immutable values). The caller (lean_process
.rs) is the authority that a file's header imports are a subset of the
snapshot's modules; the driver re-parses the header only to skip it.
`writeModule` on the branched env serializes ONLY the branch-local
decls with the snapshot's modules as recorded imports — an ordinary
olean the Link gate consumes unchanged (validated by
probes/driver-olean-roundtrip.lean).

Replies are single lines; nothing else is written to stdout. Any
uncaught exception in a request becomes {"ok":false,"fatal":...} so
the Rust side can fall back to process-per-file.
-/
import Lean
open Lean Elab

namespace TactusDriver

structure Reply where
  ok : Bool
  ms : Nat := 0
  diags : Array Json := #[]
  fatal : Option String := none

def Reply.render (r : Reply) : Json :=
  let base := [("ok", Json.bool r.ok), ("ms", ToJson.toJson r.ms)]
  let base := if r.diags.isEmpty then base else base ++ [("diags", Json.arr r.diags)]
  let base := match r.fatal with
    | some m => base ++ [("fatal", Json.str m)]
    | none => base
  Json.mkObj base

def sevStr : MessageSeverity → String
  | .error => "error"
  | .warning => "warning"
  | .information => "info"

def msgToDiag (m : Message) : IO Json := do
  let text ← m.data.toString
  return Json.mkObj [
    ("sev", Json.str (sevStr m.severity)),
    ("line", ToJson.toJson m.pos.line),
    ("col", ToJson.toJson m.pos.column),
    ("msg", Json.str text)]

/-- Elaborate `file`'s post-header commands against a branch of `env`;
    write `olean?` on success. Returns the reply (never throws). -/
unsafe def runCheck (env : Environment) (file : String) (module : Name)
    (olean? : Option String) : IO Reply := do
  let t0 ← IO.monoMsNow
  let src ← IO.FS.readFile ⟨file⟩
  let inputCtx := Parser.mkInputContext src file
  let (_, parserState, headerMsgs) ← Parser.parseHeader inputCtx
  let env := env.setMainModule module
  let cmdState := Command.mkState env headerMsgs {}
  let s ← IO.processCommands inputCtx parserState cmdState
  let msgs := s.commandState.messages.toList
  let errs := msgs.filter (·.severity == .error)
  let diags ← (msgs.filter (·.severity != .information)).mapM msgToDiag
  if errs.isEmpty then
    if let some o := olean? then
      if let some parent := (System.FilePath.mk o).parent then
        IO.FS.createDirAll parent
      writeModule s.commandState.env ⟨o⟩
  let t1 ← IO.monoMsNow
  return { ok := errs.isEmpty, ms := t1 - t0, diags := diags.toArray }

unsafe def handle (snaps : IO.Ref (Std.HashMap String Environment))
    (j : Json) : IO (Option Reply) := do
  match j.getObjValAs? String "op" with
  | .ok "exit" => return none
  | .ok "snapshot" => do
    let t0 ← IO.monoMsNow
    let key ← IO.ofExcept (j.getObjValAs? String "key")
    let mods ← IO.ofExcept (j.getObjValAs? (Array String) "modules")
    let imports := mods.map fun m => { module := m.toName : Import }
    let env ← importModules imports {} (trustLevel := 0) (loadExts := true)
    snaps.modify (·.insert key env)
    let t1 ← IO.monoMsNow
    return some { ok := true, ms := t1 - t0 }
  | .ok "check" => do
    let key ← IO.ofExcept (j.getObjValAs? String "snapshot")
    let file ← IO.ofExcept (j.getObjValAs? String "file")
    let module ← IO.ofExcept (j.getObjValAs? String "module")
    let olean? := (j.getObjValAs? String "olean").toOption
    match (← snaps.get).get? key with
    | some env => return some (← runCheck env file module.toName olean?)
    | none => return some { ok := false, fatal := s!"unknown snapshot {key}" }
  | .ok op => return some { ok := false, fatal := s!"unknown op {op}" }
  | .error e => return some { ok := false, fatal := s!"bad request: {e}" }

unsafe def driverMain : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let snaps ← IO.mkRef (∅ : Std.HashMap String Environment)
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  -- readiness line: Rust side waits for this before sending requests
  stdout.putStrLn (Json.mkObj [("ready", Json.bool true)]).compress
  stdout.flush
  repeat do
    let line ← stdin.getLine
    if line.trim.isEmpty then break   -- EOF
    let reply ← try
      match Json.parse line with
      | .ok j => handle snaps j
      | .error e => pure (some { ok := false, fatal := s!"parse: {e}" })
    catch ex =>
      pure (some { ok := false, fatal := s!"exception: {ex}" })
    match reply with
    | some r =>
      stdout.putStrLn r.render.compress
      stdout.flush
    | none => break

end TactusDriver

unsafe def main (_ : List String) : IO Unit := TactusDriver.driverMain
