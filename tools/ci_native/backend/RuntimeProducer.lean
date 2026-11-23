/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

import Lean.CoreM
import Lean.Util.ForEachExpr
import all Lean.Util.Path
import all Lean.Environment
import Lean.Compiler.Options
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.ModPkgExt

import all Lean.Compiler.CSimpAttr
import Lean.Compiler.LCNF.EmitC
import Lean.Language.Lean
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.Main
import all Lean.Compiler.LCNF.Specialize
-- `leanir` uses `lean_initialize_minimal`, which leaves initializing the `Lean`
-- modules to this module's import closure. These are the modules defining an `@[export]` whose
-- `@[extern]` counterpart is in that closure but which the closure does not otherwise reach.
import Lean.Meta.ExprDefEq
import Lean.Meta.LevelDefEq
import Lean.Meta.Match.MatchEqs
import Lean.Elab.PreDefinition.Structural.Eqns
import Lean.Parser

open Lean Compiler LCNF

structure RuntimeModule where
  name : String
  setup : String
  output : String
  deriving FromJson

structure RuntimeRequest where
  modules : Array RuntimeModule
  deriving FromJson

private def publishCIfClean (cFile : String) (text : String) (state : Core.State) : IO Unit := do
  for msg in state.messages.unreported do
    IO.eprintln (← msg.toString)
  if state.messages.hasErrors then
    throw <| IO.userError "compiler logged errors; runtime C rejected"
  let temp := cFile ++ ".partial"
  IO.FS.writeFile temp text
  IO.FS.rename temp cFile

private unsafe def produce (item : RuntimeModule) : IO Nat := do
  let setupFile := item.setup
  let cFile := item.output
  let setup ← ModuleSetup.load setupFile
  let modName := setup.name
  unless modName.toString == item.name do throw <| IO.userError "setup module identity mismatch"
  let opts := maxHeartbeats.set (Compiler.compiler.inLeanIR.set setup.options.toOptions true) 0
  enableInitializersExecution
  let env ← withImporting do
    let imports := #[{ module := modName, importAll := true : Import }]
    let (_, s) ← importModulesCore (globalLevel := .private) (loadIRSig := true)
      (arts := setup.importArts) imports |>.run
    finalizeImport (leakEnv := false) (loadExts := true) (level := .private) (loadIRSig := true) s imports opts
  let some modIdx := env.getModuleIdx? modName | throw <| IO.userError "missing module"
  let some mod := env.header.moduleData[modIdx]? | throw <| IO.userError "missing data"
  let names := mod.constNames.filter fun n =>
    if isNoncomputable env n || (IR.findEnvDecl env n).isNone then false else
    match env.find? n with
    | some (.defnInfo _) | some (.opaqueInfo _) => true
    | _ => false
  let env := (env.setMainModule modName).setModulePackage setup.package?
  let env := { env with base.private.header.imports := mod.imports, base.private.header.isModule := setup.isModule }
  let cacheExt := LCNF.Specialize.specCacheExt
  let cacheState := cacheExt.toEnvExtension.getState env
  let otherEntries := cacheState.importedEntries.mapIdx fun i entries => if i == modIdx then #[] else entries
  let cache := (mkStateFromImportedEntries LCNF.Specialize.addEntry {} otherEntries).switch
  let env := cacheExt.toEnvExtension.setState (asyncMode := .sync) env { cacheState with state := ([], cache) }
  let (res, finalState) ← (do
    LCNF.main names opts
    LCNF.emitC modName).toIO { fileName := cFile, fileMap := default, options := opts } { env }
  publishCIfClean cFile res finalState
  return names.size

public unsafe def main (args : List String) : IO UInt32 := do
  let ["--request", requestPath, "--result", resultPath] := args
    | throw <| IO.userError "usage: runtime-producer --request request.json --result result.json"
  let json ← IO.FS.readFile requestPath
  let request ← match Json.parse json >>= fromJson? (α := RuntimeRequest) with
    | .ok r => pure r
    | .error e => throw <| IO.userError e
  initSearchPathInternal
  let mut rows : Array Json := #[]
  let mut failed := false
  for item in request.modules do
    let start ← IO.monoMsNow
    let row ← try
      let n ← produce item
      pure <| Json.mkObj [("module",toJson item.name),("ok",toJson true),
        ("computational_declarations",toJson n),("output",toJson item.output),
        ("elapsed_ms",toJson ((← IO.monoMsNow)-start))]
    catch e =>
      failed := true
      pure <| Json.mkObj [("module",toJson item.name),("ok",toJson false),
        ("error",toJson e.toString),("elapsed_ms",toJson ((← IO.monoMsNow)-start))]
    rows := rows.push row
    IO.println row.compress
    let progress := Json.mkObj [("complete",toJson false),("results",toJson rows)]
    IO.FS.writeFile (resultPath ++ ".partial") progress.pretty
    IO.FS.rename (resultPath ++ ".partial") resultPath
  IO.FS.writeFile (resultPath ++ ".partial") <| (Json.mkObj [("complete",toJson true),("results",toJson rows)]).pretty
  IO.FS.rename (resultPath ++ ".partial") resultPath
  return if failed then 1 else 0
