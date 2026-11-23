/- Pack only completed raw outputs verified by stock no-build trace checking. -/
module
import Lake
import all Lake.CLI.Main
import all Lake.Load.Workspace
import all Lake.Build.Module
import all Lake.Build.Run
open Lake Lean System

public def main (args : List String) : IO Unit := do
  let (args, width) := if args.length == 5 then
      (args.take 4, args[4]!.toNat?.getD 0) else (args, 8)
  let [root, jobs, report, overrides] := args
    | throw <| IO.userError "expected root jobs report package-overrides [workers]"
  unless 1 ≤ width ∧ width ≤ 32 do
    throw <| IO.userError "recovery workers must be between 1 and 32"
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let options : LakeOptions := {
    rootDir := root, configFile := "lakefile.toml", updateToolchain := false,
    elanInstall?, leanInstall?, lakeInstall?,
    packageOverrides := ← Manifest.loadEntries overrides
  }
  let config ← options.mkLoadConfig.toIO (IO.userError ∘ toString)
  let some ws ← (loadWorkspace config).toBaseIO
    | throw <| IO.userError "cannot load recovery workspace"
  let .ok names := Json.parse (← IO.FS.readFile jobs)
    | throw <| IO.userError "invalid recovery jobs"
  let .ok (names : Array String) := fromJson? names
    | throw <| IO.userError "invalid recovery module list"
  let output ← IO.FS.Handle.mk report .write
  let action : FetchM Unit := do
    let mut offset := 0
    while offset < names.size do
      let mut pending : Array (String × Lake.Job Json) := #[]
      for name in names.extract offset (offset + width) do
        try
          let some mod := ws.findModule? name.toName | error s!"unknown module {name}"
          -- Stock Lake constructs its shared import graph on one thread.
          let artsJob ← mod.leanArts.fetch
          let job ← Job.async do
            -- noBuild=true forbids theorem elaboration and missing code generation.
            let arts ← artsJob.await
            let .ok metadata := BuildMetadata.parse (← IO.FS.readFile mod.traceFile)
              | error "invalid completed module trace"
            let some descrs := metadata.outputs? | error "completed trace has no output hashes"
            let .ok (expected : ModuleOutputDescrs) := fromJson? descrs
              | error "invalid completed output description"
            let expectedJson := toJson expected
            let actual := toJson arts.descrs
            for key in #["m", "o", "i", "rs", "r", "c", "b"] do
              if let .ok value := expectedJson.getObjVal? key then
                let .ok got := actual.getObjVal? key | error s!"missing completed output {key}"
                unless got == value do error s!"completed output hash differs: {key}"
            -- Only emit outputs attested by the saved trace. Deferred code may
            -- exist on disk without a saved output hash; it is not cache data.
            let arts := {arts with
              irSig? := if expected.irSig?.isSome then arts.irSig? else none
              ir? := if expected.ir?.isSome then arts.ir? else none
              bc? := if expected.bc?.isSome then arts.bc? else none
              ltar? := none
              -- OPTIONAL_C_436
            }
            -- An interrupted pack may leave arbitrary partial bytes. Never accept
            -- it by hashing: replace it with a fresh successful stock pack.
            if ← mod.ltarFile.pathExists then IO.FS.removeFile mod.ltarFile
            let packed ← mod.packLtar arts
            let cached ← ws.lakeCache.saveArtifact packed.path "ltar"
            return Json.mkObj [("name", toJson name), ("ok", toJson true),
              ("input", toJson metadata.depHash.toString), ("artifact", toJson cached.descr.relPath.toString)]
          pending := pending.push (name, job)
        catch _ =>
          output.putStrLn (Json.mkObj [("name", toJson name), ("ok", toJson false)]).compress
          output.flush
      -- Only this serial writer emits decisions; at most width stock jobs run.
      for (name, job) in pending do
        try
          output.putStrLn (← job.await).compress
        catch _ =>
          output.putStrLn (Json.mkObj [("name", toJson name), ("ok", toJson false)]).compress
        output.flush
      offset := offset + width
  ws.runFetchM action {verbosity := .quiet, noBuild := true, trustHash := false}
