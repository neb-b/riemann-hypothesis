/-
Bootstrap Lake metadata without elaborating the archived proofs.
This tool deliberately uses the pinned Lake's own hash and import-trace operations.
-/
module
import Lake
import Lake.Load.Workspace
import Lake.CLI.Main
import all Lake.Build.Module

open Lean Lake System

private def load (root : String) : IO Workspace := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let cfg ← (({rootDir := root, elanInstall?, leanInstall?, lakeInstall?} : LakeOptions).mkLoadConfig).toIO (IO.userError ∘ toString)
  let some ws ← (loadWorkspace cfg).toBaseIO
    | throw <| IO.userError "cannot load workspace"
  return ws

private def defaultModules (ws : Workspace) : IO (Array Lake.Module) := do
  let mut modules := #[]
  for lib in ws.root.leanLibs do
    if ws.root.defaultTargets.contains lib.name then
      modules := modules ++ (← lib.getModuleArray)
  return modules.qsort fun a b => a.name.toString < b.name.toString

private def waitForFile (path : FilePath) : FetchM Unit := do
  if ← path.pathExists then return
  let seconds := (← IO.getEnv "RIEMANN_CACHE_WAIT_SECONDS").bind String.toNat? |>.getD 0
  if seconds == 0 then return
  IO.eprintln s!"waiting for {path}"
  let deadline := (← IO.monoMsNow) + seconds * 1000
  while !(← path.pathExists) do
    if (← IO.monoMsNow) >= deadline then error s!"timed out waiting for {path}"
    IO.sleep 100

private def plan (ws : Workspace) (out : FilePath) : IO Unit := do
  IO.FS.createDirAll out.parent.get!
  let h ← IO.FS.Handle.mk out .write
  let modules ← defaultModules ws
  let names := modules.foldl (init := ({} : NameSet)) fun s mod => s.insert mod.name
  let mut seen : NameSet := {}
  for mod in modules do
    if seen.contains mod.name then continue
    seen := seen.insert mod.name
    let contents ← IO.FS.readFile mod.leanFile
    let header ← Lean.parseImports' contents mod.leanFile.toString
    if header.isModule then throw <| IO.userError s!"{mod.name}: bootstrap is for legacy modules only"
    unless mod.lib.extraDepTargets.isEmpty && mod.lib.config.needs.isEmpty &&
      mod.pkg.extraDepTargets.isEmpty && !mod.shouldPrecompile && mod.pkg.externLibs.isEmpty &&
      mod.dynlibs.isEmpty && mod.plugins.isEmpty do
      throw <| IO.userError s!"{mod.name}: unsupported extra build dependencies"
    for imp in header.imports do
      if let some dep := ws.findModule? imp.module then
        if dep.pkg.keyName == ws.root.keyName && !names.contains dep.name then
          throw <| IO.userError s!"{mod.name}: root import {dep.name} is outside the planned default libraries"
    let setup : ModuleSetup := {
      name := mod.name, package? := mod.pkg.id?, isModule := false,
      options := mod.leanOptions
    }
    let imports := header.imports.map fun imp => Json.mkObj [
      ("module", toJson imp.module),
      ("package", toJson ((ws.findModule? imp.module).bind (·.pkg.id?)))
    ]
    let job := Json.mkObj [
      ("name", toJson mod.name), ("source", toJson mod.leanFile),
      ("olean", toJson mod.oleanFile), ("ilean", toJson mod.ileanFile),
      ("c", toJson mod.cFile), ("trace", toJson mod.traceFile),
      ("setup", toJson setup), ("leanArgs", toJson mod.leanArgs),
      ("imports", toJson imports)
    ]
    h.putStrLn job.compress
  IO.println s!"planned {seen.size} modules in {out}"

private def traceOptions (opts : LeanOptions) : BuildTrace :=
  opts.values.foldl (init := .nil "options") fun t n v =>
    let opt := s!"-D{n}={v.asCliFlagValue}"
    t.mix <| .ofHash (pureHash opt) opt

private structure State where
  exports : NameMap ModuleExportInfo := {}
  visiting : NameSet := {}
  count : Nat := 0
  mappings : CacheMap := {}

private abbrev BootstrapM := StateRefT State FetchM

private partial def traceModule (mod : Lake.Module) : BootstrapM ModuleExportInfo := do
  if let some info := (← get).exports.find? mod.name then return info
  let ws ← getWorkspace
  if mod.pkg.keyName != ws.root.keyName then
    let info ← (← mod.exportInfo.fetch).await
    modify fun s => {s with exports := s.exports.insert mod.name info}
    return info
  if (← get).visiting.contains mod.name then error s!"cyclic import: {mod.name}"
  modify fun s => {s with visiting := s.visiting.insert mod.name}
  let contents ← IO.FS.readFile mod.leanFile
  let header ← Lean.parseImports' contents mod.leanFile.toString
  if header.isModule then error s!"{mod.name}: module system not supported by this bootstrap"
  unless mod.dynlibs.isEmpty && mod.plugins.isEmpty do
    error s!"{mod.name}: bootstrap does not support dynlibs or plugins"
  let input : BuildTrace := {caption := mod.leanFile.toString, hash := .ofText contents, mtime := ← getMTime mod.leanFile}
  let mut info := ModuleImportInfo.nil mod.name
  for imp in header.imports do
    if let some dep := ws.findModule? imp.module then
      let exp ← traceModule dep
      info := info.addImport true imp exp
  let extra ← mod.lib.extraDep.fetch
  discard extra.await
  let deps := (BuildTrace.nil "deps").mix extra.getTrace |>.mix info.trace
  let libs := (BuildTrace.nil "libs")
    |>.mix (.nil "import dynlibs")
    |>.mix (.nil "package external libraries")
    |>.mix (.nil "module dynlibs")
    |>.mix (.nil "module plugins")
  let lean := BuildTrace.ofHash (pureHash ws.lakeEnv.leanGithash) "Lean"
  let trace := (BuildTrace.nil mod.name.toString) |>.mix deps |>.mix libs
  let trace := if mod.platformIndependent == some false then trace.mix platformTrace else trace
  let trace := trace |>.mix lean |>.mix input
    |>.mix (traceOptions mod.leanOptions)
    |>.mix (.ofHash (pureHash false) "isModule")
    |>.mix (.ofHash (pureHash mod.name) "name")
    |>.mix (.ofHash (pureHash mod.pkg.id?) "pkg")
    |>.mix (.ofHash (pureHash mod.leanArgs) "args")
  let cache := ws.lakeCache
  waitForFile mod.cFile
  let o ← cache.saveArtifact mod.oleanFile "olean" (useLocalFile := true)
  let i ← cache.saveArtifact mod.ileanFile "ilean" (useLocalFile := true)
  let c ← cache.saveArtifact mod.cFile "c" (useLocalFile := true)
  let outputs : ModuleOutputDescrs := {isModule := false, olean := o.descr, ilean := i.descr, c := c.descr}
  -- Mark the trace as synthetic, just as a normal artifact-cache fetch would.
  let temporary := mod.traceFile.addExtension "writing"
  IO.FS.writeFile temporary ((toJson (BuildMetadata.ofFetch trace.hash (toJson outputs))).compress)
  IO.FS.rename temporary mod.traceFile
  cache.writeOutputs mod.pkg.cacheScope trace.hash outputs
  let artsTrace := (BuildTrace.nil s!"{mod.name}:importArts").mix o.trace
  let allArtsTrace := (BuildTrace.nil s!"{mod.name}:importAllArts").mix o.trace
  let exp : ModuleExportInfo := {
    srcTrace := input, arts := ⟨#[#[mod.oleanFile]]⟩,
    artsTrace, metaArtsTrace := artsTrace,
    allArts := ⟨#[#[mod.oleanFile]]⟩, allArtsTrace,
    transTrace := info.transTrace,
    metaTransTrace := info.metaTransTrace,
    allTransTrace := info.allTransTrace,
    legacyTransTrace := info.legacyTransTrace
  }
  modify fun s => {s with
    exports := s.exports.insert mod.name exp
    visiting := s.visiting.erase mod.name
    count := s.count + 1
    mappings := s.mappings.insert trace.hash outputs
  }
  if (← get).count % 1000 == 0 then IO.eprintln s!"indexed {(← get).count} root modules"
  return exp

private def index (ws : Workspace) (out : FilePath) (only : List String) : IO Unit := do
  let modules ← if only.isEmpty then defaultModules ws else only.toArray.mapM fun name => do
    let some mod := ws.findModule? name.toName | throw <| IO.userError s!"unknown module {name}"
    pure mod
  let action : BootstrapM Unit := do
    for mod in modules do discard <| traceModule mod
  let (_, state) ← ws.runFetchM (action.run {}) {verbosity := .quiet, noBuild := true}
  -- Export only root-package mappings; dependency cache entries are never published.
  let some _ ← LoggerIO.toBaseIO (CacheMap.writeFile out state.mappings : LoggerIO Unit)
    | throw <| IO.userError "cannot write mappings"
  IO.println s!"wrote {state.mappings.size} mappings to {out}"

private def pack (ws : Workspace) (jobs : FilePath) (out : FilePath) : IO Unit := do
  let input ← IO.FS.Handle.mk jobs .read
  let action : FetchM CacheMap := do
    let mut mappings : CacheMap := {}
    let mut count := 0
    repeat
      let line ← input.getLine
      if line.isEmpty then break
      let .ok job := Json.parse line | error "invalid job JSON"
      let .ok name := job.getObjValAs? String "name" | error "job has no name"
      let some mod := ws.findModule? name.toName | error s!"unknown module {name}"
      waitForFile mod.traceFile
      let .ok metadata := BuildMetadata.parse (← IO.FS.readFile mod.traceFile)
        | error s!"invalid trace for {name}"
      let some outputs := metadata.outputs? | error s!"trace has no outputs for {name}"
      let .ok (descrs : ModuleOutputDescrs) := fromJson? outputs
        | error s!"invalid outputs for {name}"
      -- Cached files can be hard links and read-only. Replace, never overwrite,
      -- an archive left by an earlier bootstrap with different inputs.
      if ← mod.ltarFile.pathExists then IO.FS.removeFile mod.ltarFile
      let ltar ← (← Job.async do
        let arts ← descrs.resolve none none
        mod.packLtar arts).await
      -- packLtar only computes the artifact when automatic caching is disabled.
      -- Store it explicitly so the isolated staging step can resolve it.
      let cached ← ws.lakeCache.saveArtifact ltar.path "ltar"
      mappings := mappings.insert metadata.depHash cached.descr
      count := count + 1
      if count % 1000 == 0 then IO.eprintln s!"packed {count} module archives"
    return mappings
  let mappings ← ws.runFetchM action {verbosity := .quiet, noBuild := true}
  let some _ ← LoggerIO.toBaseIO (CacheMap.writeFile out mappings : LoggerIO Unit)
    | throw <| IO.userError "cannot write packed mappings"
  IO.println s!"wrote {mappings.size} archive mappings to {out}"

public def main (args : List String) : IO Unit := do
  match args with
  | "plan" :: root :: out :: [] => plan (← load root) out
  | "index" :: root :: out :: only => index (← load root) out only
  | "pack" :: root :: jobs :: out :: [] => pack (← load root) jobs out
  | _ => throw <| IO.userError "usage: trace-cache plan ROOT JOBS.jsonl | trace-cache index ROOT OUTPUTS.jsonl [MODULE ...] | trace-cache pack ROOT JOBS.jsonl OUTPUTS.jsonl"
