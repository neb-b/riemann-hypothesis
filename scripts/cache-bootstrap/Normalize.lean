/-
Adapt the published legacy-module oleans to the Lake package name, without
elaborating theorem bodies, and emit stock initialization-only C where possible.

Usage: normalize-cache --jobs JOBS.jsonl --report REPORT.jsonl

Each job has `name`, `olean`, `c`, `package` (string or null), and `imports`, an
array of {module, package} objects. The package can instead come from the
`setup.package` field of a stock Lean ModuleSetup object. Import package IDs must
describe the normalized workspace, including implicit Init imports.

The report marks modules containing compiler output as `needsCompile`; their C
must be produced by Lean before constructing or publishing Lake mappings. This
program never fabricates C for computational definitions or initializers.
-/
module

import all Lean.Environment
import all Lean.Compiler.ModPkgExt
import Lean
import Lean.Compiler.LCNF.EmitC

open Lean System

namespace CacheBootstrap

private def field (j : Json) (name : String) : IO Json :=
  match j.getObjVal? name with
  | .ok value => pure value
  | .error error => throw <| IO.userError error

private def stringField (j : Json) (name : String) : IO String := do
  match (← field j name).getStr? with
  | .ok value => pure value
  | .error error => throw <| IO.userError s!"{name}: {error}"

private def packageOf (j : Json) : IO (Option PkgId) := do
  let value ← match j.getObjVal? "package" with
    | .ok value => pure value
    | .error _ => field (← field j "setup") "package"
  match value with
  | .null => pure none
  | .str value => pure (some value)
  | _ => throw <| IO.userError "package must be a string or null"

private def getImportPackages (j : Json) : IO (Std.HashMap Name (Option PkgId)) := do
  let .ok imports := (← field j "imports").getArr?
    | throw <| IO.userError "imports must be an array"
  imports.foldlM (init := {}) fun packages imp => do
    let name := (← stringField imp "module").toName
    return packages.insert name (← packageOf imp)

private def hasRuntimeCode (data : ModuleData) : Bool :=
  data.entries.any fun (name, entries) =>
    (name == `Lean.Compiler.LCNF.impureSigExt || name == `Lean.IR.declMapExt)
      && !entries.isEmpty

private unsafe def normalizePackage
    (data : ModuleData) (expected : Option PkgId) : IO (ModuleData × Bool) := do
  let mut found := false
  let mut changed := false
  let mut rewritten := #[]
  for (name, entries) in data.entries do
    if name != modPkgExt.name then
      rewritten := rewritten.push (name, entries)
      continue
    if entries.size != 1 then
      throw <| IO.userError "unexpected package-extension entry count"
    found := true
    let some entry := entries[0]?
      | throw <| IO.userError "empty package-extension metadata"
    let actual : Option PkgId := unsafeCast entry
    if actual == expected then
      rewritten := rewritten.push (name, entries)
      continue
    if actual.isSome then
      throw <| IO.userError s!"published module has unexpected package {actual}"
    changed := true
    let entry : EnvExtensionEntry := unsafeCast expected
    rewritten := rewritten.push (name, #[entry])
  unless found do
    throw <| IO.userError "published module has no package-extension metadata"
  return ({data with entries := rewritten}, changed)

private def emitInitOnly (base : Environment) (mod : Name) (data : ModuleData)
    (package : Option PkgId) (packages : Std.HashMap Name (Option PkgId)) : IO String := do
  if data.isModule || hasRuntimeCode data then
    throw <| IO.userError "initialization-only emission requires a legacy module without runtime code"
  let mods := data.imports.map fun imp =>
    ({imp with irPhases := .all, hasData := true} : EffectiveImport)
  let (_, indices) := mods.foldl
    (init := ((0, {}) : Nat × Std.HashMap Name ModuleIdx)) fun (i, indices) imp =>
      (i + 1, indices.insert imp.module i)
  let importedPackages ← mods.mapM fun imp => do
    let some package := packages[imp.module]?
      | throw <| IO.userError s!"missing package metadata for import {imp.module}"
    return #[package]
  let kernel := private_decl% {base.toKernelEnv with
    header := {base.header with
      mainModule := mod
      imports := data.imports
      modules := mods
      moduleName2Idx := indices}}
  let env := {base with base.private := kernel, checked := .pure kernel}
  let env := modPkgExt.toEnvExtension.setState env
    {importedEntries := importedPackages, state := package}
  let (output, _) ← (Compiler.LCNF.emitC mod).toIO
    {fileName := "cache bootstrap", fileMap := default} {env}
  return output

private unsafe def processJob (base : Environment) (j : Json) : IO Json := do
  let name ← stringField j "name"
  let mod := name.toName
  let olean := FilePath.mk (← stringField j "olean")
  let c := FilePath.mk (← stringField j "c")
  let package ← packageOf j
  let packages ← getImportPackages j
  let (original, region) ← readModuleData olean
  if original.isModule then
    throw <| IO.userError s!"{name}: split module-system oleans are unsupported"
  let needsCompile := hasRuntimeCode original
  let (data, normalized) ← normalizePackage original package
  if normalized then
    -- The input is memory mapped. Save to another inode before atomic replacement.
    let temporary := olean.addExtension "normalizing"
    saveModuleData temporary mod data
    IO.FS.rename temporary olean
  unless needsCompile do
    let output ← emitInitOnly base mod data package packages
    if let some parent := c.parent then IO.FS.createDirAll parent
    -- A previous index may have hard-linked this path into the read-only cache.
    -- Replace its inode; never overwrite a cached artifact through a hard link.
    let temporary := c.addExtension "normalizing"
    IO.FS.writeFile temporary output
    IO.FS.rename temporary c
  region.free
  return Json.mkObj [
    ("name", toJson name),
    ("normalized", toJson normalized),
    ("needsCompile", toJson needsCompile),
    ("olean", toJson olean.toString),
    ("c", toJson c.toString)]

end CacheBootstrap

public unsafe def main (args : List String) : IO UInt32 := do
  let ["--jobs", jobs, "--report", report] := args
    | throw <| IO.userError "usage: normalize-cache --jobs JOBS.jsonl --report REPORT.jsonl"
  let input ← IO.FS.Handle.mk jobs .read
  let output ← IO.FS.Handle.mk report .write
  let base ← mkEmptyEnvironment
  let mut count := 0
  let mut compiled := 0
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    if line.trimAscii.toString.isEmpty then continue
    let .ok job := Json.parse line
      | throw <| IO.userError s!"invalid JSON at job {count + 1}"
    let result ← CacheBootstrap.processJob base job
    output.putStrLn result.compress
    count := count + 1
    if (result.getObjValAs? Bool "needsCompile").toOption.getD false then
      compiled := compiled + 1
    if count % 1000 == 0 then
      output.flush
      IO.eprintln s!"normalized {count} modules; {compiled} require compilation"
  output.flush
  IO.eprintln s!"normalized {count} modules; {compiled} require compilation"
  return 0
