/-
Attest published Lake extras against the preserved, package-normalized oleans.

Usage: attest-extras JOBS.jsonl REPORT.jsonl [TEMP_DIRECTORY]
Each job: {"name": "Module.Name", "olean": "path", "expected": "16-hex-Lake-hash"}.
Optional `source` is the EXTERNAL build's source filename used in lint messages.

An exact byte hash match is accepted directly. Otherwise, a temporary copy may
change only LintEntry.file and LintEntry.message.fileName, leaving all constants,
compiler IR, initialization metadata and other extension entries unchanged.
The preserved input file is never overwritten. No target module is imported.
-/
module

import Lake
import Lean.Linter.PersistentLintLog

open Lean Lake System

namespace AttestExtras

private def getString (job : Json) (name : String) : IO String :=
  match job.getObjValAs? String name with
  | .ok value => pure value
  | .error error => throw <| IO.userError error

private unsafe def attest (job : Json) (temporary : FilePath) : IO Json := do
  let name ← getString job "name"
  let olean := FilePath.mk (← getString job "olean")
  let expectedString ← getString job "expected"
  let some expected := Hash.ofString? expectedString
    | throw <| IO.userError s!"{name}: expected a hexadecimal Lake hash"
  let actual ← computeBinFileHash olean
  let mut mode := "exact"
  let mut candidate := actual
  let mut lintCount := 0
  if actual != expected then
    let source := (job.getObjValAs? String "source").toOption.getD
      ("/home/jack/rh-check/proj/lean/src/" ++ name.replace "." "/" ++ ".lean")
    let (data, region) ← readModuleData olean
    if data.isModule then
      throw <| IO.userError s!"{name}: split module-system oleans are unsupported"
    let entries := data.entries.map fun (extension, values) =>
      if extension == `Lean.Linter.lintLogExt then
        let lints : Array Linter.LintEntry := unsafeCast values
        let lints := lints.map fun lint =>
          {lint with file := source, message.fileName := source}
        (extension, unsafeCast lints)
      else (extension, values)
    for (extension, values) in data.entries do
      if extension == `Lean.Linter.lintLogExt then lintCount := values.size
    if lintCount > 0 then
      saveModuleData temporary name.toName {data with entries}
      candidate ← computeBinFileHash temporary
      mode := if candidate == expected then "lint-only" else "mismatch"
      IO.FS.removeFile temporary
    else
      mode := "mismatch"
    region.free
  return Json.mkObj [
    ("name", toJson name), ("olean", toJson olean.toString),
    ("expected", toJson expected.toString), ("actual", toJson actual.toString),
    ("candidate", toJson candidate.toString), ("mode", toJson mode),
    ("lintEntries", toJson lintCount),
    ("compatible", toJson (mode != "mismatch"))]

end AttestExtras

public unsafe def main (args : List String) : IO UInt32 := do
  let (jobs, report, directory) ← match args with
    | [jobs, report] => pure (jobs, report, (FilePath.mk report).parent.getD ".")
    | [jobs, report, directory] => pure (jobs, report, FilePath.mk directory)
    | _ => throw <| IO.userError "usage: attest-extras JOBS.jsonl REPORT.jsonl [TEMP_DIRECTORY]"
  IO.FS.createDirAll directory
  let (temporaryHandle, reservation) ← IO.FS.createTempFile
  temporaryHandle.flush
  let temporary := directory / reservation.fileName.get!
  if temporary != reservation && (← temporary.pathExists) then
    throw <| IO.userError "temporary attestation filename already exists"
  let input ← IO.FS.Handle.mk jobs .read
  let output ← IO.FS.Handle.mk report .write
  let mut count := 0
  let mut exact := 0
  let mut lintOnly := 0
  let mut mismatches := 0
  try
    repeat
      let line ← input.getLine
      if line.isEmpty then break
      if line.trimAscii.isEmpty then continue
      let .ok job := Json.parse line
        | throw <| IO.userError s!"invalid JSON at job {count + 1}"
      let result ← AttestExtras.attest job temporary
      output.putStrLn result.compress
      count := count + 1
      match (result.getObjValAs? String "mode").toOption.getD "mismatch" with
      | "exact" => exact := exact + 1
      | "lint-only" => lintOnly := lintOnly + 1
      | _ => mismatches := mismatches + 1
      if count % 1000 == 0 then
        output.flush
        IO.println s!"attested {count}: {exact} exact, {lintOnly} lint-only, {mismatches} mismatches"
    output.flush
    IO.println s!"attested {count}: {exact} exact, {lintOnly} lint-only, {mismatches} mismatches"
  finally
    if ← temporary.pathExists then IO.FS.removeFile temporary
    if temporary != reservation && (← reservation.pathExists) then IO.FS.removeFile reservation
  return if mismatches == 0 then 0 else 1
