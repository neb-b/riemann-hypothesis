/- Compare actual artifact bytes with independently published Lake hashes. -/
module
import Lake.Build.Trace
import Lean.Data.Json.FromToJson
open Lake Lean System

public def main (args : List String) : IO Unit := do
  let [jobs, output] := args | throw <| IO.userError "usage: hash-outputs JOBS.jsonl REPORT.jsonl"
  let input ← IO.FS.Handle.mk jobs .read
  let out ← IO.FS.Handle.mk output .write
  let mut count := 0
  let mut countMatches := 0
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let .ok job := Json.parse line | throw <| IO.userError "invalid JSON"
    let .ok name := job.getObjValAs? String "name" | throw <| IO.userError "missing name"
    let .ok file := job.getObjValAs? String "file" | throw <| IO.userError "missing file"
    let .ok expected := job.getObjValAs? String "expected" | throw <| IO.userError "missing expected hash"
    let actual := (← computeBinFileHash file).toString
    let same := actual == expected
    out.putStrLn (Json.mkObj [("name", toJson name), ("actual", toJson actual),
      ("expected", toJson expected), ("match", toJson same)]).compress
    count := count + 1
    if same then countMatches := countMatches + 1
    if count % 1000 == 0 then
      out.flush
      IO.eprintln s!"hashed {count} outputs: {countMatches} match"
  out.flush
  IO.eprintln s!"hashed {count} outputs: {countMatches} match"
