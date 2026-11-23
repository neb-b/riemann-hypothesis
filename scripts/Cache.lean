import Init.System.IO

/-- Fetch Mathlib and the project's published artifacts using stock tools. -/
def main (args : List String) : IO UInt32 := do
  let child ← IO.Process.spawn {
    cmd := "bash"
    args := #["scripts/lake-cache-get.sh"] ++ args.toArray
  }
  child.wait
