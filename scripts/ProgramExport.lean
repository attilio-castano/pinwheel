import Pinwheel.Program.Requests

/-! Static production entrypoint: one JSON request on stdin, one response on
stdout, and errors on stderr with a nonzero exit code. -/
def main (args : List String) : IO UInt32 := do
  if !args.isEmpty then
    IO.eprintln "Program export reads one JSON request from standard input"
    return 1
  let input ← (← IO.getStdin).readToEnd
  match Pinwheel.Program.Export.compileText input with
  | .ok response => IO.println response; return 0
  | .error message => IO.eprintln s!"Program export rejected request: {message}"; return 1
