import Pinwheel.Hardware.Stream.Diamond
import Pinwheel.Hardware.Stream.Replay

open Pinwheel.Hardware Pinwheel.Hardware.Stream Pinwheel.Hardware.Stream.Replay

def main (args : List String) : IO Unit := do
  let [w, l, r, path, stimulus] := args
    | throw (IO.userError "Usage: stream_graph WIDTH LEFT_STAGES RIGHT_STAGES DIRECTORY stimulus.csv")
  let width ← number w
  let left ← number l
  let right ← number r
  unless width > 0 && left > 0 && right > 0 do throw (IO.userError "Width and both stage counts must be positive")
  let d := diamondDesign width (left - 1) (right - 1)
  let dir : System.FilePath := path
  exportDesign d dir
  IO.FS.writeFile (dir / "payload.json") (interfaceJson (diamondPayloadInterface width)).pretty
  let edges ← simulate d.flatten stimulus (dir / "lean.csv")
  IO.println s!"Fork/join {width}/{left}/{right}: {edges} edges, all registers and transactions agree."
