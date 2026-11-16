import Pinwheel.Hardware.Stream.Replay
import Pinwheel.Hardware.Stream.Timing

open Pinwheel.Hardware Pinwheel.Hardware.Stream Pinwheel.Hardware.Stream.Replay

def main (args : List String) : IO Unit := do
  let w :: d :: l :: path :: remaining := args
    | throw (IO.userError "Usage: stream_example WIDTH DEPTH STAGES DIRECTORY [stimulus.csv]")
  let width ← number w
  let depth ← number d
  let stages ← number l
  unless width > 0 && stages > 0 do throw (IO.userError "Width and stages must be positive")
  if hd : depth > 0 then
    let design := adderDesign width depth (stages - 1) hd
    let directory : System.FilePath := path
    exportDesign design directory
    match remaining with
    | [] => pure ()
    | [stimulus] =>
      let count ← simulate design.flatten stimulus (directory / "lean.csv")
      IO.println s!"Stream {width}/{depth}/{stages}: {count} edges, structural state and transaction model agree."
    | _ => throw (IO.userError "Unexpected arguments")
  else throw (IO.userError "FIFO depth must be positive")
