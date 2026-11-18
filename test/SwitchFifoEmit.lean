import Pinwheel.Hardware.Switch.Backend
import Pinwheel.Hardware.Stream.CircularFifo3
import Pinwheel.Hardware.TypedModule

open Pinwheel.Hardware Pinwheel.Hardware.Switch

namespace SwitchFifoEmit

abbrev encoding : Physical.DestinationEncoding 2 := ⟨1, by decide, by decide⟩

def fifo (circular : Bool) : Stream.BackendAPI.Fifo 5 3 :=
  if circular then Stream.CircularFifo3.backend 5 else Stream.BackendAPI.shift 5 3 (by decide)

def design (circular : Bool) :
    TypedModule (Physical.In 1 1 1 4) (WithFifo.Register 1 1 4 (fifo circular).Register)
      (Physical.Out 1 1 4) :=
  let f := fifo circular
  let kind := if circular then "circular" else "shift"
  ⟨"switch_2x2_d3_w4_" ++ kind, WithFifo.circuit (w := 4) (depth := 3) encoding f 1,
    Physical.inputInterface 1 1 1 4, WithFifo.registers f 1 1 4,
    Physical.outputInterface 1 1 4⟩

def emit (circular : Bool) (dir : System.FilePath) : IO Unit := do
  let emitted ← IO.ofExcept (design circular).emit
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "switch.mlir") emitted.mlir
  IO.FS.writeFile (dir / "interface.json") (emitted.descriptor.pretty ++ "\n")

end SwitchFifoEmit

def main (args : List String) : IO Unit := do
  match args with
  | ["shift", dir] => SwitchFifoEmit.emit false dir
  | ["circular", dir] => SwitchFifoEmit.emit true dir
  | _ => throw (IO.userError "Usage: SwitchFifoEmit (shift|circular) outdir")
