import Pinwheel.Hardware.Library

/-! A library client: independently buffered increment pipelines. Each lane
has its own reset and backpressure. Change lane count, width, FIFO depth or
pipeline depth without changing the component proofs or library internals.
-/

open Pinwheel.Hardware

namespace IndependentLanes

def lane (width depth extraStages : Nat) (hd : 0 < depth) : Stream.Certified width width :=
  (Stream.Design.buffered (Stream.increment width) depth hd extraStages).flatten

def circuit (count width depth extraStages : Nat) (hd : 0 < depth) :=
  Bank.circuit count (lane width depth extraStages hd).normalized.circuit

def certificate (count width depth extraStages : Nat) (hd : 0 < depth) :=
  (lane width depth extraStages hd).implementation.bank count

theorem trace_correct (count width depth extraStages : Nat) (hd : 0 < depth)
    (traffic : List (Values (Bank count (Stream.In width)))) :
    let c := lane width depth extraStages hd
    (circuit count width depth extraStages hd).component.trace
      (Bank.values (fun _ => c.encode c.initial)) traffic =
    (Bank.model count c.physicalModel).trace (fun _ => c.initial) traffic :=
  (certificate count width depth extraStages hd).trace_eq _ (fun _ =>
    (lane width depth extraStages hd).initial_valid) traffic

def emit (path : System.FilePath) : IO Unit := do
  let c := lane 17 3 1 (by decide)
  let inputs := Bank.interface 3 (Stream.inputPorts 17).interface
  let registers := Bank.interface 3 c.registers
  let outputs := Bank.interface 3 (Stream.outputPorts 17).interface
  -- Independent interface roles must have distinct external names.
  let nameInput := fun {w} (p : Bank 3 (Stream.In 17) w) => "input_" ++ toString (inputs.position p).val
  let nameOutput := fun {w} (p : Bank 3 (Stream.Out 17) w) => "output_" ++ toString (outputs.position p).val
  let rtl ← IO.ofExcept (Emit.moduleText "independent_lanes" (circuit 3 17 3 1 (by decide))
    inputs.ports registers.ports outputs.ports nameInput registers.label nameOutput)
  IO.FS.writeFile path rtl

end IndependentLanes

def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "Usage: IndependentLanes.lean OUTPUT.mlir")
  IndependentLanes.emit output
  IO.println "Emitted three independently buffered 17-bit increment pipelines."
