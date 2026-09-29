import Pinwheel.Hardware.Storage.PairedClosed

open Pinwheel.Hardware Pinwheel.Hardware.Storage

private def arbitrary : Memory.Sram.State 9 64 := ⟨fun _ => 99, 165⟩
private def written := Memory.SinglePort.step arbitrary (.write 3 42)

-- These controls forbid three tempting but invalid memory assumptions.
example : written.q = 165 := by decide +kernel
example : written.q ≠ 42 := by decide +kernel
example : (Memory.SinglePort.step written (.read 3)).q = 42 := by decide +kernel
example : (Memory.SinglePort.step written .idle).q = 165 := by decide +kernel
example : arbitrary.contents 0 ≠ 0 := by decide +kernel
example : (Memory.SinglePort.modelStep (Memory.Sram.Model.initial (a := 9) (w := 64))
    (.read 3)).q 0 = none := by decide +kernel
example : PairedClosed.enables (Memory.SinglePort.Command.write (3 : BitVec 9) (42 : BitVec 64)) ≠
    (1, 1) := by decide +kernel
example : PairedSemantics.ordered [] PairedController.bindings.reverse = false := by decide +kernel
example : PairedSemantics.ordered []
    (PairedController.bindings ++ PairedController.bindings.take 1) = false := by decide +kernel

/-- This executable witness prevents the conditional core theorems from being
used with a failing constructor, and binds the proved package to the current
emitter. Historical artifact identity is checked separately by the runner. -/
def main (args : List String) : IO Unit := do
  unless args.length == 1 do throw (IO.userError "Expected a fresh output directory")
  let .ok _ := PairedController.core | throw (IO.userError "Original paired graph failed construction")
  let .ok n := PairedValidation.core | throw (IO.userError "Retained paired graph failed construction")
  let proved := Netlist.moduleText "pinwheel_paired_controller" (PairedComposition.package n)
    (PairedController.inputs Backend.Policy.chipInputs) PairedController.fullRegisters
    (PairedController.outputs Backend.Policy.chipOutputs)
    (SramAssembly.inputLabel Backend.Policy.chipInputLabel) PairedController.fullLabel
    (SramAssembly.outputLabel Backend.Policy.chipOutputLabel)
  let .ok proved := proved | throw (IO.userError "Proved package failed emission")
  let .ok emitted := PairedValidation.chipText | throw (IO.userError "Retained package failed emission")
  unless proved == emitted do throw (IO.userError "Proved package differs from emitter input")
  IO.FS.writeFile (args.head! ++ "/proved-chip.mlir") proved
  IO.println s!"Paired formal witness: both constructors pass; {PairedController.bindings.length} nodes; proved package matches emitted package."
