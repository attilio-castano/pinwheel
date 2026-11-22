import Lean
import Pinwheel.Hardware.Processor.Examples.ReadySPIProofs
import Pinwheel.Hardware.Processor.ReadyHostCircuit

open Lean Pinwheel.Hardware Pinwheel.Hardware.Processor

/-! Replay every post-loader clock using the same ROM as the hierarchy
exporter. The input byte comes from the emitted Ready pads. The GPIO drive
and architectural result come independently from the CPU model. -/
def main (args : List String) : IO Unit := do
  let [requestPath, edgePath, collection, expected] := args |
    throw (IO.userError "expected request table, edge stream, collection index and peer word")
  let some collect := collection.toNat? | throw (IO.userError "invalid collection index")
  let some result := expected.toNat? | throw (IO.userError "invalid peer word")
  let requests ← IO.FS.readBinFile requestPath
  let stream ← IO.FS.readBinFile edgePath
  unless stream.size > 0 && stream.size % 2 == 0 do throw (IO.userError "incomplete edge stream")
  let rom := ReadySPI.rom (requests.data.map UInt8.toBitVec) (requests.size / 44) collect
  let mut cpu := SystemModel.initial (aw := 2) (fun _ => 0) 0
  for k in [:stream.size / 2] do
    let gpio := stream[2*k]!.toNat
    unless cpu.mmio.gpioOut.toNat == gpio do throw (IO.userError s!"GPIO diverged at edge {k}")
    let input : SystemModel.Input := {gpio := BitVec.ofNat 32 stream[2*k+1]!.toNat}
    cpu := SystemModel.step ReadySPI.layout rom input cpu
  let captured := RV32I.Semantics.read cpu.core.arch.registers 25
  unless captured.toNat == result do throw (IO.userError s!"unexpected x25 {captured}")
  match cpu.core.phase with
  | .terminal fault =>
    unless fault.pc == 152 && fault.word == some 0x00100073 do
      throw (IO.userError "unexpected terminal instruction")
  | _ => throw (IO.userError "firmware did not terminate")
  IO.println s!"Model checked {stream.size/2} GPIO edges and x25={captured}."

open Lean.Elab.Command in
elab "#audit_ready_firmware" : command => do
  for name in [``ReadyHost.read_reply, ``ReadyHost.write_drives_next, ``ReadyHost.held_clock,
      ``ReadyHost.store_substitution, ``ReadyHost.gpio_output, ``ReadyHost.feedback_refines,
      ``ReadySPI.receiveNibble_value, ``ReadySPI.collect_value, ``ReadySPI.receive_word] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
    unless bad.isEmpty do throwError "Unexpected axioms for {name}: {bad}"

#audit_ready_firmware
