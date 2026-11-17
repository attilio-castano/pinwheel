import Lean
import Pinwheel.Hardware.Processor.SerialRefinement

open Lean Elab Pinwheel.Hardware Pinwheel.Hardware.Processor

namespace ProcessorSerialRefinementTests

def changed (d : Uart.Timing) (ordinal value : Nat) : SerialRefinement.Physical d where
  step := (SerialCircuit.circuit d).step
  observe := fun i s {b} o =>
    if (SerialInterface.outputs.position o).val == ordinal then BitVec.ofNat b value
    else (SerialCircuit.circuit d).observe i s o

def pins (cpu : Bool) : Values SerialInterface.Input := fun {b} p =>
  BitVec.ofNat b (match (SerialInterface.inputs.position p).val with
    | 1 => cpu.toNat
    | 6 => 0xdecafbad
    | 7 => 1
    | _ => 0)

def sensitivities : IO Nat := do
  let mut count := 0
  for divisor in [4,6,10,32] do
    let some d := Uart.Timing.check divisor | throw (IO.userError "Invalid test divisor")
    for (ordinal,value) in [(1,0),(2,1),(3,0x12345678),(9,1),(10,1),(11,0x5a),(12,1)] do
      let logical : SerialModel.State :=
        if ordinal == 9 then
          ⟨{MmioModel.initial with tx := some 0x69},⟨.active 0x69 0,.idle⟩⟩
        else if ordinal == 11 then
          ⟨MmioModel.initial,⟨.idle,.receiving (d.stopSample-1) 0xa5⟩⟩
        else SerialModel.initial
      let raw : Values (SerialCircuit.Register d) := SerialCircuit.encode d logical
      let i : Values SerialInterface.Input := pins (ordinal ≤ 3)
      let expected : List MmioModel.Event :=
        if ordinal ≤ 3 then [.cpu ⟨.gpio,0,false,0⟩ 0xdecafbad (.read 0xdecafbad),.tick]
        else if ordinal == 11 then [.tick,.receive 0xa5 true]
        else [.tick]
      let original := SerialRefinement.events (SerialCircuit.circuit d).component i raw
      unless decide (original = expected) do
        throw (IO.userError s!"Incorrect serial event fixture D={divisor}/output={ordinal}")
      let altered := SerialRefinement.events (changed d ordinal value) i raw
      if decide (altered = expected) then
        throw (IO.userError s!"Actual imported output was ignored D={divisor}/output={ordinal}")
      count := count+1
  return count

theorem imported_device_replay (d : Uart.Timing) (rtl : SerialRefinement.Physical d)
    (proof : Artifact.Correspondence (SerialCircuit.circuit d) rtl)
    (i : Values SerialInterface.Input) (s : Values (SerialCircuit.Register d))
    (resetHigh : i SerialInterface.reset = 1) (traffic : List (Values SerialInterface.Input))
    (legal : rtl.Legal (fun j _ => SerialInterface.Admitted j) (rtl.step i s) traffic) :
    MmioModel.replay MmioModel.initial
      (rtl.eventTrace (SerialRefinement.events rtl) (rtl.step i s) traffic) =
      some (SerialCircuit.view (rtl.run (rtl.step i s) traffic)).mmio :=
  SerialRefinement.replay_after_reset proof i s resetHigh traffic legal

elab "#audit_serial_refinement" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Processor.SerialRefinement." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Processor.SerialRefinement" ||
        name.toString.startsWith "ProcessorSerialRefinementTests." then
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved serial artifact-event axiom {name}: {bad}"
      count := count+1
  if count < 20 then throwError "Incomplete serial artifact-event audit"
  logInfo m!"Serial artifact-event audit: {count} declarations, standard axioms only."

#audit_serial_refinement

end ProcessorSerialRefinementTests

def main : IO Unit := do
  let count ← ProcessorSerialRefinementTests.sensitivities
  IO.println s!"Serial artifact events: {count} actual response/UART output sensitivity cases with independent baseline events."
