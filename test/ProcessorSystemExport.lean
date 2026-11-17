import Lean
import Pinwheel.Hardware.Processor.SystemExportProofs
import Pinwheel.Hardware.Processor.Examples.ByteProgram

open Lean Elab Pinwheel.Hardware Pinwheel.Hardware.Processor ProcessorSystemFirmware

namespace ProcessorSystemExportTests

def dirty (seed : Nat) : Values (SystemCircuit.Register 2) := fun r =>
  BitVec.ofNat _ (0x91827364 + 0x10001 * ((SystemCircuit.registers 2).position r).val + seed)

def pins (flags : Nat) : Values SystemInterface.Input
  | _, .at ⟨0,_⟩ => BitVec.ofNat _ (flags%2)
  | _, .at ⟨1,_⟩ => 0xdecafbad
  | _, .at ⟨2,_⟩ => BitVec.ofNat _ (flags/2%2)
  | _, .at ⟨3,_⟩ => BitVec.ofNat _ (flags/4%2)
  | _, .at ⟨4,_⟩ => 0xa5
  | _, .at ⟨5,_⟩ => BitVec.ofNat _ (flags/8%2)
  | _, .at ⟨k+6,h⟩ => False.elim (by change k+6 < 6 at h; omega)

def feedback : IO Nat := do
  let mut cases := 0
  for seed in [0:8] do
    for flags in [0:16] do
      let state := SystemExport.snapshot (SystemCircuit.registers 2) (dirty seed)
      let input := SystemExport.snapshot SystemInterface.inputs (pins flags)
      let stage := SystemExport.stages layout rom (by decide) (by decide) input.values state.values
      let observed := SystemExport.outputSnapshot layout rom (by decide) (by decide) input.values state.values
      let ram := SystemExport.snapshot Memory.ByteAdapterInterface.outputs
        ((Memory.ByteAdapterCircuit.circuit 2).observe stage.ramInput.values
          (fun r => state.values (SystemCircuit.ram r)))
      let connected := SystemExport.snapshot SystemExport.busInputs (SystemExport.busValues input.values
        (fun p => observed.values (.left p)) ram.values (fun p => observed.values (.right p)))
      let bus := SystemExport.busCircuit layout rom (by decide) (by decide)
      let fs : Values SystemInterface.Fetch := fun r => state.values (SystemCircuit.fetch r)
      for ⟨_,p⟩ in (SystemExport.busOutputs 2).ports do
        let expected := match p with
          | .left p => stage.coreInput.values p
          | .right (.left p) => stage.ramInput.values p
          | .right (.right p) => stage.mmioInput.values p
        unless bus.observe connected.values fs p == expected do
          throw (IO.userError "Actual core response feedback changed a bus input")
      for ⟨_,p⟩ in SystemInterface.fetchPorts.interface.ports do
        unless bus.step connected.values fs p == stage.fetchNext.values p do
          throw (IO.userError "Actual core response feedback changed fetch state")
      for ⟨_,r⟩ in (SystemCircuit.registers 2).ports do
        unless state.values r == dirty seed r do throw (IO.userError "Snapshot lost a typed register")
      cases := cases+1
  return cases

elab "#audit_system_export" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Processor.SystemExport." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Processor.SystemExport" ||
        name == ``CoreCircuit.request_outputs then
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved system-export axioms in {name}: {bad}"
      count := count+1
  if count < 80 then throwError "Incomplete system-export audit"
  logInfo m!"System export audit: {count} declarations, standard axioms only."

#audit_system_export

def checkLeafNames (ii : Interface I) (ri : Interface R) (oi : Interface O) : IO Unit := do
  let names := #["clk"] ++ (ii.ports.map fun ⟨_,p⟩ => ii.label p) ++
    ((SystemExport.tapInterface oi ri).ports.map fun ⟨_,p⟩ => (SystemExport.tapInterface oi ri).label p)
  unless names.toList.eraseDups.length == names.size do
    throw (IO.userError "Leaf inputs, outputs or clock have duplicate physical labels")

def main : IO Unit := do
  checkLeafNames CoreInterface.inputs CoreCircuit.registers CoreInterface.outputs
  checkLeafNames (Memory.ByteAdapterInterface.inputs 2) (Memory.ByteAdapterCircuit.registers 2) Memory.ByteAdapterInterface.outputs
  checkLeafNames MmioInterface.inputs MmioCircuit.registers MmioInterface.outputs
  checkLeafNames SystemExport.busInputs SystemInterface.fetchPorts.interface (SystemExport.busOutputs 2)
  let cases ← feedback
  unless (SystemCircuit.registers 2).size == 60 && SystemCircuit.outputs.size == 37 &&
      SystemInterface.inputs.size == 6 && SystemExport.busInputs.size == 47 &&
      (SystemExport.busOutputs 2).size == 32 do throw (IO.userError "Incomplete hierarchy interface")
  IO.println s!"System export: {cases} arbitrary-state actual-feedback cases, all 32 bus inputs and 3 fetch updates; 60-register snapshots preserved."

end ProcessorSystemExportTests

def main := ProcessorSystemExportTests.main
