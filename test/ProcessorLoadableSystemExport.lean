import Lean
import Pinwheel.Hardware.Processor.LoadableSystemExportProofs
import Pinwheel.Hardware.Processor.LoadableSystemProofs
import Pinwheel.Hardware.Processor.Examples.ByteProgram

open Lean Elab Pinwheel.Hardware Pinwheel.Hardware.Processor ProcessorSystemFirmware

namespace ProcessorLoadableSystemExportTests

def dirty (seed : Nat) : Values (LoadableSystem.Register 2) := fun r =>
  BitVec.ofNat _ (0x91827364 + 0x10001 * ((LoadableSystem.registers 2).position r).val + seed)

def pins (flags : Nat) : Values (LoadableSystem.Input 2) := fun p =>
  BitVec.ofNat _ (#[flags%2,0xdecafbad,flags/8%2,flags/16%2,0xa5,flags/32%2,
    flags/2%2,flags/4%2,flags/16%4,0xaabbccdd+flags][(LoadableSystem.inputs 2).position p]'(by
      exact ((LoadableSystem.inputs 2).position p).isLt))

def feedback : IO Nat := do
  let mut cases := 0
  for seed in [0:4] do
    for flags in [0:64] do
      let state := SystemExport.snapshot (LoadableSystem.registers 2) (dirty seed)
      let input := SystemExport.snapshot (LoadableSystem.inputs 2) (pins flags)
      let stage := SystemExport.stages layout rom (by decide) (by decide) (LoadableSystem.systemPins input.values) state.values
      let observed := LoadableSystem.outputSnapshot layout rom (by decide) (by decide) input.values state.values
      let li := SystemExport.snapshot (Memory.ByteAdapterLoader.inputs 2) (LoadableSystem.loaderPins input.values stage.ramInput.values)
      let ram := SystemExport.snapshot Memory.ByteAdapterLoader.outputs
        ((Memory.ByteAdapterLoader.circuit 2).observe li.values (fun r => state.values (SystemCircuit.ram r)))
      let connected := SystemExport.snapshot (LoadableSystemExport.busInputs 2) (Stream.Joint.values input.values
        (Stream.Joint.values (fun p => observed.values (.left (.left p)))
          (Stream.Joint.values ram.values (fun p => observed.values (.left (.right p))))))
      let bus := LoadableSystemExport.busCircuit layout rom (by decide) (by decide)
      let fs : Values SystemInterface.Fetch := fun r => state.values (SystemCircuit.fetch r)
      for ⟨_,p⟩ in (LoadableSystemExport.busOutputs 2).ports do
        let expected := match p with
          | .left p => stage.coreInput.values p
          | .right (.left p) => li.values p
          | .right (.right (.left p)) => stage.mmioInput.values p
          | .right (.right (.right p)) => observed.values (.right p)
        unless bus.observe connected.values fs p == expected do
          throw (IO.userError "Loader hierarchy changed a canonical component input/status")
      for ⟨_,p⟩ in SystemInterface.fetchPorts.interface.ports do
        unless bus.step connected.values fs p == stage.fetchNext.values p do
          throw (IO.userError "Loader hierarchy changed fetch state")
      for ⟨_,r⟩ in (LoadableSystem.registers 2).ports do
        unless state.values r == dirty seed r do throw (IO.userError "Snapshot lost a typed register")
      cases := cases+1
  return cases

elab "#audit_loadable_system_export" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Processor.LoadableSystemExport." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Processor.LoadableSystemExport" ||
        name.toString.startsWith "Pinwheel.Hardware.Processor.LoadableSystem." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Processor.LoadableSystemStaged" then
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved loadable-export axioms in {name}: {bad}"
      count := count+1
  if count < 30 then throwError "Incomplete loadable-export audit"
  logInfo m!"Loadable system export audit: {count} declarations, standard axioms only."

#audit_loadable_system_export

def uniqueNames (i : Interface I) (o : Interface O) : IO Unit := do
  let names := #["clk"] ++ (i.ports.map fun ⟨_,p⟩ => i.label p) ++ (o.ports.map fun ⟨_,p⟩ => o.label p)
  unless names.toList.eraseDups.length == names.size do
    throw (IO.userError "Duplicate physical input/output/clock label")

def main : IO Unit := do
  uniqueNames (LoadableSystemExport.inputs 2) LoadableSystem.outputs
  uniqueNames CoreInterface.inputs (SystemExport.tapInterface CoreInterface.outputs CoreCircuit.registers)
  uniqueNames (Memory.ByteAdapterLoader.inputs 2)
    (SystemExport.tapInterface Memory.ByteAdapterLoader.outputs (Memory.ByteAdapterLoader.registers 2))
  uniqueNames MmioInterface.inputs (SystemExport.tapInterface MmioInterface.outputs MmioCircuit.registers)
  uniqueNames (LoadableSystemExport.busInputs 2)
    (SystemExport.tapInterface (LoadableSystemExport.busOutputs 2) SystemInterface.fetchPorts.interface)
  unless (LoadableSystem.registers 2).size == 60 && LoadableSystem.outputs.size == 39 &&
      (LoadableSystemExport.inputs 2).size == 10 && (LoadableSystemExport.busInputs 2).size == 52 &&
      (LoadableSystemExport.busOutputs 2).size == 38 do throw (IO.userError "Incomplete loader hierarchy interface")
  let cases ← feedback
  IO.println s!"Loadable export: {cases} arbitrary-state actual-feedback cases; all 38 bus outputs and 3 fetch updates, complete 60-register map."

end ProcessorLoadableSystemExportTests

def main := ProcessorLoadableSystemExportTests.main
