import Pinwheel.Hardware.Processor.LoadableSystem
import Pinwheel.Hardware.Processor.SystemExportProofs

/-! Finite cached evaluation of the loader-owned system. All component steps
use the same pre-edge state. The loader's external reset remains distinct from
the effective reset that holds the processor, fetch path and devices quiescent. -/
namespace Pinwheel.Hardware.Processor.LoadableSystem

def systemPins (i : Values (Input aw)) : Values SystemInterface.Input
  | _, .at ⟨0,_⟩ => i reset ||| i mode
  | _, .at k => i (.left (.at k))

def loaderPins (i : Values (Input aw)) (ramPins : Values (Memory.ByteAdapterInterface.Input aw)) :
    Values (Memory.ByteAdapterLoader.Input aw)
  | _, .left (.at ⟨0,_⟩) => i reset
  | _, .left (.at ⟨k+1,h⟩) => ramPins (.at ⟨k+1,h⟩)
  | _, .right p => i (.right p)

variable (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

def nextSnapshot (i : Values (Input aw)) (s : Values (Register aw)) : SystemExport.Snapshot (Register aw) :=
  let stage := SystemExport.stages layout rom romFits ramFits (systemPins i) s
  let li := SystemExport.snapshot (Memory.ByteAdapterLoader.inputs aw) (loaderPins i stage.ramInput.values)
  SystemExport.snapshot (registers aw) (fun r => match r with
    | .left r => CoreCircuit.circuit.step stage.coreInput.values (fun p => s (SystemCircuit.core p)) r
    | .right (.left r) => (Memory.ByteAdapterLoader.circuit aw).step li.values (fun p => s (SystemCircuit.ram p)) r
    | .right (.right (.left r)) => MmioCircuit.circuit.step stage.mmioInput.values (fun p => s (SystemCircuit.mmio p)) r
    | .right (.right (.right r)) => stage.fetchNext.values r)

def outputSnapshot (i : Values (Input aw)) (s : Values (Register aw)) : SystemExport.Snapshot Output :=
  let normal := SystemExport.outputSnapshot layout rom romFits ramFits (systemPins i) s
  SystemExport.snapshot outputs (fun {b} o => match b,o with
    | _, .left o => normal.values o
    | _, .right (.at ⟨0,_⟩) => i mode &&& ~~~i reset
    | _, .right (.at ⟨1,_⟩) => ~~~i mode &&& ~~~i reset
    | _, .right (.at ⟨k+2,h⟩) => False.elim (by change k+2 < 2 at h; omega))

def staged : Timed.Component (Values (Input aw)) (Values (Register aw)) (Values Output) where
  step i s := (nextSnapshot layout rom romFits ramFits i s).values
  observe i s := (outputSnapshot layout rom romFits ramFits i s).values

end Pinwheel.Hardware.Processor.LoadableSystem
