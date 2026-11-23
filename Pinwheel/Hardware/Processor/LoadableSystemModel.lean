import Pinwheel.Hardware.Processor.LoadableSystemStaged
import Pinwheel.Hardware.Processor.SystemCircuitInputs

/-! Logical loader ownership above the connected processor model. Effective
reset cancels CPU/provider work before an admitted full-word write updates RAM.
The same state also models ordinary execution after loader ownership ends. -/
namespace Pinwheel.Hardware.Processor.LoadableSystem

def patchMemory (s : SystemModel.State aw) (address : BitVec aw) (data : BitVec 32) : SystemModel.State aw :=
  {s with
    ram := {s.ram with
      memory := {s.ram.memory with
        contents := fun k => if address = k then data else s.ram.memory.contents k}}}

def spec (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32) :
    Timed.Component (Values (Input aw)) (SystemModel.State aw) (Values Output) where
  step i s :=
    let base := (SystemCircuit.spec layout rom).step (systemPins i) s
    if Accepted i then patchMemory base (i address) (i data) else base
  observe := fun i s {b} o => match b,o with
    | _, .left o => (SystemCircuit.spec layout rom).observe (systemPins i) s o
    | _, .right (.at ⟨0,_⟩) => i mode &&& ~~~i reset
    | _, .right (.at ⟨1,_⟩) => ~~~i mode &&& ~~~i reset
    | _, .right (.at ⟨k+2,h⟩) => False.elim (by change k+2 < 2 at h; omega)

end Pinwheel.Hardware.Processor.LoadableSystem
