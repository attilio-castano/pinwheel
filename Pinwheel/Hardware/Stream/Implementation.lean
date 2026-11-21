import Pinwheel.Hardware.Stream.Normalize
import Pinwheel.Hardware.Artifact

namespace Pinwheel.Hardware.Stream

/-- The stream model with its complete physical input/output interface. Idle
payload bits are ignored by decoding and the normalized circuit alike. -/
def Certified.physicalModel (c : Certified wi wo) :
    Timed.Component (Values (In wi)) c.State (Values (Out wo)) :=
  ⟨fun i s => c.machine.step (decodeInput i) s,
   fun i s => outputValues (c.machine.component.observe (decodeInput i) s)⟩

/-- Single-channel stream components and multiport hardware share the same
implementation certificate. Their protocol contracts remain distinct. -/
def Certified.implementation (c : Certified wi wo) :
    Implementation c.normalized.circuit c.physicalModel where
  Valid := c.contract.Valid
  encode := c.encode
  preserved := fun i s h => c.contract.preserved (decodeInput i) s h
  step_eq := by
    intro i s h w r
    exact (normalize_step c.circuit i (c.encode s) r).trans (c.step_eq (decodeInput i) s h r)
  output_eq := by
    intro i s h w o
    exact (normalize_observe c.circuit i (c.encode s) o).trans (c.output_eq (decodeInput i) s h o)

def Certified.resetCertificate (c : Certified wi wo) : c.implementation.Reset reset where
  initial := c.initial
  initial_valid := c.initial_valid
  reset_eq := c.normalized.reset_eq

end Pinwheel.Hardware.Stream
