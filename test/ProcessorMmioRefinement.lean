import Lean
import Pinwheel.Hardware.Processor.MmioRefinement

open Lean Elab Command Pinwheel.Hardware Pinwheel.Hardware.Processor
open MmioInterface MmioCircuit

namespace ProcessorMmioRefinementTests

theorem identityCertificate : Artifact.Correspondence circuit circuit.component := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

example (s : Values Register) (traffic : List (Values Input))
    (legal : circuit.component.Legal (fun i _ => Admitted i) s traffic) :
    MmioModel.replay (view s) (circuit.component.eventTrace (MmioRefinement.events circuit.component) s traffic) =
      some (view (circuit.component.run s traffic)) :=
  MmioRefinement.replay_trace identityCertificate s traffic legal

def timerInput : Values Input := fun {b} p => BitVec.ofNat b
  (if (inputs.position p).val = 1 ∨ (inputs.position p).val = 2 then 1 else 0)
def timerState : Values Register := fun {b} p => BitVec.ofNat b (if (registers.position p).val = 1 then 42 else 0)

/-- The source-side theorem is not an artifact certificate. Changing the actual
response data changes extraction and fails checked event replay. -/
def corrupted : Circuit Input Register Output where
  next := circuit.next
  output := fun o => match o with
    | .at ⟨3, _⟩ => .lit 0
    | .at k => circuit.output (.at k)

example : Admitted timerInput := by unfold Admitted; decide +kernel
example : MmioRefinement.observedResponse circuit.component timerInput timerState = some (.read 42) := by decide +kernel
example : MmioRefinement.observedResponse corrupted.component timerInput timerState = some (.read 0) := by decide +kernel
example : MmioModel.replay (view timerState) (MmioRefinement.events corrupted.component timerInput timerState) = none := by decide +kernel
example : MmioRefinement.events corrupted.component timerInput timerState ≠
    MmioRefinement.events circuit.component timerInput timerState := by decide +kernel

theorem corruption_has_no_certificate : ¬Artifact.Correspondence circuit corrupted.component := by
  intro proof
  have equality := MmioRefinement.observedResponse_eq proof timerInput timerState
  contradiction

end ProcessorMmioRefinementTests

elab "#audit_mmio_transport" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if ["Pinwheel.Hardware.Processor.MmioRefinement.", "_private.Pinwheel.Hardware.Processor.MmioRefinement.",
        "ProcessorMmioRefinementTests."].any (fun pfx => name.toString.startsWith pfx) then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved MMIO transport axioms in {name}: {bad}"
  if count < 20 then throwError "Incomplete MMIO artifact transport audit"
  logInfo m!"MMIO artifact transport: {count} declarations, standard axioms only."

#audit_mmio_transport
