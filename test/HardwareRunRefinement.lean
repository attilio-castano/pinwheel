import Lean
import Pinwheel.Hardware.RunRefinement
import Pinwheel.Hardware.Memory.TransferHostCircuitProofs

open Lean Elab Command
open Pinwheel.Hardware Pinwheel.Hardware.Memory

namespace HardwareRunRefinementTests

/-- A downstream artifact use: combine arbitrary-state, memory-preserving
reset with final encoded state transport. The artifact correspondence remains
an explicit premise; this test does not invent a certificate for external RTL. -/
theorem host_reset_run (m : Stream.Map wi wo)
    {rtl : Timed.Component (Values (TransferHostInterface.Input a wi wo))
      (Values (TransferHostCircuit.Register a wi wo)) (Values (TransferHostInterface.Output wi wo))}
    (artifact : Artifact.Correspondence (TransferHostCircuit.circuit m) rtl)
    (i : Values (TransferHostInterface.Input a wi wo)) (raw : Values (TransferHostCircuit.Register a wi wo))
    (hr : i TransferHostInterface.reset = 1) (inputs : List (Values (TransferHostInterface.Input a wi wo))) :
    @Eq (Values (TransferHostCircuit.Register a wi wo)) (rtl.run (rtl.step i raw) inputs)
      (TransferHostCircuit.encode ((TransferHostInterface.spec m).run (TransferHostCircuit.resetState raw) inputs)) := by
  have recovered := funext fun b => funext fun r => TransferHostCircuit.reset_eq m i raw hr (b := b) r
  rw [artifact.step_eq, recovered]
  apply artifact.encoded_run (TransferHostCircuit.implementation m)
  simp [TransferHostCircuit.implementation, TransferHostCircuit.resetState,
    TransferModel.initialState, TransferModel.initialControl, TransferModel.Control.Valid, TransferModel.emptyConfig]

/-- Entire source and destination memory states, including Q, follow from the
represented-state equation even when the current host outputs expose neither
memory. This uses no inverse or injectivity assumption on a general encoding. -/
theorem host_final_memories (m : Stream.Map wi wo)
    {rtl : Timed.Component (Values (TransferHostInterface.Input a wi wo))
      (Values (TransferHostCircuit.Register a wi wo)) (Values (TransferHostInterface.Output wi wo))}
    (artifact : Artifact.Correspondence (TransferHostCircuit.circuit m) rtl)
    (i : Values (TransferHostInterface.Input a wi wo)) (raw : Values (TransferHostCircuit.Register a wi wo))
    (hr : i TransferHostInterface.reset = 1) (inputs : List (Values (TransferHostInterface.Input a wi wo))) :
    let actual : Values (TransferHostCircuit.Register a wi wo) := rtl.run (rtl.step i raw) inputs
    let expected := (TransferHostInterface.spec m).run (TransferHostCircuit.resetState raw) inputs
    (StreamFlops.view (TransferHostCircuit.sourceValues actual)).memory = expected.source.memory ∧
      (StreamFlops.view (TransferHostCircuit.destinationValues actual)).memory = expected.destination.memory := by
  dsimp only
  rw [host_reset_run m artifact i raw hr inputs]
  simp

def identityMap : Stream.Map 8 8 := ⟨.input .data, id, fun _ => rfl⟩

def pins (row : Array Nat) : Values (TransferHostInterface.Input 1 8 8) :=
  fun {w} p => BitVec.ofNat w row[((TransferHostInterface.inputs 1 8 8).position p).val]!

def resetInput : Values (TransferHostInterface.Input 1 8 8) :=
  pins #[1, 1, 1, 1, 3, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1]

def writeInput : Values (TransferHostInterface.Input 1 8 8) :=
  pins #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 165, 1]

def quietInput : Values (TransferHostInterface.Input 1 8 8) :=
  pins #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]

def dirty : Values (TransferHostCircuit.Register 1 8 8) :=
  fun {w} _ => BitVec.ofNat w (2^w-1)

/-- Reset ignores offered writes, the later accepted host write persists after
an idle edge, the other memory is untouched, and neither Q register is cleared.
These words are not visible as host responses in this final idle state. -/
theorem imported_host_write
    {rtl : Timed.Component (Values (TransferHostInterface.Input 1 8 8))
      (Values (TransferHostCircuit.Register 1 8 8)) (Values (TransferHostInterface.Output 8 8))}
    (artifact : Artifact.Correspondence (TransferHostCircuit.circuit (a := 1) identityMap) rtl) :
    let result : Values (TransferHostCircuit.Register 1 8 8) := rtl.run (rtl.step resetInput dirty) [writeInput, quietInput]
    result (.right (.right (.left (CommandFlops.word 1)))) = 165 ∧
      result (.right (.right (.left (CommandFlops.word 0)))) = 255 ∧
      result (.right (.left (.left (CommandFlops.word 1)))) = 255 ∧
      result (.right (.left (.left CommandFlops.q))) = 255 ∧
      result (.right (.right (.left CommandFlops.q))) = 255 := by
  dsimp only
  have h := host_reset_run identityMap artifact resetInput dirty (by decide +kernel) [writeInput, quietInput]
  rw [congrFun h 8]
  decide +kernel

/-- The host response offer is empty despite the retained written word. This
distinguishes final represented state from a current output sample. -/
example :
    let result := (TransferHostInterface.spec identityMap).run
      (TransferHostCircuit.resetState dirty) [writeInput, quietInput]
    (TransferHostModel.observe (TransferHostInterface.decode quietInput) result).destination.offered = none ∧
      result.destination.memory.contents 1 = 165 := by
  decide +kernel

end HardwareRunRefinementTests

elab "#audit_run_refinement" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let selected := name == ``Timed.Refinement.run_related || name == ``Implementation.run_eq ||
      name == ``Artifact.Correspondence.run_eq || name == ``Artifact.Correspondence.encoded_run ||
      name.toString.startsWith "HardwareRunRefinementTests." ||
      name.toString.startsWith "_private.test.HardwareRunRefinement."
    if selected then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count < 4 then throwError "Incomplete final-state refinement audit"
  logInfo m!"Run refinement audit: {count} declarations, standard axioms only."

#audit_run_refinement

def main : IO Unit :=
  IO.println "Final-state refinement: arbitrary host reset/final-memory transport and concrete retained write/Q examples kernel-checked; artifact correspondence remains an explicit premise."
