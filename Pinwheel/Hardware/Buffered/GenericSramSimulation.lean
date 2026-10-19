import Pinwheel.Hardware.Buffered.GenericSimulation
import Pinwheel.Hardware.Buffered.GenericSramRelation

/-! Generic source simulation at the actual typed digital SRAM boundary.
Each quiet clock preserves both physical replicas and registered read readiness. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

theorem RelatedSram.step {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : SramState.State} {source : Program.Buffered.State}
    (h : RelatedSram p layout payload actual source) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) :
    RelatedSram p layout payload (actual.step i)
      (Program.Buffered.advance p capacity source (i .rawInputs)) := by
  rcases h with ⟨rows, dictionary, resident, ready, related⟩
  have executing : SramExecution.ExecutingInput i := by
    simp [SramExecution.ExecutingInput, SharedBranches.Runtime, quiet.1, quiet.2]
  refine ⟨rows, dictionary,
    SramExecution.resident_executing actual i rows dictionary executing resident,
    SramExecution.ready_executing actual i rows dictionary executing resident, ?_⟩
  rw [SramExecution.reference_step_eq actual i rows dictionary executing resident ready]
  exact related_step related i quiet

theorem RelatedSram.run {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : SramState.State} {source : Program.Buffered.State}
    (h : RelatedSram p layout payload actual source) (incoming : Nat → BitVec 2) (edges : Nat) :
    RelatedSram p layout payload (actual.run (SpiStart.clocks incoming edges))
      (Program.Buffered.run p capacity source incoming edges) := by
  rcases h with ⟨rows, dictionary, resident, ready, related⟩
  have runtime := SpiStart.clocks_executing incoming edges
  have invariants := SramExecution.runtime_invariants actual (SpiStart.clocks incoming edges)
    rows dictionary resident ready runtime
  have execution := SramExecution.runtime_run actual (SpiStart.clocks incoming edges)
    rows dictionary resident ready runtime
  refine ⟨rows, dictionary, invariants.1, invariants.2, ?_⟩
  rw [execution]
  exact related_run related incoming edges

theorem RelatedSram.run_inputs {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : SramState.State} {source : Program.Buffered.State}
    (h : RelatedSram p layout payload actual source) (inputs : List (Values Reactive.Input))
    (quiet : ∀ i ∈ inputs, SpiCircuit.Quiet i) :
    RelatedSram p layout payload (actual.run inputs)
      (inputs.foldl (fun state input => Program.Buffered.advance p capacity state (input .rawInputs)) source) := by
  induction inputs generalizing actual source
  case nil => exact h
  case cons i inputs ih =>
    have head : SpiCircuit.Quiet i := quiet @i (by simp)
    have tail : ∀ j ∈ inputs, SpiCircuit.Quiet j :=
      fun j hj => quiet @j (@List.mem_cons_of_mem (Values Reactive.Input) @i @j inputs hj)
    exact ih (h.step i head) tail

end Pinwheel.Hardware.Buffered.Refinement
