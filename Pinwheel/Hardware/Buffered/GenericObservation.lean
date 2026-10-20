import Pinwheel.Hardware.Buffered.GenericSramRelation

/-! Public phase, busy and ownership observations follow from the execution
relation. They distinguish retained engine testimony from protocol success. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

def controlPhase : Engine.Reactive.Control 1023 → BitVec 3
  | .active .. => 1
  | .waiting .. => 2
  | .checked .. => 3
  | .qualifying .. => 4
  | .stopped .ready => 0
  | .stopped .completed => 5
  | .stopped .timeout => 6
  | .stopped .fault => 7

theorem Running.phase {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) :
    r .phase = controlPhase s.core.control := by
  have state := h.control
  cases control : s.core.control
  all_goals rw [control] at state
  case stopped => contradiction
  all_goals simpa only [control, controlPhase] using state.2.1

theorem Stopped.phase_control {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {outcome : Transfer.Outcome}
    (h : Stopped p layout payload r s e outcome) :
    r .phase = controlPhase s.core.control := by
  rw [h.control]
  cases outcome <;> simpa only [controlPhase, stopReason, stopPhase] using h.phase

theorem Related.phase {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    (h : Related p layout payload r s) : r .phase = controlPhase s.core.control := by
  rcases h with ⟨e, instruction, pc, running⟩ | ⟨e, outcome, stopped⟩
  · exact running.phase
  · exact stopped.phase_control

theorem Related.busy {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    (h : Related p layout payload r s) (query : Values Reactive.Input) :
    Reactive.busy.eval query r = BitVec.ofBool (Engine.Reactive.busy s.core) := by
  rw [show Reactive.busy.eval query r =
    BitVec.ofBool (decide (r .phase ≠ 0)) &&&
      BitVec.ofBool (decide ((r .phase).toNat < 5)) by
        simp [Reactive.busy, Reactive.both, Expr.eval]
        rfl]
  rw [h.phase]
  cases control : s.core.control
  case stopped reason =>
    cases reason <;> simp [controlPhase, Engine.Reactive.busy, control]
  all_goals simp [controlPhase, Engine.Reactive.busy, control]

def slotRetained : Transfer.Slot → Bool
  | .completed _ => true
  | _ => false

theorem Related.retained {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    (h : Related p layout payload r s) : r .retained = BitVec.ofBool (slotRetained s.buffers.slot) := by
  rcases h with ⟨e, instruction, pc, running⟩ | ⟨e, outcome, stopped⟩
  · simpa only [running.slot, slotRetained, BitVec.ofBool_false] using running.retained
  · simpa only [stopped.slot, slotRetained, BitVec.ofBool_true] using stopped.retained

theorem Related.completed_of_retained {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    (h : Related p layout payload r s) (retained : r .retained = 1) :
    ∃ e outcome, Stopped p layout payload r s e outcome := by
  rcases h with ⟨e, instruction, pc, running⟩ | ⟨e, outcome, stopped⟩
  · have impossible := running.retained.symm.trans retained
    contradiction
  · exact ⟨e, outcome, stopped⟩

theorem RelatedSram.phase {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : SramState.State} {source : Program.Buffered.State}
    (h : RelatedSram p layout payload actual source) :
    actual.registers (.core .phase) = controlPhase source.core.control := by
  rcases h with ⟨rows, dictionary, _, _, related⟩
  exact related.phase

theorem RelatedSram.busy {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : SramState.State} {source : Program.Buffered.State}
    (h : RelatedSram p layout payload actual source) (query : Values Reactive.Input) :
    Reactive.busy.eval query (SramExecution.core actual.registers) =
      BitVec.ofBool (Engine.Reactive.busy source.core) := by
  rcases h with ⟨rows, dictionary, _, _, related⟩
  exact related.busy query

theorem RelatedSram.retained {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : SramState.State} {source : Program.Buffered.State}
    (h : RelatedSram p layout payload actual source) :
    actual.registers (.core .retained) = BitVec.ofBool (slotRetained source.buffers.slot) := by
  rcases h with ⟨rows, dictionary, _, _, related⟩
  exact related.retained

theorem RelatedSram.valid {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : SramState.State} {source : Program.Buffered.State}
    (h : RelatedSram p layout payload actual source) : actual.registers (.core .valid) = 1 := by
  rcases h with ⟨rows, dictionary, _, _, related⟩
  rcases related with ⟨e, instruction, pc, running⟩ | ⟨e, outcome, stopped⟩
  · exact running.common.valid
  · exact stopped.common.valid

end Pinwheel.Hardware.Buffered.Refinement
