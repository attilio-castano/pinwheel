import Pinwheel.Hardware.Buffered.GenericStart
import Pinwheel.Hardware.Buffered.GenericSramRelation

/-! A reusable certified image at the actual SRAM boundary. Its witness does
not require the transfer slot to be free; START admission remains an actual
controller guard. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

def InstalledSram (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (actual : SramState.State) : Prop :=
  ∃ rows dictionary,
    SramExecution.Resident actual rows dictionary ∧
    SramExecution.Ready actual rows ∧
    GenericStart.Installed p layout (SramExecution.reference actual rows dictionary) ∧
    actual.registers (.core .valid) = 1

theorem RelatedSram.installed {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : SramState.State} {source : Program.Buffered.State}
    (h : RelatedSram p layout payload actual source) : InstalledSram p layout actual := by
  rcases h with ⟨rows, dictionary, resident, ready, related⟩
  rcases related with ⟨e, instruction, pc, running⟩ | ⟨e, outcome, stopped⟩
  · exact ⟨rows, dictionary, resident, ready,
      ⟨running.common.count, running.common.span, running.common.idleLevels,
        running.common.idleEnabled, running.common.image⟩, running.common.valid⟩
  · exact ⟨rows, dictionary, resident, ready,
      ⟨stopped.common.count, stopped.common.span, stopped.common.idleLevels,
        stopped.common.idleEnabled, stopped.common.image⟩, stopped.common.valid⟩

theorem InstalledSram.start {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {actual : SramState.State} (h : InstalledSram p layout actual)
    (i : Values Reactive.Input)
    (starting : Reactive.starting.eval i (SramExecution.core actual.registers) = 1) :
    RelatedSram p layout (i .txData) (actual.step i)
      (GenericStart.started p (SramExecution.core actual.registers) i) := by
  rcases h with ⟨rows, dictionary, resident, ready, installed, valid⟩
  have accepted : Reactive.starting.eval i (SramExecution.reference actual rows dictionary) = 1 :=
    (SramExecution.starting_withWords i (SramExecution.core actual.registers) _).trans starting
  have executing := (SpiAdmission.starting_controls i (SramExecution.core actual.registers) starting).executing
  refine ⟨rows, dictionary,
    SramExecution.resident_executing actual i rows dictionary executing resident,
    SramExecution.ready_executing actual i rows dictionary executing resident, ?_⟩
  rw [SramExecution.reference_step_eq actual i rows dictionary executing resident ready]
  exact GenericStart.start_related i (SramExecution.reference actual rows dictionary) installed accepted

end Pinwheel.Hardware.Buffered.Refinement
