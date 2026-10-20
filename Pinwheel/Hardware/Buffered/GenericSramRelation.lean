import Pinwheel.Hardware.Buffered.GenericRelation
import Pinwheel.Hardware.Buffered.SpiSramRelation

/-! Generic source agreement at the actual typed digital SRAM boundary.
Resident and Ready connect both stored replicas and their registered reads. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

def RelatedSram (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (payload : BitVec 32) (actual : SramState.State) (source : Program.Buffered.State) : Prop :=
  ∃ rows dictionary,
    SramExecution.Resident actual rows dictionary ∧
    SramExecution.Ready actual rows ∧
    Related p layout payload (SramExecution.reference actual rows dictionary) source

theorem Related.pins {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : Values Reactive.Register} {source : Program.Buffered.State}
    (h : Related p layout payload actual source) :
    source.core.pins = ⟨actual .levels, actual .enabled⟩ := by
  rcases h with ⟨e, instruction, pc, running⟩ | ⟨e, outcome, stopped⟩
  · exact running.common.pins
  · exact stopped.common.pins

theorem Related.scratch {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : Values Reactive.Register} {source : Program.Buffered.State}
    (h : Related p layout payload actual source) :
    GenericPhase.Scratch (actual .scratch) source.core.samples := by
  rcases h with ⟨e, instruction, pc, running⟩ | ⟨e, outcome, stopped⟩
  · exact running.common.scratch
  · exact stopped.common.scratch

theorem RelatedSram.pins {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : SramState.State} {source : Program.Buffered.State}
    (h : RelatedSram p layout payload actual source) :
    source.core.pins = ⟨actual.registers (.core .levels), actual.registers (.core .enabled)⟩ := by
  rcases h with ⟨rows, dictionary, _, _, related⟩
  exact related.pins

theorem RelatedSram.scratch {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : SramState.State} {source : Program.Buffered.State}
    (h : RelatedSram p layout payload actual source) :
    GenericPhase.Scratch (actual.registers (.core .scratch)) source.core.samples := by
  rcases h with ⟨rows, dictionary, _, _, related⟩
  exact related.scratch

theorem RelatedSram.datapath {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : SramState.State} {source : Program.Buffered.State}
    (h : RelatedSram p layout payload actual source) :
    ∃ e, Datapath payload (SramExecution.core actual.registers) e ∧
      e.request.identity = source.owner ∧
      (source.buffers.slot = .running e ∨
        ∃ outcome, source.buffers.slot = .completed ⟨e, outcome⟩) := by
  rcases h with ⟨rows, dictionary, _, _, related⟩
  rcases related with ⟨e, instruction, pc, running⟩ | ⟨e, outcome, stopped⟩
  · exact ⟨e, running.common.data.actual_core, running.common.owner, Or.inl running.slot⟩
  · exact ⟨e, stopped.common.data.actual_core, stopped.common.owner,
      Or.inr ⟨outcome, stopped.slot⟩⟩

end Pinwheel.Hardware.Buffered.Refinement
