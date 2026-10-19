import Pinwheel.Hardware.Buffered.SpiRelation

/-! The source relation at the actual digital SRAM boundary. Its resident-image
witness is connected to both physical instruction replicas and registered read
responses by the existing Resident/Ready predicates. -/
namespace Pinwheel.Hardware.Buffered.SpiRefinement
open Pinwheel.Hardware Pinwheel.Program

def RelatedSram (c : SpiSource.Config) (payload : BitVec 32)
    (actual : SramState.State) (source : Program.Buffered.State) : Prop :=
  ∃ rows dictionary,
    SramExecution.Resident actual rows dictionary ∧
    SramExecution.Ready actual rows ∧
    Related c payload (SramExecution.reference actual rows dictionary) source

theorem Datapath.actual_core {payload : BitVec 32} {actual : SramState.State}
    {rows : Memory.Contents 6 92} {dictionary : Memory.Contents 4 56}
    {e : Transfer.Execution}
    (h : Datapath payload (SramExecution.reference actual rows dictionary) e) :
    Datapath payload (SramExecution.core actual.registers) e :=
  ⟨h.bounded, h.tx, h.txLength, h.rxCapacity, h.consumed, h.shifted,
    h.rxLength, h.received, h.generation, h.transfer⟩

/-- Pin agreement concerns the actual controller registers, independent of the
resident-image witness used to establish correct SRAM instruction selection. -/
theorem RelatedSram.pins {c : SpiSource.Config} {payload : BitVec 32}
    {actual : SramState.State} {source : Program.Buffered.State}
    (h : RelatedSram c payload actual source) :
    source.core.pins = ⟨actual.registers (.core .levels), actual.registers (.core .enabled)⟩ := by
  rcases h with ⟨rows, dictionary, _, _, related⟩
  rcases related with ⟨e, pc, remaining, running⟩ | ⟨e, complete, stopped⟩
  · exact running.common.pins
  · exact stopped.common.pins
  done

/-- The owned running or retained execution carries the exact actual TX/RX
counts and packed prefix. Unused high TX bits remain in the original payload.
-/
theorem RelatedSram.datapath {c : SpiSource.Config} {payload : BitVec 32}
    {actual : SramState.State} {source : Program.Buffered.State}
    (h : RelatedSram c payload actual source) :
    ∃ e, Datapath payload (SramExecution.core actual.registers) e ∧
      e.request.identity = source.owner ∧
      (source.buffers.slot = .running e ∨
        ∃ complete, source.buffers.slot = .completed ⟨e, outcome complete⟩) := by
  rcases h with ⟨rows, dictionary, _, _, related⟩
  rcases related with ⟨e, pc, remaining, running⟩ | ⟨e, complete, stopped⟩
  · exact ⟨e, running.common.data.actual_core, running.common.owner, Or.inl running.slot⟩
  · exact ⟨e, stopped.common.data.actual_core, stopped.common.owner,
      Or.inr ⟨complete, stopped.slot⟩⟩
  done

end Pinwheel.Hardware.Buffered.SpiRefinement
