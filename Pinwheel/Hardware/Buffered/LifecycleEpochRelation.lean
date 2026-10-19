import Pinwheel.Hardware.Buffered.LifecycleEpochBuffered
import Pinwheel.Hardware.Buffered.GenericSramRelation

/-! Generic correspondence is compatible with a later logical reset epoch.
The wire transfer sequence stays exact; the source epoch is not an observed
wire field and adds no replay-authentication claim. -/
namespace Pinwheel.Hardware.Buffered.Lifecycle.EpochView
open Pinwheel.Hardware Pinwheel.Program

theorem datapath (offset : Nat) {payload : BitVec 32} {r : Values Reactive.Register}
    {e : Transfer.Execution} (h : Refinement.Datapath payload r e) :
    Refinement.Datapath payload r (execution offset e) := by
  exact ⟨h.bounded, h.tx, h.txLength, h.rxCapacity, h.consumed, h.shifted,
    h.rxLength, h.received, h.generation, h.transfer⟩
  done

theorem common (offset : Nat) {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    (h : Refinement.Common p layout payload r s e) :
    Refinement.Common p layout payload r (buffered offset s) (execution offset e) := by
  exact ⟨h.count, h.span, h.idleLevels, h.idleEnabled, h.image, h.valid,
    datapath offset h.data, congrArg (identity offset) h.owner, h.pins, h.scratch⟩
  done

theorem running (offset : Nat) {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Refinement.Running p layout payload r s e instruction pc) :
    Refinement.Running p layout payload r (buffered offset s) (execution offset e) instruction pc := by
  refine ⟨common offset h.common, ?_, h.within, h.fetch, h.coordinates, h.virtualPC,
    h.currentControl, h.caches, h.control, h.retained, h.first, h.second⟩
  simp only [buffered, state, h.slot, slot]
  done

theorem stopped (offset : Nat) {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    {outcome : Transfer.Outcome}
    (h : Refinement.Stopped p layout payload r s e outcome) :
    Refinement.Stopped p layout payload r (buffered offset s) (execution offset e) outcome := by
  refine ⟨common offset h.common, ?_, h.control, h.phase, h.retained, h.pc, h.virtualPC,
    h.outer, h.inner, h.currentControl, h.remaining, h.waitLeft, h.cachedDuration,
    h.cachedBudget, h.cachedCheck, h.cachedWait, h.cachedTerminal, h.cachedBranch⟩
  simp only [buffered, state, h.slot, slot, completion]
  done

theorem related (offset : Nat) {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    (h : Refinement.Related p layout payload r s) :
    Refinement.Related p layout payload r (buffered offset s) := by
  rcases h with ⟨e, instruction, pc, h⟩ | ⟨e, outcome, h⟩
  · exact Or.inl ⟨execution offset e, instruction, pc, running offset h⟩
  · exact Or.inr ⟨execution offset e, outcome, stopped offset h⟩
  done

theorem relatedSram (offset : Nat) {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {actual : SramState.State} {s : Program.Buffered.State}
    (h : Refinement.RelatedSram p layout payload actual s) :
    Refinement.RelatedSram p layout payload actual (buffered offset s) := by
  rcases h with ⟨rows, dictionary, resident, ready, h⟩
  exact ⟨rows, dictionary, resident, ready, related offset h⟩
  done

end Pinwheel.Hardware.Buffered.Lifecycle.EpochView
