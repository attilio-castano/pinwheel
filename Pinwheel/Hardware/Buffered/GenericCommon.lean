import Pinwheel.Hardware.Buffered.GenericRelation
import Pinwheel.Hardware.Buffered.GenericPhase
import Pinwheel.Hardware.Buffered.GenericPhaseStop

/-! Frame and data preservation for clock-only updates. These lemmas carry no
assumed source/circuit execution agreement beyond their explicit invariant. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

theorem Datapath.holdTick {payload : BitVec 32} {r : Values Reactive.Register}
    {e : Transfer.Execution} (h : Datapath payload r e)
    (raw : BitVec 2) (remaining waitLeft : BitVec 8) :
    Datapath payload (GenericPhase.holdTick r raw remaining waitLeft) e :=
  ⟨h.bounded, h.tx, h.txLength, h.rxCapacity, h.consumed, h.shifted,
    h.rxLength, h.received, h.generation, h.transfer⟩

theorem Datapath.stopTick {payload : BitVec 32} {r : Values Reactive.Register}
    {e : Transfer.Execution} (h : Datapath payload r e)
    (raw : BitVec 2) (timeout : Bool) :
    Datapath payload (GenericPhase.stopTick r raw timeout) e :=
  ⟨h.bounded, h.tx, h.txLength, h.rxCapacity, h.consumed, h.shifted,
    h.rxLength, h.received, h.generation, h.transfer⟩

theorem Common.holdTick {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} (h : Common p layout payload r s e)
    (raw : BitVec 2) (remaining waitLeft : BitVec 8) (control : Engine.Reactive.Control 1023) :
    Common p layout payload (GenericPhase.holdTick r raw remaining waitLeft)
      {s with
        core := {s.core with control}
        samplerFirst := raw
        samplerSecond := s.samplerFirst} e :=
  ⟨h.count, h.span, h.idleLevels, h.idleEnabled, h.image, h.valid,
    h.data.holdTick raw remaining waitLeft, h.owner, h.pins, h.scratch⟩

theorem Common.stopTick {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} (h : Common p layout payload r s e)
    (raw : BitVec 2) (timeout : Bool) (outcome : Transfer.Outcome) :
    Common p layout payload (GenericPhase.stopTick r raw timeout)
      (Program.Buffered.terminal p capacity s outcome) e := by
  refine ⟨h.count, h.span, h.idleLevels, h.idleEnabled, h.image, h.valid,
    h.data.stopTick raw timeout, h.owner, ?_, h.scratch⟩
  change p.idle = ⟨r .idleLevels, r .idleEnabled⟩
  rw [h.idleLevels, h.idleEnabled]
  done

end Pinwheel.Hardware.Buffered.Refinement
