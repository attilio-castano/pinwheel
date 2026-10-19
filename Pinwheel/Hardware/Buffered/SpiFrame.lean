import Pinwheel.Hardware.Buffered.SpiEntry
import Pinwheel.Hardware.Buffered.SpiCircuit
import Pinwheel.Hardware.Buffered.SpiGeometry

/-! Control-frame preservation under the actual successful entry update.
Payload and source-interpreter correspondence are separate obligations. -/
namespace Pinwheel.Hardware.Buffered.SpiFrame
open Pinwheel.Hardware SpiCoordinates

theorem geometry_runEntryTick (c : SpiSource.Config) (i : Values Reactive.Input)
    (r : Values Reactive.Register) (h : SpiGeometry.Geometry c r) :
    SpiGeometry.Geometry c (SpiCircuit.runEntryTick i r) :=
  ⟨h.count, h.virtualSpan, h.idleLevels, h.idleEnabled⟩

theorem image_runEntryTick (c : SpiSource.Config) (i : Values Reactive.Input)
    (r : Values Reactive.Register) (image : ∀ k, r (.word k) = SpiSource.fullWords c k) :
    ∀ k, SpiCircuit.runEntryTick i r (.word k) = SpiSource.fullWords c k := image

theorem valid_runEntryTick (i : Values Reactive.Input) (r : Values Reactive.Register)
    (valid : r .valid = 1) : SpiCircuit.runEntryTick i r .valid = 1 := valid

theorem run_entry_at (c : SpiSource.Config) (target : Nat)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (pc : Reactive.entryPC.eval i r = BitVec.ofNat 7 (physicalPC c target))
    (virtualPC : Reactive.entryVirtual.eval i r = BitVec.ofNat 11 target)
    (outerIndex : Reactive.entryOuter.eval i r = BitVec.ofNat 3 (outer c target))
    (innerIndex : Reactive.entryInner.eval i r = BitVec.ofNat 3 (inner c target))
    (control : Reactive.entryControl.eval i r =
      SpiSource.control c (BitVec.ofNat 6 (physicalPC c target)))
    (count : r .count = 4) (span : r .virtualSpan = BitVec.ofNat 11 (bitSpan c + 2))
    (image : ∀ k, r (.word k) = SpiSource.fullWords c k) :
    At c target (SpiCircuit.runEntryTick i r) := by
  refine ⟨rfl, ?_, pc, congrArg (fun word : BitVec 24 => word.extractLsb' 0 22) control,
    outerIndex, innerIndex, count, span, image⟩
  simp [SpiCircuit.runEntryTick, virtualPC, ← BitVec.setWidth_ushiftRight_eq_extractLsb,
    BitVec.setWidth_ofNat_of_le (by decide : 10 ≤ 11)]
  done

end Pinwheel.Hardware.Buffered.SpiFrame
