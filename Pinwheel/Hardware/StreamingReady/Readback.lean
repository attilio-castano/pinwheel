import Pinwheel.Hardware.Streaming.Readback

namespace Pinwheel.Hardware.StreamingReady.Readback

/-- Exact three-bit phase comparison, useful after CIRCT's Boolean factoring. -/
theorem phase_lt5 : ∀ x : BitVec 3,
    BitVec.ofBool (decide (x.toNat < (5#3).toNat)) =
      ~~~(x.extractLsb' 2 1) ||| (~~~(x.extractLsb' 1 1) &&& ~~~(x.extractLsb' 0 1)) := by
  decide +kernel

end Pinwheel.Hardware.StreamingReady.Readback
