import Std

/-! The waveform contract for observing one 64-slot Classical CAN window.
At 4 MHz, a 125 kbit/s bit is nominally 32 samples long. The peer's absolute
slot boundaries may move independently within four samples of nominal. -/
namespace Pinwheel.Program.StreamingCANCore

def rawBit (raw : List (BitVec 2)) (k : Nat) : Bool := (raw[k]?.getD 0).getLsbD 0

def apertures (fall : Nat) : List Nat := (List.range 64).map (fun k => fall + 16 + 32 * k)

/-- The peer fixes the symbol on each interval between its own boundaries.
The start transition is the time origin for the bounded clock skew. -/
structure PeerFrame (raw : List (BitVec 2)) (slots : List Bool) where
  fall : Nat
  boundary : Nat → Nat
  count : slots.length = 64
  startAtFall : boundary 0 = fall
  skew : ∀ k ≤ 64, fall + 32 * k ≤ boundary k + 4 ∧ boundary k ≤ fall + 32 * k + 4
  idle : ∀ t < fall, rawBit raw t = true
  bits : ∀ k < 64, ∀ t, boundary k ≤ t → t < boundary (k + 1) →
    rawBit raw t = slots[k]?.getD true
  length : raw.length = fall + 2053

private theorem in_slot (peer : PeerFrame raw slots) (k : Nat) (bound : k < 64) :
    peer.boundary k ≤ peer.fall + 16 + 32 * k ∧
      peer.fall + 16 + 32 * k < peer.boundary (k + 1) := by
  have upper := (peer.skew k (by omega)).2
  have lower := (peer.skew (k + 1) (by omega)).1
  omega

theorem PeerFrame.dominant (peer : PeerFrame raw slots) (first : slots[0]? = some false) :
    rawBit raw peer.fall = false := by
  have next := (peer.skew 1 (by decide)).1
  have start := peer.bits 0 (by decide) peer.fall (peer.startAtFall ▸ Nat.le_refl _)
    (show peer.fall < peer.boundary 1 by omega)
  simpa only [first, Option.getD_some] using start

/-- Every actual cell contains its nominal center sample, even at the
extreme skew bounds, so the result uses exactly the peer's 64 slot values. -/
theorem PeerFrame.samples (peer : PeerFrame raw slots) :
    (apertures peer.fall).map (rawBit raw) = slots := by
  apply List.ext_getElem
  · simp [apertures, peer.count]
  · intro k inside slotBound
    have bound : k < 64 := by simpa only [peer.count] using slotBound
    have window := in_slot peer k bound
    have level := peer.bits k bound _ window.1 window.2
    simpa only [apertures, List.getElem_map, List.getElem_range,
      List.getElem?_eq_getElem slotBound, Option.getD_some] using level

end Pinwheel.Program.StreamingCANCore
