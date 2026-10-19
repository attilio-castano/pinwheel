import Pinwheel.Program.StreamingSafety

/-! Bounded exported-RX custody. A popped core word remains owned by the
frontend until a subsequent admitted request acknowledges its exact end. -/
namespace Pinwheel.Program.Streaming

structure Receipt where
  data : BitVec 64 := 0
  start : BitVec 16 := 0
  bits : Fin 65 := 0
  ack : BitVec 16 := 0
  deriving DecidableEq, Repr

def Receipt.endOffset (r : Receipt) : BitVec 16 := r.start + BitVec.ofNat 16 r.bits.val

def Receipt.drained (r : Receipt) : Bool := r.ack == r.endOffset

/-- Naturals are proof counters, not additional operational storage. -/
structure Receipt.Valid (r : Receipt) (produced popped : Nat) : Prop where
  ackBefore : r.ack.toNat ≤ r.start.toNat
  endEquals : r.start.toNat + r.bits.val = popped
  exported : popped ≤ produced
  representable : produced < 65536

/-- Only exact acknowledgement allows the old receipt to be overwritten. -/
def Receipt.admit (r : Receipt) (popped ack : BitVec 16) : Receipt :=
  if ack == r.endOffset then { start := popped, ack := ack } else r

/-- The frontend takes custody of one existing RX word, including partial words. -/
def Receipt.capture (r : Receipt) (chunk : Chunk) : Receipt :=
  { r with
    data := chunk.data.setWidth 64,
    bits := ⟨chunk.validBits, by have := chunk.validBits_le; omega⟩ }

def releaseAllowed (s : State addrBits) (i : Input) (receipt : Receipt) : Bool :=
  s.canRelease i && receipt.drained

theorem Receipt.end_toNat (r : Receipt) (valid : r.Valid produced popped) :
    r.endOffset.toNat = popped := by
  rcases valid with ⟨ackBefore, endEquals, exported, representable⟩
  simp only [endOffset, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem Receipt.reject_ack (r : Receipt) (popped ack : BitVec 16)
    (wrong : ack ≠ r.endOffset) : r.admit popped ack = r := by
  simp [admit, wrong]

theorem Receipt.admit_valid (r : Receipt) (produced : Nat) (popped ack : BitVec 16)
    (valid : r.Valid produced popped.toNat) (exactAck : ack = r.endOffset) :
    (r.admit popped ack).Valid produced popped.toNat := by
  have endNat := r.end_toNat valid
  rcases valid with ⟨ackBefore, endEquals, exported, representable⟩
  constructor <;> simp_all [admit]

theorem Receipt.capture_valid (r : Receipt) (chunk : Chunk) (produced popped : Nat)
    (valid : r.Valid produced popped) (empty : r.bits = 0)
    (available : popped + chunk.validBits ≤ produced) :
    (r.capture chunk).Valid produced (popped + chunk.validBits) := by
  constructor
  · exact valid.ackBefore
  · simpa only [capture, empty, Fin.val_zero, Nat.add_zero] using
      congrArg (fun n => n + chunk.validBits) valid.endEquals
  · exact available
  · exact valid.representable

theorem Receipt.drained_iff (r : Receipt) (valid : r.Valid produced popped) :
    r.drained = true ↔ r.ack.toNat = popped := by
  simp only [drained, beq_iff_eq, ← BitVec.toNat_inj, r.end_toNat valid]

theorem Receipt.unacknowledged_blocks (r : Receipt) (valid : r.Valid produced popped)
    (unacknowledged : r.ack.toNat < popped) : r.drained = false := by
  apply Bool.eq_false_iff.mpr
  intro drained
  exact (Nat.ne_of_lt unacknowledged) ((r.drained_iff valid).mp drained)

theorem Receipt.positive_receipt_blocks (r : Receipt) (valid : r.Valid produced popped)
    (nonempty : 0 < r.bits.val) : r.drained = false := by
  apply r.unacknowledged_blocks valid
  have ackBefore := valid.ackBefore
  have endEquals := valid.endEquals
  omega

/-- An exact retransmission reads the same retained interval; it does not admit a new request. -/
def Receipt.replay (r : Receipt) : Receipt := r

theorem Receipt.replay_valid (r : Receipt) (valid : r.Valid produced popped) :
    r.replay.Valid produced popped := valid

theorem Receipt.replay_preserves (r : Receipt) :
    r.replay.data = r.data ∧ r.replay.start = r.start ∧ r.replay.bits = r.bits ∧
      r.replay.ack = r.ack := ⟨rfl, rfl, rfl, rfl⟩

end Pinwheel.Program.Streaming
