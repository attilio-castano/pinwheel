import Pinwheel.Hardware.Switch.Interface
import Pinwheel.Hardware.Stream.FifoCircuit
import Pinwheel.Hardware.Stream.MapValues

/-! Packet storage for the switch reuses the verified stream FIFO unchanged.
Destination bits precede payload bits in each cell. Mapping values through an
encoding preserves the queue's reset, ready, replacement, and ordering rules.
-/

namespace Pinwheel.Hardware.Switch.PacketEncoding

open Physical

def pack (e : DestinationEncoding outputs) (p : Packet outputs (BitVec w)) : BitVec (e.width + w) :=
  encodeDestination e p.destination ++ p.payload

def payload (x : BitVec (dw + w)) : BitVec w := x.extractLsb' 0 w
def destination (x : BitVec (dw + w)) : BitVec dw := x.extractLsb' w dw

def unpack (e : DestinationEncoding outputs) (x : BitVec (e.width + w)) : Option (Packet outputs (BitVec w)) :=
  if h : (destination x).toNat < outputs then
    some ⟨⟨(destination x).toNat, h⟩, payload x⟩
  else none

@[simp] theorem payload_pack (e : DestinationEncoding outputs) (p : Packet outputs (BitVec w)) :
    payload (pack e p) = p.payload := BitVec.extractLsb'_append_eq_right

@[simp] theorem destination_pack (e : DestinationEncoding outputs) (p : Packet outputs (BitVec w)) :
    destination (pack e p) = encodeDestination e p.destination := BitVec.extractLsb'_append_eq_left

@[simp] theorem destination_pack_toNat (e : DestinationEncoding outputs) (p : Packet outputs (BitVec w)) :
    (destination (pack e p)).toNat = p.destination.val := by
  simp only [destination_pack, encodeDestination_toNat]

@[simp] theorem unpack_pack (e : DestinationEncoding outputs) (p : Packet outputs (BitVec w)) :
    unpack e (pack e p) = some p := by
  simp [unpack, encodeDestination_toNat]

theorem pack_of_unpack (e : DestinationEncoding outputs) (x : BitVec (e.width + w))
    (p : Packet outputs (BitVec w)) (h : unpack e x = some p) : pack e p = x := by
  unfold unpack at h
  split at h
  · cases Option.some.inj h
    change BitVec.ofNat e.width (x.extractLsb' w e.width).toNat ++ x.extractLsb' 0 w = x
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.extractLsb'_append_extractLsb'
  · contradiction

theorem pack_injective (e : DestinationEncoding outputs) :
    Function.Injective (pack e (w := w)) := by
  intro a b h
  exact Option.some.inj (by simpa using congrArg (unpack e) h)

theorem encodeDestination_injective (e : DestinationEncoding outputs) :
    Function.Injective (encodeDestination e) := by
  intro a b h
  apply Fin.ext
  simpa only [encodeDestination_toNat] using congrArg BitVec.toNat h

/-- Raw legal input wires can enter the FIFO without re-encoding logic. The
same destination check rejects every unused binary code. -/
theorem decode_raw_pack (e : DestinationEncoding (m + 1)) (d : BitVec e.width) (p : BitVec w) :
    (Physical.decodePacket d p).map (pack e) =
      if d.toNat < m + 1 then some (d ++ p) else none := by
  by_cases h : d.toNat < m + 1 <;>
    simp [Physical.decodePacket, h, pack, encodeDestination, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem decode_raw_isSome (d : BitVec dw) (p : BitVec w) :
    (Physical.decodePacket (m := m) d p).isSome = decide (d.toNat < m + 1) := by
  by_cases h : d.toNat < m + 1 <;> simp [Physical.decodePacket, h]

def cells (e : DestinationEncoding outputs) (q : List (Packet outputs (BitVec w))) :
    Values (Stream.CellReg (e.width + w) depth) := Stream.cells (q.map (pack e))

def head (e : DestinationEncoding outputs) (q : List (Packet outputs (BitVec w))) : BitVec (e.width + w) :=
  (q.head?.map (pack e)).getD 0

@[simp] theorem head_payload (e : DestinationEncoding outputs) (q : List (Packet outputs (BitVec w))) :
    payload (head e q) = (q.head?.map Packet.payload).getD 0 := by
  cases q <;> simp [head, payload, pack, BitVec.extractLsb'_append_eq_right]

@[simp] theorem head_destination (e : DestinationEncoding outputs) (q : List (Packet outputs (BitVec w))) :
    destination (head e q) = (q.head?.map (fun p => encodeDestination e p.destination)).getD 0 := by
  cases q <;> simp [head, destination, pack, BitVec.extractLsb'_append_eq_left]

theorem head_matches (e : DestinationEncoding outputs) (q : List (Packet outputs (BitVec w)))
    (o : Fin outputs) :
    (q.head?.isSome && (destination (head e q) == encodeDestination e o)) =
      q.head?.any (fun p => decide (p.destination = o)) := by
  cases q with
  | nil => rfl
  | cons p rest =>
    simp only [head_destination, List.head?_cons, Option.isSome_some, Option.map_some,
      Option.getD_some, Bool.true_and, Option.any_some]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    exact (encodeDestination_injective e).eq_iff

theorem cell_valid (e : DestinationEncoding outputs) (q : List (Packet outputs (BitVec w)))
    (hq : q.length ≤ depth) (i : Values I) (k : Nat) :
    (Stream.cellValid (e.width + w) depth k).eval i (cells e q) = BitVec.ofBool q[k]?.isSome := by
  dsimp only [cells]
  rw [Stream.cellValid_eval (q.map (pack e)) (by simpa using hq)]
  simp

theorem cell_head (e : DestinationEncoding outputs) (q : List (Packet outputs (BitVec w)))
    (hq : q.length ≤ depth) (i : Values I) :
    (Stream.cellData (e.width + w) depth 0).eval i (cells e q) = head e q := by
  dsimp only [cells]
  rw [Stream.cellData_eval (q.map (pack e)) (by simpa using hq)]
  cases q <;> rfl

theorem head_valid (e : DestinationEncoding outputs) (q : List (Packet outputs (BitVec w)))
    (hq : q.length ≤ depth) (i : Values I) :
    (Stream.cellValid (e.width + w) depth 0).eval i (cells e q) = BitVec.ofBool q.head?.isSome := by
  rw [cell_valid e q hq]
  cases q <;> rfl

theorem cell_head_payload (e : DestinationEncoding outputs) (q : List (Packet outputs (BitVec w)))
    (hq : q.length ≤ depth) (i : Values I) :
    ((Stream.cellData (e.width + w) depth 0).eval i (cells e q)).extractLsb' 0 w =
      (q.head?.map Packet.payload).getD 0 := by
  rw [cell_head e q hq]
  exact head_payload e q

theorem cell_head_destination (e : DestinationEncoding outputs) (q : List (Packet outputs (BitVec w)))
    (hq : q.length ≤ depth) (i : Values I) :
    ((Stream.cellData (e.width + w) depth 0).eval i (cells e q)).extractLsb' w e.width =
      (q.head?.map (fun p => encodeDestination e p.destination)).getD 0 := by
  rw [cell_head e q hq]
  exact head_destination e q

theorem fifo_step (e : DestinationEncoding outputs) (i : Stream.Input (Packet outputs (BitVec w)))
    (q : List (Packet outputs (BitVec w))) (hq : q.length ≤ depth)
    (r : Stream.CellReg (e.width + w) depth b) :
    (Stream.Fifo.circuit (e.width + w) depth).step
      (Stream.inputValues (Stream.mapInput (pack e) i)) (cells e q) r =
      cells e ((Stream.queue depth).step i q) r := by
  dsimp only [cells]
  rw [Stream.Fifo.fifo_step _ _ (by simpa using hq), Stream.queue_map_step]

theorem fifo_output (e : DestinationEncoding outputs) (i : Stream.Input (Packet outputs (BitVec w)))
    (q : List (Packet outputs (BitVec w))) (hq : q.length ≤ depth) (hd : 0 < depth)
    (o : Stream.Out (e.width + w) b) :
    (Stream.Fifo.circuit (e.width + w) depth).observe
      (Stream.inputValues (Stream.mapInput (pack e) i)) (cells e q) o =
      Stream.outputValues
        ⟨((Stream.queue depth).component.observe i q).ready,
         ((Stream.queue depth).component.observe i q).offered.map (pack e)⟩ o := by
  dsimp only [cells]
  rw [Stream.Fifo.fifo_output _ _ (by simpa using hq) hd, Stream.queue_map_observe]

end Pinwheel.Hardware.Switch.PacketEncoding
