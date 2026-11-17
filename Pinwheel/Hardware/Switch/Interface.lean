import Pinwheel.Hardware.Switch.Model
import Pinwheel.Hardware.Stream.Compose

namespace Pinwheel.Hardware.Switch.Physical

set_option backward.isDefEq.respectTransparency false

/-- Caller-selected physical destination width, including a nonzero width for
the one-output case. Extra binary codes are rejected at admission. -/
structure DestinationEncoding (outputs : Nat) where
  width : Nat
  positive : 0 < width
  fits : outputs ≤ 2 ^ width

def lanePorts (width count : Nat) : Stream.Ports where
  size := count
  widths := fun _ => width
  names := fun k => "lane_" ++ Nat.repr k.val
  distinct := by
    intro a b h
    simp only [String.append_right_inj] at h
    exact Fin.ext (Nat.repr_injective h)

abbrev Lane (w count : Nat) := (lanePorts w count).Signal

/-- Enumeration order: reset, all input valids, all destinations, all payloads,
then all output readies. The explicit clock is added by the existing emitter. -/
abbrev In (n m dw w : Nat) := Stream.Joint (Lane 1 1)
  (Stream.Joint (Lane 1 (n + 1)) (Stream.Joint (Lane dw (n + 1))
    (Stream.Joint (Lane w (n + 1)) (Lane 1 (m + 1)))))

/-- Enumeration order: all input readies, all output valids, all output payloads. -/
abbrev Out (n m w : Nat) := Stream.Joint (Lane 1 (n + 1))
  (Stream.Joint (Lane 1 (m + 1)) (Lane w (m + 1)))

def indexedInterface (d : Hardware.Interface P) (stem : String) : Hardware.Interface P :=
  d.rename (fun p => stem ++ Nat.repr (d.position p).val) (by
    intro a b h
    simp only [Hardware.Interface.position_signal, String.append_right_inj] at h
    exact Fin.ext (Nat.repr_injective h))

def inputInterface (n m dw w : Nat) : Hardware.Interface (In n m dw w) :=
  indexedInterface
    (Stream.Joint.interface (lanePorts 1 1).interface
      (Stream.Joint.interface (lanePorts 1 (n+1)).interface
        (Stream.Joint.interface (lanePorts dw (n+1)).interface
          (Stream.Joint.interface (lanePorts w (n+1)).interface (lanePorts 1 (m+1)).interface)))) "in_"

def outputInterface (n m w : Nat) : Hardware.Interface (Out n m w) :=
  indexedInterface (Stream.Joint.interface (lanePorts 1 (n+1)).interface
    (Stream.Joint.interface (lanePorts 1 (m+1)).interface (lanePorts w (m+1)).interface)) "out_"

def reset : In n m dw w 1 := .left (.at ⟨0, by decide⟩)
def inValid (k : Fin (n+1)) : In n m dw w 1 := .right (.left (.at k))
def inDestination (k : Fin (n+1)) : In n m dw w dw := .right (.right (.left (.at k)))
def inPayload (k : Fin (n+1)) : In n m dw w w := .right (.right (.right (.left (.at k))))
def outReady (k : Fin (m+1)) : In n m dw w 1 := .right (.right (.right (.right (.at k))))
def inReady (k : Fin (n+1)) : Out n m w 1 := .left (.at k)
def outValid (k : Fin (m+1)) : Out n m w 1 := .right (.left (.at k))
def outPayload (k : Fin (m+1)) : Out n m w w := .right (.right (.at k))

structure Pins (n m dw w : Nat) where
  reset : BitVec 1
  valid : Fin (n+1) → BitVec 1
  destination : Fin (n+1) → BitVec dw
  payload : Fin (n+1) → BitVec w
  ready : Fin (m+1) → BitVec 1

def Pins.values (p : Pins n m dw w) : Values (In n m dw w)
  | _, .left (.at _) => p.reset
  | _, .right (.left (.at k)) => p.valid k
  | _, .right (.right (.left (.at k))) => p.destination k
  | _, .right (.right (.right (.left (.at k)))) => p.payload k
  | _, .right (.right (.right (.right (.at k)))) => p.ready k

def readPins (i : Values (In n m dw w)) : Pins n m dw w :=
  ⟨i reset, fun k => i (inValid k), fun k => i (inDestination k),
    fun k => i (inPayload k), fun k => i (outReady k)⟩

theorem readPins_values (p : Pins n m dw w) : readPins p.values = p := by
  cases p
  rfl

def decodePacket (destination : BitVec dw) (payload : BitVec w) : Option (Packet (m+1) (BitVec w)) :=
  if h : destination.toNat < m+1 then some ⟨⟨destination.toNat, h⟩, payload⟩ else none

def encodeDestination (e : DestinationEncoding outputs) (d : Fin outputs) : BitVec e.width :=
  BitVec.ofNat e.width d.val

theorem encodeDestination_toNat (e : DestinationEncoding outputs) (d : Fin outputs) :
    (encodeDestination e d).toNat = d.val := by
  simp only [encodeDestination, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le d.isLt e.fits)

theorem decodePacket_encode (e : DestinationEncoding (m+1)) (p : Packet (m+1) (BitVec w)) :
    decodePacket (encodeDestination e p.destination) p.payload = some p := by
  simp only [decodePacket, encodeDestination_toNat, dif_pos p.destination.isLt]

def decode (p : Pins n m dw w) : Switch.Input n (m+1) (BitVec w) where
  reset := p.reset == 1
  offered := fun k => if p.valid k = 1 then decodePacket (p.destination k) (p.payload k) else none
  ready := fun k => p.ready k == 1

def encode (e : DestinationEncoding (m+1)) (i : Switch.Input n (m+1) (BitVec w)) : Pins n m e.width w where
  reset := BitVec.ofBool i.reset
  valid := fun k => BitVec.ofBool (i.offered k).isSome
  destination := fun k => ((i.offered k).map (fun p => encodeDestination e p.destination)).getD 0
  payload := fun k => ((i.offered k).map Packet.payload).getD 0
  ready := fun k => BitVec.ofBool (i.ready k)

private theorem bool_roundtrip (b : Bool) : (BitVec.ofBool b == 1) = b := by
  cases b <;> rfl

theorem decode_encode (e : DestinationEncoding (m+1)) (i : Switch.Input n (m+1) (BitVec w)) :
    decode (encode e i) = i := by
  cases i with
  | mk rst offers ready =>
    simp only [decode, encode, bool_roundtrip]
    congr 1
    funext k
    cases offers k <;> simp [decodePacket_encode]

def admissible (p : Pins n m dw w) (k : Fin (n+1)) : Bool :=
  !(p.valid k == 1) || decide ((p.destination k).toNat < m+1)

theorem admissible_encode (e : DestinationEncoding (m+1)) (i : Switch.Input n (m+1) (BitVec w))
    (k : Fin (n+1)) : admissible (encode e i) k = true := by
  cases hi : i.offered k <;> simp [admissible, encode, hi, encodeDestination_toNat]

def outputValues (o : Switch.Output n (m+1) (BitVec w)) : Values (Out n m w)
  | _, .left (.at k) => BitVec.ofBool (o.ready k)
  | _, .right (.left (.at k)) => BitVec.ofBool (o.offered k).isSome
  | _, .right (.right (.at k)) => ((o.offered k).map (fun d => d.packet.payload)).getD 0

def observe (depth : Nat) (p : Pins n m dw w) (s : Switch.State n (m+1) (BitVec w)) :
    Values (Out n m w)
  | _, .left (.at k) => BitVec.ofBool ((Switch.observe depth (decode p) s).ready k && admissible p k)
  | _, .right (.left (.at k)) => BitVec.ofBool ((Switch.observe depth (decode p) s).offered k).isSome
  | _, .right (.right (.at k)) => ((Switch.observe depth (decode p) s).offered k).map
      (fun d => d.packet.payload) |>.getD 0

/-- The wrapper steps the logical model on decoded legal offers. Physical ready
is additionally masked, so an asserted invalid offer is never acknowledged. -/
def component (e : DestinationEncoding (m+1)) (depth : Nat) :
    Timed.Component (Values (In n m e.width w)) (Switch.State n (m+1) (BitVec w)) (Values (Out n m w)) :=
  ⟨fun i s => Switch.step depth (decode (readPins i)) s,
   fun i s => observe depth (readPins i) s⟩

theorem observe_encode (e : DestinationEncoding (m+1)) (depth : Nat)
    (i : Switch.Input n (m+1) (BitVec w)) (s : Switch.State n (m+1) (BitVec w))
    (p : Out n m w b) :
    observe depth (encode e i) s p = outputValues (Switch.observe depth i s) p := by
  cases p with
  | left p => cases p; simp only [observe, outputValues, decode_encode, admissible_encode, Bool.and_true]
  | right p => cases p with
    | left p => cases p; simp only [observe, outputValues, decode_encode]
    | right p => cases p; simp only [observe, outputValues, decode_encode]

theorem invalid_decodes_none (p : Pins n m dw w) (k : Fin (n+1))
    (hd : m+1 ≤ (p.destination k).toNat) : (decode p).offered k = none := by
  simp [decode, decodePacket, Nat.not_lt.mpr hd]

theorem invalid_ready_low (depth : Nat) (p : Pins n m dw w) (s : Switch.State n (m+1) (BitVec w))
    (k : Fin (n+1)) (hv : p.valid k = 1) (hd : m+1 ≤ (p.destination k).toNat) :
    observe depth p s (inReady k) = 0 := by
  simp [observe, inReady, admissible, hv, Nat.not_lt.mpr hd]

theorem ready_legal (depth : Nat) (p : Pins n m dw w) (s : Switch.State n (m+1) (BitVec w))
    (k : Fin (n+1)) (hd : (p.destination k).toNat < m+1) :
    observe depth p s (inReady k) = BitVec.ofBool ((Switch.observe depth (decode p) s).ready k) := by
  simp [observe, inReady, admissible, hd]

theorem ready_idle (depth : Nat) (p : Pins n m dw w) (s : Switch.State n (m+1) (BitVec w))
    (k : Fin (n+1)) (hv : p.valid k ≠ 1) :
    observe depth p s (inReady k) = BitVec.ofBool ((Switch.observe depth (decode p) s).ready k) := by
  have he : (p.valid k == 1) = false := beq_eq_false_iff_ne.mpr hv
  simp only [observe, inReady, admissible, he, Bool.not_false, Bool.true_or, Bool.and_true]

theorem accepted_destination_legal (depth : Nat) (p : Pins n m dw w)
    (s : Switch.State n (m+1) (BitVec w)) (k : Fin (n+1)) (hv : p.valid k = 1)
    (hr : observe depth p s (inReady k) = 1) : (p.destination k).toNat < m+1 := by
  by_cases h : (p.destination k).toNat < m+1
  · exact h
  · have hz := invalid_ready_low depth p s k hv (Nat.le_of_not_gt h)
    rw [hz] at hr
    contradiction

end Pinwheel.Hardware.Switch.Physical
