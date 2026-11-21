import Pinwheel.Hardware.Stream.BufferedMerge.Model
import Pinwheel.Hardware.Stream.Compose

namespace Pinwheel.Hardware.Stream.BufferedMerge.Physical

set_option backward.isDefEq.respectTransparency false

def lanePorts (width count : Nat) : Stream.Ports where
  size := count
  widths := fun _ => width
  names := fun k => "lane_" ++ Nat.repr k.val
  distinct := by
    intro a b h
    simp only [String.append_right_inj] at h
    exact Fin.ext (Nat.repr_injective h)

abbrev Lane (width count : Nat) := (lanePorts width count).Signal

/-- Enumeration: reset, downstream ready, all valids, all payloads. -/
abbrev In (n w : Nat) := Joint (Lane 1 2) (Joint (Lane 1 (n+1)) (Lane w (n+1)))
/-- Enumeration: all input readies, output valid, output payload. -/
abbrev Out (n w : Nat) := Joint (Lane 1 (n+1)) (Joint (Lane 1 1) (Lane w 1))

def indexedInterface (d : Hardware.Interface P) (stem : String) : Hardware.Interface P :=
  d.rename (fun p => stem ++ Nat.repr (d.position p).val) (by
    intro a b h
    simp only [Hardware.Interface.position_signal, String.append_right_inj] at h
    exact Fin.ext (Nat.repr_injective h))

def inputInterface (n w : Nat) : Hardware.Interface (In n w) :=
  indexedInterface (Joint.interface (lanePorts 1 2).interface
    (Joint.interface (lanePorts 1 (n+1)).interface (lanePorts w (n+1)).interface)) "in_"

def outputInterface (n w : Nat) : Hardware.Interface (Out n w) :=
  indexedInterface (Joint.interface (lanePorts 1 (n+1)).interface
    (Joint.interface (lanePorts 1 1).interface (lanePorts w 1).interface)) "out_"

def reset : In n w 1 := .left (.at ⟨0, by decide⟩)
def outReady : In n w 1 := .left (.at ⟨1, by decide⟩)
def inValid (k : Fin (n+1)) : In n w 1 := .right (.left (.at k))
def inPayload (k : Fin (n+1)) : In n w w := .right (.right (.at k))
def inReady (k : Fin (n+1)) : Out n w 1 := .left (.at k)
def outValid : Out n w 1 := .right (.left (.at ⟨0, by decide⟩))
def outPayload : Out n w w := .right (.right (.at ⟨0, by change 0 < 1; decide⟩))

structure Pins (n w : Nat) where
  reset : BitVec 1
  ready : BitVec 1
  valid : Fin (n+1) → BitVec 1
  payload : Fin (n+1) → BitVec w

def Pins.values (p : Pins n w) : Values (In n w)
  | _, .left (.at k) => if k.val = 0 then p.reset else p.ready
  | _, .right (.left (.at k)) => p.valid k
  | _, .right (.right (.at k)) => p.payload k

def readPins (i : Values (In n w)) : Pins n w :=
  ⟨i reset, i outReady, fun k => i (inValid k), fun k => i (inPayload k)⟩

theorem readPins_values (p : Pins n w) : readPins p.values = p := by
  cases p
  rfl

def decode (p : Pins n w) : BufferedMerge.Input n (BitVec w) :=
  ⟨p.reset == 1, fun k => if p.valid k = 1 then some (p.payload k) else none,
    fun _ => p.ready == 1⟩

def encodeInput (i : BufferedMerge.Input n (BitVec w)) : Pins n w :=
  ⟨BitVec.ofBool i.reset, BitVec.ofBool (i.ready 0),
    fun k => BitVec.ofBool (i.offered k).isSome, fun k => (i.offered k).getD 0⟩

private theorem bool_roundtrip (b : Bool) : (BitVec.ofBool b == 1) = b := by
  cases b <;> rfl

theorem decode_encode (i : BufferedMerge.Input n (BitVec w)) : decode (encodeInput i) = i := by
  cases i with
  | mk reset offered ready =>
    simp only [decode, encodeInput, bool_roundtrip]
    congr 1
    · funext k
      cases offered k <;> simp
    · funext k
      have hk : k = 0 := Fin.ext (by omega)
      subst k
      rfl

def outputValues (o : BufferedMerge.Output n (BitVec w)) : Values (Out n w)
  | _, .left (.at k) => BitVec.ofBool (o.ready k)
  | _, .right (.left (.at _)) => BitVec.ofBool (o.offered 0).isSome
  | _, .right (.right (.at _)) => ((o.offered 0).map Delivery.payload).getD 0

/-- Arbitrary raw input payloads are ignored when their valid bit is low.
Source provenance remains logical and is erased only in output/register encodings. -/
def component (n w : Nat) :
    Timed.Component (Values (In n w)) (State n (BitVec w)) (Values (Out n w)) :=
  ⟨fun i s => BufferedMerge.step (decode (readPins i)) s,
    fun i s => outputValues (BufferedMerge.observe (decode (readPins i)) s)⟩

end Pinwheel.Hardware.Stream.BufferedMerge.Physical
