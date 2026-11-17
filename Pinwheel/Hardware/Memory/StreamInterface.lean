import Pinwheel.Hardware.Memory.StreamModel
import Pinwheel.Hardware.Stream.Ports

/-! Raw physical request/response pins. A valid request selects either a read or
a full-word write. Read data bits and all fields of an invalid request are
ignored. Address and data widths may be zero in the semantics; HDL exporters
may require positive widths. There is no invalid binary address code.
-/
namespace Pinwheel.Hardware.Memory.StreamInterface

abbrev inputPorts (a w : Nat) : Hardware.Stream.Ports where
  size := 6
  widths := fun k => if k.val = 3 then a else if k.val = 4 then w else 1
  names := fun k => #["reset", "req_valid", "req_write", "req_address", "req_data", "resp_ready"][k]
  distinct := by decide +kernel

abbrev outputPorts (w : Nat) : Hardware.Stream.Ports where
  size := 3
  widths := fun k => if k.val = 2 then w else 1
  names := fun k => #["req_ready", "resp_valid", "resp_data"][k]
  distinct := by decide +kernel

abbrev Input (a w : Nat) := (inputPorts a w).Signal
abbrev Output (w : Nat) := (outputPorts w).Signal

def reset : Input a w 1 := .at ⟨0, by simp⟩
def valid : Input a w 1 := .at ⟨1, by simp⟩
def write : Input a w 1 := .at ⟨2, by simp⟩
def address : Input a w a := .at ⟨3, by simp⟩
def data : Input a w w := .at ⟨4, by simp⟩
def ready : Input a w 1 := .at ⟨5, by simp⟩

def inReady : Output w 1 := .at ⟨0, by simp⟩
def outValid : Output w 1 := .at ⟨1, by simp⟩
def outData : Output w w := .at ⟨2, by simp⟩

def inputs (a w : Nat) : Interface (Input a w) := (inputPorts a w).interface
def outputs (w : Nat) : Interface (Output w) := (outputPorts w).interface

structure Pins (a w : Nat) where
  reset : BitVec 1
  valid : BitVec 1
  write : BitVec 1
  address : BitVec a
  data : BitVec w
  ready : BitVec 1

def Pins.values (p : Pins a w) : Values (Input a w)
  | _, .at ⟨0, _⟩ => p.reset
  | _, .at ⟨1, _⟩ => p.valid
  | _, .at ⟨2, _⟩ => p.write
  | _, .at ⟨3, _⟩ => p.address
  | _, .at ⟨4, _⟩ => p.data
  | _, .at ⟨5, _⟩ => p.ready
  | _, .at ⟨k+6, h⟩ => False.elim (by change k+6 < 6 at h; omega)

def readPins (i : Values (Input a w)) : Pins a w :=
  ⟨i reset, i valid, i write, i address, i data, i ready⟩

theorem readPins_values (p : Pins a w) : readPins p.values = p := by
  cases p
  rfl

theorem values_readPins (i : Values (Input a w)) (p : Input a w b) :
    (readPins i).values p = i p := by
  cases p with
  | «at» k =>
    match k with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ => rfl
    | ⟨k+6, h⟩ => exact False.elim (by change k+6 < 6 at h; omega)

def decode (i : Values (Input a w)) : StreamModel.Input a w :=
  ⟨i reset == 1,
    if i valid = 1 then
      some (if i write = 1 then .write (i address) (i data) else .read (i address))
    else none,
    i ready == 1⟩

def encodeInput (i : StreamModel.Input a w) : Values (Input a w) :=
  Pins.values ⟨BitVec.ofBool i.reset, BitVec.ofBool i.offered.isSome,
    match i.offered with | some (.write _ _) => 1 | _ => 0,
    match i.offered with | some (.read a) | some (.write a _) => a | _ => 0,
    match i.offered with | some (.write _ d) => d | _ => 0,
    BitVec.ofBool i.ready⟩

theorem decode_encode (i : StreamModel.Input a w) : decode (encodeInput i) = i := by
  cases i with
  | mk rst offered rdy =>
    cases rst <;> cases rdy <;> cases offered
    all_goals simp [decode, encodeInput, Pins.values, reset, valid, write, address, data, ready]
    all_goals rename_i request; cases request <;> rfl

def outputValues (o : StreamModel.Output w) : Values (Output w)
  | _, .at ⟨0, _⟩ => BitVec.ofBool o.ready
  | _, .at ⟨1, _⟩ => BitVec.ofBool o.offered.isSome
  | _, .at ⟨2, _⟩ => o.offered.getD 0
  | _, .at ⟨k+3, h⟩ => False.elim (by change k+3 < 3 at h; omega)

def spec (a w : Nat) : Timed.Component (Values (Input a w)) (StreamModel.State a w) (Values (Output w)) where
  step i s := StreamModel.step (decode i) s
  observe i s := outputValues ((StreamModel.component a w).observe (decode i) s)

end Pinwheel.Hardware.Memory.StreamInterface
