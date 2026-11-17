import Pinwheel.Hardware.Memory.ByteAdapterModel
import Pinwheel.Hardware.Stream.Ports

/-! Word address and byte offset are separate. Response codes are read=00,
stored=01, reserved-size=10, misaligned=11. Invalid response code/data are zero.
-/
namespace Pinwheel.Hardware.Memory.ByteAdapterInterface

abbrev inputPorts (a : Nat) : Hardware.Stream.Ports where
  size := 9
  widths := fun k => if k.val = 4 ∨ k.val = 6 then 2 else if k.val = 5 then a else if k.val = 7 then 32 else 1
  names := fun k => #["reset", "request_valid", "write", "signed", "size", "address", "offset", "data", "response_ready"][k]
  distinct := by decide +kernel

abbrev outputPorts : Hardware.Stream.Ports where
  size := 4
  widths := fun k => if k.val = 2 then 2 else if k.val = 3 then 32 else 1
  names := fun k => #["request_ready", "response_valid", "response_code", "response_data"][k]
  distinct := by decide +kernel

abbrev Input (a : Nat) := (inputPorts a).Signal
abbrev Output := outputPorts.Signal

def reset : Input a 1 := .at ⟨0, by simp⟩
def requestValid : Input a 1 := .at ⟨1, by simp⟩
def write : Input a 1 := .at ⟨2, by simp⟩
def signed : Input a 1 := .at ⟨3, by simp⟩
def size : Input a 2 := .at ⟨4, by simp⟩
def address : Input a a := .at ⟨5, by simp⟩
def offset : Input a 2 := .at ⟨6, by simp⟩
def data : Input a 32 := .at ⟨7, by simp⟩
def responseReady : Input a 1 := .at ⟨8, by simp⟩

def requestReady : Output 1 := .at ⟨0, by simp⟩
def responseValid : Output 1 := .at ⟨1, by simp⟩
def responseCode : Output 2 := .at ⟨2, by simp⟩
def responseData : Output 32 := .at ⟨3, by simp⟩

def inputs (a : Nat) : Interface (Input a) := (inputPorts a).interface
def outputs : Interface Output := outputPorts.interface

def request (write signed : BitVec 1) (size : BitVec 2) (address : BitVec a)
    (offset : BitVec 2) (data : BitVec 32) : ByteAdapterModel.Request a :=
  if write = 1 then .store size address offset data else .read (signed == 1) size address offset

def decode (i : Values (Input a)) : ByteAdapterModel.Input a :=
  ⟨i reset == 1, if i requestValid = 1 then
    some (request (i write) (i signed) (i size) (i address) (i offset) (i data)) else none,
    i responseReady == 1⟩

def code : ByteAdapterModel.Response → BitVec 2
  | .read _ => 0
  | .stored => 1
  | .fault .reservedSize => 2
  | .fault .misaligned => 3

def payload : ByteAdapterModel.Response → BitVec 32
  | .read value => value
  | _ => 0

def outputValues (o : ByteAdapterModel.Output) : Values Output
  | _, .at ⟨0, _⟩ => BitVec.ofBool o.ready
  | _, .at ⟨1, _⟩ => BitVec.ofBool o.offered.isSome
  | _, .at ⟨2, _⟩ => (o.offered.map code).getD 0
  | _, .at ⟨3, _⟩ => (o.offered.map payload).getD 0
  | _, .at ⟨k+4, h⟩ => False.elim (by change k+4 < 4 at h; omega)

def spec (a : Nat) : Timed.Component (Values (Input a)) (ByteAdapterModel.State a) (Values Output) where
  step i s := ByteAdapterModel.step (decode i) s
  observe i s := outputValues ((ByteAdapterModel.component a).observe (decode i) s)

end Pinwheel.Hardware.Memory.ByteAdapterInterface
