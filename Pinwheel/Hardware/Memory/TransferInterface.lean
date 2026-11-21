import Pinwheel.Hardware.Memory.TransferModel
import Pinwheel.Hardware.Stream.Ports

/-! Complete physical interface for the open transfer controller. Command
lengths retain their extra capacity bit. `memory_reset` forwards external reset
on valid control states and also supports safe reserved-phase recovery. All
other inactive physical outputs use zero-valued payload/address bits.
-/
namespace Pinwheel.Hardware.Memory.TransferInterface

abbrev inputPorts (a wi : Nat) : Hardware.Stream.Ports where
  size := 9
  widths := fun k => if k.val = 2 ∨ k.val = 3 then a
    else if k.val = 4 then a+1 else if k.val = 7 then wi else 1
  names := fun k => #["reset", "start_valid", "source_base", "destination_base", "length",
    "source_request_ready", "source_response_valid", "source_response_data", "destination_request_ready"][k]
  distinct := by decide +kernel

abbrev outputPorts (a wo : Nat) : Hardware.Stream.Ports where
  size := 11
  widths := fun k => if k.val = 5 ∨ k.val = 8 then a else if k.val = 9 then wo else 1
  names := fun k => #["start_ready", "busy", "done", "error", "source_request_valid", "source_request_address",
    "source_response_ready", "destination_request_valid", "destination_request_address", "destination_request_data",
    "memory_reset"][k]
  distinct := by decide +kernel

abbrev Input (a wi : Nat) := (inputPorts a wi).Signal
abbrev Output (a wo : Nat) := (outputPorts a wo).Signal

def reset : Input a wi 1 := .at ⟨0, by simp⟩
def startValid : Input a wi 1 := .at ⟨1, by simp⟩
def sourceBase : Input a wi a := .at ⟨2, by simp⟩
def destinationBase : Input a wi a := .at ⟨3, by simp⟩
def length : Input a wi (a+1) := .at ⟨4, by simp⟩
def sourceRequestReady : Input a wi 1 := .at ⟨5, by simp⟩
def sourceResponseValid : Input a wi 1 := .at ⟨6, by simp⟩
def sourceResponseData : Input a wi wi := .at ⟨7, by simp⟩
def destinationRequestReady : Input a wi 1 := .at ⟨8, by simp⟩

def startReady : Output a wo 1 := .at ⟨0, by simp⟩
def busy : Output a wo 1 := .at ⟨1, by simp⟩
def done : Output a wo 1 := .at ⟨2, by simp⟩
def error : Output a wo 1 := .at ⟨3, by simp⟩
def sourceRequestValid : Output a wo 1 := .at ⟨4, by simp⟩
def sourceRequestAddress : Output a wo a := .at ⟨5, by simp⟩
def sourceResponseReady : Output a wo 1 := .at ⟨6, by simp⟩
def destinationRequestValid : Output a wo 1 := .at ⟨7, by simp⟩
def destinationRequestAddress : Output a wo a := .at ⟨8, by simp⟩
def destinationRequestData : Output a wo wo := .at ⟨9, by simp⟩
def memoryReset : Output a wo 1 := .at ⟨10, by simp⟩

def inputs (a wi : Nat) : Interface (Input a wi) := (inputPorts a wi).interface
def outputs (a wo : Nat) : Interface (Output a wo) := (outputPorts a wo).interface

structure Pins (a wi : Nat) where
  reset : BitVec 1
  startValid : BitVec 1
  sourceBase : BitVec a
  destinationBase : BitVec a
  length : BitVec (a+1)
  sourceRequestReady : BitVec 1
  sourceResponseValid : BitVec 1
  sourceResponseData : BitVec wi
  destinationRequestReady : BitVec 1

def Pins.values (p : Pins a wi) : Values (Input a wi)
  | _, .at ⟨0, _⟩ => p.reset
  | _, .at ⟨1, _⟩ => p.startValid
  | _, .at ⟨2, _⟩ => p.sourceBase
  | _, .at ⟨3, _⟩ => p.destinationBase
  | _, .at ⟨4, _⟩ => p.length
  | _, .at ⟨5, _⟩ => p.sourceRequestReady
  | _, .at ⟨6, _⟩ => p.sourceResponseValid
  | _, .at ⟨7, _⟩ => p.sourceResponseData
  | _, .at ⟨8, _⟩ => p.destinationRequestReady
  | _, .at ⟨k+9, h⟩ => False.elim (by change k+9 < 9 at h; omega)

def readPins (i : Values (Input a wi)) : Pins a wi :=
  ⟨i reset, i startValid, i sourceBase, i destinationBase, i length,
    i sourceRequestReady, i sourceResponseValid, i sourceResponseData, i destinationRequestReady⟩

def decode (i : Values (Input a wi)) : TransferModel.Input a wi :=
  ⟨i reset == 1,
    if i startValid = 1 then some ⟨i sourceBase, i destinationBase, i length⟩ else none,
    i sourceRequestReady == 1,
    if i sourceResponseValid = 1 then some (i sourceResponseData) else none,
    i destinationRequestReady == 1⟩

def outputValues (reset : Bool) (o : TransferModel.Output a wo) : Values (Output a wo)
  | _, .at ⟨0, _⟩ => BitVec.ofBool o.startReady
  | _, .at ⟨1, _⟩ => BitVec.ofBool o.busy
  | _, .at ⟨2, _⟩ => BitVec.ofBool o.done
  | _, .at ⟨3, _⟩ => BitVec.ofBool o.error
  | _, .at ⟨4, _⟩ => BitVec.ofBool o.sourceRead.isSome
  | _, .at ⟨5, _⟩ => o.sourceRead.getD 0
  | _, .at ⟨6, _⟩ => BitVec.ofBool o.sourceResponseReady
  | _, .at ⟨7, _⟩ => BitVec.ofBool o.destinationWrite.isSome
  | _, .at ⟨8, _⟩ => (o.destinationWrite.map Prod.fst).getD 0
  | _, .at ⟨9, _⟩ => (o.destinationWrite.map Prod.snd).getD 0
  | _, .at ⟨10, _⟩ => BitVec.ofBool reset
  | _, .at ⟨k+11, h⟩ => False.elim (by change k+11 < 11 at h; omega)

def spec (m : Hardware.Stream.Map wi wo) :
    Timed.Component (Values (Input a wi)) (TransferModel.Control a) (Values (Output a wo)) where
  step i s := TransferModel.step (decode i) s
  observe i s := outputValues (decode i).reset (TransferModel.observe m (decode i) s)

end Pinwheel.Hardware.Memory.TransferInterface
