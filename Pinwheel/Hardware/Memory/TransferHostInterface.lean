import Pinwheel.Hardware.Memory.TransferHostModel
import Pinwheel.Hardware.Memory.StreamInterface

/-! Complete host-facing interface for a loader, transfer controller, and two
independent memories. Requests and responses are sampled at the same edge.
Command length retains the capacity bit. Inactive response payloads are zero.
-/
namespace Pinwheel.Hardware.Memory.TransferHostInterface

abbrev inputPorts (a wi wo : Nat) : Hardware.Stream.Ports where
  size := 15
  widths := fun k => if k.val = 2 ∨ k.val = 3 ∨ k.val = 7 ∨ k.val = 12 then a
    else if k.val = 4 then a+1 else if k.val = 8 then wi else if k.val = 13 then wo else 1
  names := fun k => #["reset", "start_valid", "source_base", "destination_base", "length",
    "source_req_valid", "source_req_write", "source_req_address", "source_req_data", "source_resp_ready",
    "destination_req_valid", "destination_req_write", "destination_req_address", "destination_req_data",
    "destination_resp_ready"][k]
  distinct := by decide +kernel

abbrev outputPorts (wi wo : Nat) : Hardware.Stream.Ports where
  size := 10
  widths := fun k => if k.val = 6 then wi else if k.val = 9 then wo else 1
  names := fun k => #["start_ready", "busy", "done", "error", "source_req_ready", "source_resp_valid",
    "source_resp_data", "destination_req_ready", "destination_resp_valid", "destination_resp_data"][k]
  distinct := by decide +kernel

abbrev Input (a wi wo : Nat) := (inputPorts a wi wo).Signal
abbrev Output (wi wo : Nat) := (outputPorts wi wo).Signal

def reset : Input a wi wo 1 := .at ⟨0, by simp⟩
def startValid : Input a wi wo 1 := .at ⟨1, by simp⟩
def sourceBase : Input a wi wo a := .at ⟨2, by simp⟩
def destinationBase : Input a wi wo a := .at ⟨3, by simp⟩
def length : Input a wi wo (a+1) := .at ⟨4, by simp⟩
def sourceValid : Input a wi wo 1 := .at ⟨5, by simp⟩
def sourceWrite : Input a wi wo 1 := .at ⟨6, by simp⟩
def sourceAddress : Input a wi wo a := .at ⟨7, by simp⟩
def sourceData : Input a wi wo wi := .at ⟨8, by simp⟩
def sourceReady : Input a wi wo 1 := .at ⟨9, by simp⟩
def destinationValid : Input a wi wo 1 := .at ⟨10, by simp⟩
def destinationWrite : Input a wi wo 1 := .at ⟨11, by simp⟩
def destinationAddress : Input a wi wo a := .at ⟨12, by simp⟩
def destinationData : Input a wi wo wo := .at ⟨13, by simp⟩
def destinationReady : Input a wi wo 1 := .at ⟨14, by simp⟩

def startReady : Output wi wo 1 := .at ⟨0, by simp⟩
def busy : Output wi wo 1 := .at ⟨1, by simp⟩
def done : Output wi wo 1 := .at ⟨2, by simp⟩
def error : Output wi wo 1 := .at ⟨3, by simp⟩
def sourceRequestReady : Output wi wo 1 := .at ⟨4, by simp⟩
def sourceResponseValid : Output wi wo 1 := .at ⟨5, by simp⟩
def sourceResponseData : Output wi wo wi := .at ⟨6, by simp⟩
def destinationRequestReady : Output wi wo 1 := .at ⟨7, by simp⟩
def destinationResponseValid : Output wi wo 1 := .at ⟨8, by simp⟩
def destinationResponseData : Output wi wo wo := .at ⟨9, by simp⟩

def inputs (a wi wo : Nat) : Interface (Input a wi wo) := (inputPorts a wi wo).interface
def outputs (wi wo : Nat) : Interface (Output wi wo) := (outputPorts wi wo).interface

def sourceHostPins (i : Values (Input a wi wo)) : Values (StreamInterface.Input a wi) :=
  StreamInterface.Pins.values ⟨i reset, i sourceValid, i sourceWrite, i sourceAddress, i sourceData, i sourceReady⟩

def destinationHostPins (i : Values (Input a wi wo)) : Values (StreamInterface.Input a wo) :=
  StreamInterface.Pins.values
    ⟨i reset, i destinationValid, i destinationWrite, i destinationAddress, i destinationData, i destinationReady⟩

def decode (i : Values (Input a wi wo)) : TransferHostModel.Input a wi wo :=
  ⟨i reset == 1,
    if i startValid = 1 then some ⟨i sourceBase, i destinationBase, i length⟩ else none,
    (StreamInterface.decode (sourceHostPins i)).offered, i sourceReady == 1,
    (StreamInterface.decode (destinationHostPins i)).offered, i destinationReady == 1⟩

def outputValues (o : TransferHostModel.Output wi wo) : Values (Output wi wo)
  | _, .at ⟨0, _⟩ => BitVec.ofBool o.startReady
  | _, .at ⟨1, _⟩ => BitVec.ofBool o.busy
  | _, .at ⟨2, _⟩ => BitVec.ofBool o.done
  | _, .at ⟨3, _⟩ => BitVec.ofBool o.error
  | _, .at ⟨4, _⟩ => BitVec.ofBool o.source.ready
  | _, .at ⟨5, _⟩ => BitVec.ofBool o.source.offered.isSome
  | _, .at ⟨6, _⟩ => o.source.offered.getD 0
  | _, .at ⟨7, _⟩ => BitVec.ofBool o.destination.ready
  | _, .at ⟨8, _⟩ => BitVec.ofBool o.destination.offered.isSome
  | _, .at ⟨9, _⟩ => o.destination.offered.getD 0
  | _, .at ⟨k+10, h⟩ => False.elim (by change k+10 < 10 at h; omega)

def spec (m : Hardware.Stream.Map wi wo) :
    Timed.Component (Values (Input a wi wo)) (TransferModel.State a wi wo) (Values (Output wi wo)) where
  step i s := TransferHostModel.step m (decode i) s
  observe i s := outputValues (TransferHostModel.observe (decode i) s)

end Pinwheel.Hardware.Memory.TransferHostInterface
