import Pinwheel.Hardware.Processor.CoreInterface
import Pinwheel.Hardware.Processor.RV32I.ExecuteCircuit
import Pinwheel.Hardware.RegisterFile
import Pinwheel.Hardware.Stream.Compose

/-! A serialized RV32I core assembled from existing expression and register-file
components. Phases0..6 are fetch offer, fetch reply, execute, data offer, data
reply, local fence and terminal. Phase7 holds without effects until reset.
The held instruction and architectural registers supply stable request operands.
Deferred data providers commit on response acceptance; atomic providers commit
on the request-service edge. Reset clears every physical register.
Correspondence to CoreModel is supplied in CoreCircuitProofs. -/
namespace Pinwheel.Hardware.Processor.CoreCircuit

open CoreInterface
namespace RF
export Hardware.RegisterFile (word)
end RF

abbrev controlPorts : Stream.Ports where
  size := 6
  widths := fun k => #[3,32,32,4,32,1][k]
  names := fun k => #["phase", "pc", "instruction", "fault_cause", "fault_address", "fault_word_valid"][k]
  distinct := by decide +kernel

abbrev Control := controlPorts.Signal
abbrev Register := Stream.Joint (Hardware.RegisterFile.Register 5 32) Control
def registers : Interface Register :=
  Stream.Joint.interface (Hardware.RegisterFile.registerInterface 5 32) controlPorts.interface

def phase : Register 3 := .right (.at ⟨0,by decide⟩)
def pc : Register 32 := .right (.at ⟨1,by decide⟩)
def instruction : Register 32 := .right (.at ⟨2,by decide⟩)
def faultCause : Register 4 := .right (.at ⟨3,by decide⟩)
def faultAddress : Register 32 := .right (.at ⟨4,by decide⟩)
def faultWordValid : Register 1 := .right (.at ⟨5,by decide⟩)
def word (k : Fin 31) : Register 32 := .left (Hardware.RegisterFile.word k)

abbrev E (b : Nat) := Expr Input Register b
def both (x y : E 1) : E 1 := .band x y
def either (x y : E 1) : E 1 := WordOps.wordOr x y
def gated (enabled : E 1) (value : E b) : E b := .mux enabled value (.lit 0)
def active : E 1 := .inv (.input reset)
def inPhase (p : BitVec 3) : E 1 := .equal (.reg phase) (.lit p)
def pcAligned : E 1 := .zero (.slice 0 2 (by decide) (.reg pc))

def registerWord (address : BitVec 5) : E 32 :=
  if h : address.toNat = 0 then .lit 0 else
    .reg (word ⟨address.toNat-1, by have := address.isLt; omega⟩)
def readOperand (address : E 5) : E 32 := Execution.readTree 5 registerWord address
def decoded : RV32I.DecodeCircuit.Bundle Input Register := RV32I.DecodeCircuit.bundle (.reg instruction)
def execution : RV32I.ExecuteCircuit.Bundle Input Register :=
  RV32I.ExecuteCircuit.bundle (.reg instruction) (.reg pc)
    (readOperand (decoded .rs1)) (readOperand (decoded .rs2))

def isLoad : E 1 := .equal (execution .classification) (.lit 1)
def isStore : E 1 := .equal (execution .classification) (.lit 2)
def executing : E 1 := both active (inPhase 2)
def immediateRetire : E 1 := both executing (.equal (execution .classification) (.lit 0))
def dataOffer : E 1 := both active (inPhase 3)
def dataWaiting : E 1 := both active (inPhase 4)
def atomicCompletion : E 1 := both dataOffer (both (.input dataServiceValid) (.input dataServiceAtomic))
def deferredCompletion : E 1 := both dataWaiting (.input dataResponseValid)
def dataCompletion : E 1 := either atomicCompletion deferredCompletion
def replyFault : E 2 := .mux (inPhase 3) (.input dataServiceFault) (.input dataResponseFault)
def replyData : E 32 := .mux (inPhase 3) (.input dataServiceData) (.input dataResponseData)
def dataSuccess : E 1 := both dataCompletion (.zero replyFault)
def fenceRetire : E 1 := both active (inPhase 5)
def retiring : E 1 := either immediateRetire (either dataSuccess fenceRetire)

def extendByte (value : E 32) : E 32 :=
  .concat (.mux (both (execution .signedLoad) (.slice 7 1 (by decide) value))
    (.lit (BitVec.allOnes 24)) (.lit 0)) (.slice 0 8 (by decide) value)
def extendHalf (value : E 32) : E 32 :=
  .concat (.mux (both (execution .signedLoad) (.slice 15 1 (by decide) value))
    (.lit (BitVec.allOnes 16)) (.lit 0)) (.slice 0 16 (by decide) value)
def loadedValue : E 32 :=
  .mux (.equal (execution .size) (.lit 0)) (extendByte replyData)
    (.mux (.equal (execution .size) (.lit 1)) (extendHalf replyData) replyData)
def writeEnabled : E 1 := either (both immediateRetire (execution .writeEnable))
  (both dataSuccess (both isLoad (.inv (.zero (execution .loadRd)))))
def writeRd : E 5 := gated writeEnabled (.mux immediateRetire (execution .writeRd) (execution .loadRd))
def writeData : E 32 := gated writeEnabled (.mux immediateRetire (execution .writeData) loadedValue)
def nextPC : E 32 := .mux immediateRetire (execution .nextPC) (WordOps.add (.reg pc) (.lit 4))

def fetchMisaligned : E 1 := both active (both (inPhase 0) (.inv pcAligned))
def fetchFault : E 1 := both active (both (inPhase 1)
  (both (.input fetchResponseValid) (.input fetchResponseFault)))
def executeTrap : E 1 := both executing (.equal (execution .classification) (.lit 4))
def dataTrap : E 1 := both dataCompletion (.inv (.zero replyFault))
def trapping : E 1 := either fetchMisaligned (either fetchFault (either executeTrap dataTrap))
def trapHasWord : E 1 := either executeTrap dataTrap
def newCause : E 4 :=
  .mux fetchMisaligned (.lit 0) (.mux fetchFault (.lit 1)
    (.mux executeTrap (WordOps.add (.concat (.lit (0#2)) (execution .trapCause)) (.lit 2))
      (.mux isLoad (.mux (.equal replyFault (.lit 1)) (.lit 6) (.lit 7))
        (.mux (.equal replyFault (.lit 1)) (.lit 8) (.lit 9)))))
def newFaultAddress : E 32 :=
  .mux (either fetchMisaligned fetchFault) (.reg pc)
    (.mux executeTrap (execution .trapTarget) (execution .address))

def nextPhase : E 3 :=
  .mux trapping (.lit 6) (.mux retiring (.lit 0)
    (.mux (inPhase 0) (.mux (both pcAligned (.input fetchReady)) (.lit 1) (.reg phase))
      (.mux (inPhase 1) (.mux (.input fetchResponseValid) (.lit 2) (.reg phase))
        (.mux (inPhase 2) (.mux (either isLoad isStore) (.lit 3)
          (.mux (.equal (execution .classification) (.lit 3)) (.lit 5) (.reg phase)))
          (.mux (inPhase 3) (.mux (.input dataServiceValid) (.lit 4) (.reg phase)) (.reg phase))))))

def registerInput : {b : Nat} → Hardware.RegisterFile.Input 5 32 b → E b
  | _, .at ⟨0,_⟩ => .input reset
  | _, .at ⟨1,_⟩ => writeEnabled
  | _, .at ⟨2,_⟩ => writeRd
  | _, .at ⟨3,_⟩ => writeData
  | _, .at ⟨4,_⟩ => decoded .rs1
  | _, .at ⟨5,_⟩ => decoded .rs2
  | _, .at ⟨k+6,h⟩ => False.elim (by change k+6 < 6 at h; omega)

def controlNext : {b : Nat} → Control b → E b
  | _, r => match r with
    | .at ⟨0,_⟩ => .mux (.input reset) (.lit 0) nextPhase
    | .at ⟨1,_⟩ => .mux (.input reset) (.lit 0) (.mux retiring nextPC (.reg pc))
    | .at ⟨2,_⟩ => .mux (.input reset) (.lit 0)
        (.mux (both (inPhase 1) (both (.input fetchResponseValid) (.inv (.input fetchResponseFault))))
          (.input fetchResponseData) (.reg instruction))
    | .at ⟨3,_⟩ => .mux (.input reset) (.lit 0) (.mux trapping newCause (.reg faultCause))
    | .at ⟨4,_⟩ => .mux (.input reset) (.lit 0) (.mux trapping newFaultAddress (.reg faultAddress))
    | .at ⟨5,_⟩ => .mux (.input reset) (.lit 0) (.mux trapping trapHasWord (.reg faultWordValid))
    | .at ⟨k+6,h⟩ => False.elim (by change k+6 < 6 at h; omega)

def circuit : Circuit Input Register Output where
  next r := match r with
    | .left r => ((Hardware.RegisterFile.circuit 5 32).next r).bind registerInput (fun p => .reg (.left p))
    | .right r => controlNext r
  output o := match o with
    | .at ⟨0,_⟩ => .input reset
    | .at ⟨1,_⟩ => both active (both (inPhase 0) pcAligned)
    | .at ⟨2,_⟩ => gated (both active (both (inPhase 0) pcAligned)) (.reg pc)
    | .at ⟨3,_⟩ => both active (inPhase 1)
    | .at ⟨4,_⟩ => dataOffer
    | .at ⟨5,_⟩ => both dataOffer isStore
    | .at ⟨6,_⟩ => gated dataOffer (execution .address)
    | .at ⟨7,_⟩ => gated dataOffer (execution .size)
    | .at ⟨8,_⟩ => both dataOffer (execution .signedLoad)
    | .at ⟨9,_⟩ => gated dataOffer (execution .storeData)
    | .at ⟨10,_⟩ => dataWaiting
    | .at ⟨11,_⟩ => retiring
    | .at ⟨12,_⟩ => gated retiring (.reg pc)
    | .at ⟨13,_⟩ => gated retiring (.reg instruction)
    | .at ⟨14,_⟩ => gated retiring nextPC
    | .at ⟨15,_⟩ => writeEnabled
    | .at ⟨16,_⟩ => writeRd
    | .at ⟨17,_⟩ => writeData
    | .at ⟨18,_⟩ => trapping
    | .at ⟨19,_⟩ => gated trapping (.reg pc)
    | .at ⟨20,_⟩ => trapHasWord
    | .at ⟨21,_⟩ => gated trapHasWord (.reg instruction)
    | .at ⟨22,_⟩ => gated trapping newCause
    | .at ⟨23,_⟩ => gated trapping newFaultAddress
    | .at ⟨24,_⟩ => both active (inPhase 6)
    | .at ⟨25,_⟩ => gated (both active (inPhase 6)) (.reg pc)
    | .at ⟨26,_⟩ => both active (both (inPhase 6) (.reg faultWordValid))
    | .at ⟨27,_⟩ => gated (both active (both (inPhase 6) (.reg faultWordValid))) (.reg instruction)
    | .at ⟨28,_⟩ => gated (both active (inPhase 6)) (.reg faultCause)
    | .at ⟨29,_⟩ => gated (both active (inPhase 6)) (.reg faultAddress)
    | .at ⟨k+30,h⟩ => False.elim (by change k+30 < 30 at h; omega)

end Pinwheel.Hardware.Processor.CoreCircuit
