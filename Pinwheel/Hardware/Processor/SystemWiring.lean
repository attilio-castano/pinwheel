import Pinwheel.Hardware.Processor.SystemInterface
import Pinwheel.Hardware.Processor.AddressDecode
import Pinwheel.Hardware.Memory.ByteAdapterCircuit

/-! Bus wiring parameterized by typed component outputs. This common owner is
instantiated both by full expression substitution and by hierarchical export. -/
namespace Pinwheel.Hardware.Processor.SystemWiring

open SystemInterface

structure Network (I R : Nat → Type) where
  pins : {b : Nat} → Input b → Expr I R b
  coreOutputs : {b : Nat} → CoreInterface.Output b → Expr I R b
  ramOutputs : {b : Nat} → Memory.ByteAdapterInterface.Output b → Expr I R b
  mmioOutputs : {b : Nat} → MmioInterface.Output b → Expr I R b
  fetchValues : {b : Nat} → Fetch b → Expr I R b

def both (a b : Expr I R 1) : Expr I R 1 := .band a b
def either (a b : Expr I R 1) : Expr I R 1 := WordOps.wordOr a b

variable (n : Network I R) (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

def route : Expr I R 3 :=
  AddressDecode.runtime layout (.mux (n.coreOutputs CoreInterface.dataWrite) (.lit 2) (.lit 1))
    (n.coreOutputs CoreInterface.dataSize) (n.coreOutputs CoreInterface.dataAddress)
def region (code : BitVec 3) : Expr I R 1 := .equal (route n layout) (.lit code)
def peripheral : Expr I R 1 := either (region n layout 2) (either (region n layout 3) (region n layout 4))

def localAddress (base : BitVec 32) : Expr I R 32 := .sub (n.coreOutputs CoreInterface.dataAddress) (.lit base)
def ramInput : {b : Nat} → Memory.ByteAdapterInterface.Input aw b → Expr I R b
  | _, .at ⟨0,_⟩ => n.pins reset
  | _, .at ⟨1,_⟩ => both (n.coreOutputs CoreInterface.dataValid) (region n layout 1)
  | _, .at ⟨2,_⟩ => n.coreOutputs CoreInterface.dataWrite
  | _, .at ⟨3,_⟩ => n.coreOutputs CoreInterface.dataSigned
  | _, .at ⟨4,_⟩ => n.coreOutputs CoreInterface.dataSize
  | _, .at ⟨5,_⟩ => .slice 2 aw (Nat.add_le_add_left ramFits 2) (localAddress n layout.config.ramBase)
  | _, .at ⟨6,_⟩ => .slice 0 2 (by decide) (n.coreOutputs CoreInterface.dataAddress)
  | _, .at ⟨7,_⟩ => n.coreOutputs CoreInterface.dataStoreData
  | _, .at ⟨8,_⟩ => n.coreOutputs CoreInterface.dataResponseReady
  | _, .at ⟨k+9,h⟩ => False.elim (by change k+9 < 9 at h; omega)
def peripheralBase : Expr I R 32 :=
  .mux (region n layout 2) (.lit layout.config.gpioBase)
    (.mux (region n layout 3) (.lit layout.config.timerBase) (.lit layout.config.uartBase))
def mmioInput : {b : Nat} → MmioInterface.Input b → Expr I R b
  | _, .at ⟨0,_⟩ => n.pins reset
  | _, .at ⟨1,_⟩ => both (n.coreOutputs CoreInterface.dataValid) (peripheral n layout)
  | _, .at ⟨2,_⟩ => .mux (region n layout 2) (.lit 0) (.mux (region n layout 3) (.lit 1) (.lit 2))
  | _, .at ⟨3,_⟩ => n.coreOutputs CoreInterface.dataWrite
  | _, .at ⟨4,_⟩ => .slice 2 6 (by decide) (.sub (n.coreOutputs CoreInterface.dataAddress) (peripheralBase n layout))
  | _, .at ⟨5,_⟩ => n.coreOutputs CoreInterface.dataStoreData
  | _, .at ⟨6,_⟩ => n.pins gpioInput
  | _, .at ⟨7,_⟩ => n.pins txComplete
  | _, .at ⟨8,_⟩ => n.pins rxValid
  | _, .at ⟨9,_⟩ => n.pins rxData
  | _, .at ⟨10,_⟩ => n.pins framingError
  | _, .at ⟨k+11,h⟩ => False.elim (by change k+11 < 11 at h; omega)
def romData : Expr I R 32 :=
  Execution.readTree rw (fun a => .lit (rom a))
    (.slice 2 rw (Nat.add_le_add_left romFits 2) (n.coreOutputs CoreInterface.dataAddress))
def romLoad : Expr I R 32 := Memory.ByteAdapterCircuit.loadExpr (n.coreOutputs CoreInterface.dataSize)
  (.slice 0 2 (by decide) (n.coreOutputs CoreInterface.dataAddress)) (n.coreOutputs CoreInterface.dataSigned) (romData n rom romFits)
def serviceFault : Expr I R 2 :=
  .mux (peripheral n layout)
    (.mux (.ult (n.mmioOutputs MmioInterface.responseCode) (.lit 2)) (.lit 0) (.lit 2))
    (.mux (region n layout 0) (.lit 0) (.mux (region n layout 5) (.lit 1) (.lit 2)))
def responseFault : Expr I R 2 :=
  .mux (.equal (n.ramOutputs Memory.ByteAdapterInterface.responseCode) (.lit 3)) (.lit 1)
    (.mux (.equal (n.ramOutputs Memory.ByteAdapterInterface.responseCode) (.lit 2)) (.lit 2) (.lit 0))

def coreInput : {b : Nat} → CoreInterface.Input b → Expr I R b
  | _, .at ⟨0,_⟩ => n.pins reset
  | _, .at ⟨1,_⟩ => .lit 1
  | _, .at ⟨2,_⟩ => n.fetchValues (.at ⟨0,by decide⟩)
  | _, .at ⟨3,_⟩ => n.fetchValues (.at ⟨1,by decide⟩)
  | _, .at ⟨4,_⟩ => n.fetchValues (.at ⟨2,by decide⟩)
  | _, .at ⟨5,_⟩ => both (n.coreOutputs CoreInterface.dataValid)
      (.mux (region n layout 1) (n.ramOutputs Memory.ByteAdapterInterface.requestReady) (.lit 1))
  | _, .at ⟨6,_⟩ => .inv (region n layout 1)
  | _, .at ⟨7,_⟩ => serviceFault n layout
  | _, .at ⟨8,_⟩ => .mux (region n layout 0) (romLoad n rom romFits) (n.mmioOutputs MmioInterface.responseData)
  | _, .at ⟨9,_⟩ => n.ramOutputs Memory.ByteAdapterInterface.responseValid
  | _, .at ⟨10,_⟩ => responseFault n
  | _, .at ⟨11,_⟩ => n.ramOutputs Memory.ByteAdapterInterface.responseData
  | _, .at ⟨k+12,h⟩ => False.elim (by change k+12 < 12 at h; omega)

def fetchRoute : Expr I R 3 := AddressDecode.result layout .fetch .word (n.coreOutputs CoreInterface.fetchAddress)
def fetchNext : {b : Nat} → Fetch b → Expr I R b
  | _, .at ⟨0,_⟩ => both (.inv (n.pins reset)) (n.coreOutputs CoreInterface.fetchValid)
  | _, .at ⟨1,_⟩ => .mux (n.pins reset) (.lit 0)
      (.mux (n.coreOutputs CoreInterface.fetchValid) (.inv (.equal (fetchRoute n layout) (.lit 0))) (n.fetchValues (.at ⟨1,by decide⟩)))
  | _, .at ⟨2,_⟩ => .mux (n.pins reset) (.lit 0)
      (.mux (n.coreOutputs CoreInterface.fetchValid)
        (.mux (.equal (fetchRoute n layout) (.lit 0))
          (Execution.readTree rw (fun a => .lit (rom a))
            (.slice 2 rw (Nat.add_le_add_left romFits 2) (n.coreOutputs CoreInterface.fetchAddress))) (.lit 0)) (n.fetchValues (.at ⟨2,by decide⟩)))
  | _, .at ⟨k+3,h⟩ => False.elim (by change k+3 < 3 at h; omega)

end Pinwheel.Hardware.Processor.SystemWiring
