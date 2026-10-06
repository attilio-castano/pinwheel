import Pinwheel.Compile.I2CReadTransaction
import Pinwheel.Compile.SPITransaction
import Lean.Data.Json

/-! Production request-to-program export. Bounds are checked before constructing
finite compiler operands. Protocol models, compilers and the execution encoding
are reused unchanged; this module does not generate or alter circuit source. -/
namespace Pinwheel.Program.Export
open Lean

def requestSchema : String := "pinwheel-protocol-request-v1"
def responseSchema : String := "pinwheel-compiled-program-v1"

private def requireKeys (request : Json) (expected : List String) : Except String Unit := do
  let object ← request.getObj?
  let keys := object.toList.map Prod.fst
  unless keys.length == expected.length && expected.all (keys.contains ·) do
    throw s!"Request must contain exactly: {String.intercalate ", " expected}"

private def bounded (value : Json) (name : String) (minimum maximum : Nat) :
    Except String {n : Nat // minimum ≤ n ∧ n ≤ maximum} := do
  let n ← value.getNat?.mapError (fun _ => s!"{name} must be an unsigned integer")
  if h : minimum ≤ n ∧ n ≤ maximum then return ⟨n, h⟩
  else throw s!"{name} must be in {minimum}..{maximum}"

private def field (request : Json) (name : String) (minimum maximum : Nat) :
    Except String {n : Nat // minimum ≤ n ∧ n ≤ maximum} := do
  bounded (← request.getObjVal? name) name minimum maximum

private def readProgram (request : Json) : Except String Hardware.Execution.Image := do
  requireKeys request ["schema", "protocol", "address", "register", "byte_count", "phase_cycles", "wait_cycles"]
  let address ← field request "address" 0 127
  let register ← field request "register" 0 255
  let count ← field request "byte_count" 1 2
  let phase ← field request "phase_cycles" 1 256
  let wait ← field request "wait_cycles" 1 256
  let cfg : I2C.Config := ⟨⟨phase.val - 1, by have := phase.property; omega⟩,
    ⟨wait.val - 1, by have := wait.property; omega⟩⟩
  let transaction : I2C.RegisterReadTransaction.Request :=
    ⟨⟨address.val, by have := address.property; omega⟩, BitVec.ofNat 8 register.val,
      ⟨count.val - 1, by have := count.property; omega⟩⟩
  return Compile.I2CReadTransaction.program cfg transaction

private def spiProgram (request : Json) : Except String Hardware.Execution.Image := do
  requireKeys request ["schema", "protocol", "mode", "payload", "half_cycles"]
  let mode ← field request "mode" 0 3
  let half ← field request "half_cycles" 1 256
  let values ← (← request.getObjVal? "payload").getArr?
  if h : 1 ≤ values.size ∧ values.size ≤ 2 then
    let bytes ← values.mapM (fun value => bounded value "payload byte" 0 255)
    let payload := bytes.foldl (fun total byte => total * 256 + byte.val) 0
    let cfg : SPI.Transaction.Config :=
      ⟨⟨mode.val / 2 == 1, mode.val % 2 == 1⟩,
        ⟨half.val - 1, by have := half.property; omega⟩,
        ⟨values.size - 1, by omega⟩⟩
    return Compile.SPITransaction.program cfg (BitVec.ofNat 16 payload)
  else throw "payload must contain one or two bytes in wire order"

private def programJson (program : Hardware.Execution.Image) : Json := Json.mkObj [
  ("format", toJson "pinwheel-paired32-v1"),
  ("words", toJson ((Hardware.Execution.imageWords program).toList.map BitVec.toNat)),
  ("last", toJson program.last.val),
  ("idle_levels", toJson program.idle.levels.toNat),
  ("idle_enabled", toJson program.idle.enabled.toNat)]

/-- Export the existing frontend's canonical source and retain the validated
request identity. Result interpretation remains attached to this request. -/
def compileRequest (request : Json) : Except String Json := do
  let schema ← (← request.getObjVal? "schema").getStr?
  unless schema == requestSchema do throw "Unsupported request schema"
  let protocol ← (← request.getObjVal? "protocol").getStr?
  let program ← match protocol with
    | "i2c-register-read" => readProgram request
    | "spi-transaction" => spiProgram request
    | _ => throw "Unsupported protocol"
  return Json.mkObj [("schema", toJson responseSchema), ("request", request), ("program", programJson program)]

def compileText (text : String) : Except String String := do
  let request ← Json.parse text
  return (← compileRequest request).compress

end Pinwheel.Program.Export
