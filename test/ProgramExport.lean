import Pinwheel.Program.Requests

open Lean Pinwheel
open Pinwheel.Program.Export

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def readRequest (address register count phase wait : Nat) : Json := Json.mkObj [
  ("schema", toJson requestSchema), ("protocol", toJson "i2c-register-read"),
  ("address", toJson address), ("register", toJson register), ("byte_count", toJson count),
  ("phase_cycles", toJson phase), ("wait_cycles", toJson wait)]

private def spiRequest (mode : Nat) (bytes : List Nat) (half : Nat) : Json := Json.mkObj [
  ("schema", toJson requestSchema), ("protocol", toJson "spi-transaction"),
  ("mode", toJson mode), ("payload", toJson bytes), ("half_cycles", toJson half)]

private def replaceField (request : Json) (key : String) (value : Json) : Json :=
  match request.getObj? with
  | .error _ => request
  | .ok object => Json.mkObj (object.toList.map fun (name, old) =>
      (name, if name == key then value else old))

private def failed : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def fieldIs (object : Json) (name : String) (expected : Json) : Bool :=
  match object.getObjVal? name with
  | .ok actual => actual == expected
  | .error _ => false

private def rejects (request : Json) : IO Unit :=
  ensure (failed (compileRequest request)) s!"Invalid request accepted: {request.compress}"

private def matchesImage (request : Json) (expected : Hardware.Execution.Image) : IO Unit := do
  let .ok response := compileRequest request | throw (IO.userError "Valid request rejected")
  ensure (fieldIs response "request" request) "Request identity changed"
  ensure (fieldIs response "schema" (toJson responseSchema)) "Response schema changed"
  let .ok program := response.getObjVal? "program" | throw (IO.userError "Missing program")
  ensure (fieldIs program "format" (toJson "pinwheel-paired32-v1")) "Wrong hardware target"
  ensure (fieldIs program "words" (toJson ((Hardware.Execution.imageWords expected).toList.map BitVec.toNat)))
    "Export changed the frontend's exact E64 words"
  ensure (fieldIs program "last" (toJson expected.last.val)) "Export changed last address"
  ensure (fieldIs program "idle_levels" (toJson expected.idle.levels.toNat) &&
    fieldIs program "idle_enabled" (toJson expected.idle.enabled.toNat)) "Export changed idle pins"

def main : IO Unit := do
  -- Established fixture requests, including all modes and both transfer sizes.
  for mode in [:4] do
    for count in [1, 2] do
      let bytes := if count == 1 then [0xa6] else [0xa6, 0x53]
      let cfg : SPI.Transaction.Config := ⟨⟨mode ≥ 2, mode % 2 == 1⟩, 3,
        (if count == 1 then 0 else 1)⟩
      matchesImage (spiRequest mode bytes 4) (Compile.SPITransaction.program cfg (if count == 1 then 0xa6 else 0xa653))
  matchesImage (readRequest 0x53 0xa6 1 4 32) (Compile.I2CReadTransaction.program ⟨3, 31⟩ ⟨0x53, 0xa6, 0⟩)
  matchesImage (readRequest 0x53 0xa6 2 4 32) (Compile.I2CReadTransaction.program ⟨3, 31⟩ ⟨0x53, 0xa6, 1⟩)
  -- Fresh requests exercise strict endpoints and different literal payloads.
  matchesImage (readRequest 0x2d 0x71 2 7 19) (Compile.I2CReadTransaction.program ⟨6, 18⟩ ⟨0x2d, 0x71, 1⟩)
  matchesImage (readRequest 127 255 1 256 1) (Compile.I2CReadTransaction.program ⟨255, 0⟩ ⟨127, 255, 0⟩)
  matchesImage (spiRequest 3 [0, 255] 256) (Compile.SPITransaction.program ⟨⟨true, true⟩, 255, 1⟩ 255)
  matchesImage (spiRequest 1 [0x3b] 1) (Compile.SPITransaction.program ⟨⟨false, true⟩, 0, 0⟩ 0x3b)
  let read := readRequest 0x53 0xa6 2 4 32
  for (name, bad) in [("address", 128), ("register", 256), ("byte_count", 0), ("byte_count", 3),
      ("phase_cycles", 0), ("phase_cycles", 257), ("wait_cycles", 0), ("wait_cycles", 257)] do
    rejects (replaceField read name (toJson (bad : Nat)))
  for name in ["address", "register", "byte_count", "phase_cycles", "wait_cycles"] do
    for bad in [Json.bool true, Json.null, toJson "1", toJson (-1 : Int)] do
      rejects (replaceField read name bad)
  for name in ["schema", "protocol"] do rejects (replaceField read name (toJson "wrong"))
  let .ok object := read.getObj? | throw (IO.userError "Test request is not an object")
  rejects (Json.mkObj (("extra", toJson (1 : Nat)) :: object.toList))
  rejects (Json.mkObj (object.toList.filter fun (name, _) => name != "register"))
  let spi := spiRequest 0 [0xa6] 4
  for (name, bad) in [("mode", 4), ("half_cycles", 0), ("half_cycles", 257)] do
    rejects (replaceField spi name (toJson (bad : Nat)))
  for bytes in [([] : List Nat), [0, 1, 2], [256], [1, 256]] do
    rejects (replaceField spi "payload" (toJson bytes))
  for bad in [Json.bool false, Json.null, toJson "payload", Json.arr #[toJson (-1 : Int)], Json.arr #[Json.bool true]] do
    rejects (replaceField spi "payload" bad)
  for text in ["not JSON", "{}", "[]", "null", "{\"schema\":1}",
      "{\"schema\":\"pinwheel-protocol-request-v1\",\"protocol\":\"i2c-register-read\",\"address\":1.0,\"register\":0,\"byte_count\":1,\"phase_cycles\":1,\"wait_cycles\":1}"] do
    ensure (failed (compileText text)) s!"Malformed or noninteger JSON accepted: {text}"
  IO.println "Program export: 14 exact frontend images, strict request ranges/types/shapes, and nonfixture/boundary requests passed."
