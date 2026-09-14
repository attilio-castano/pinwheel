import Pinwheel

open Pinwheel
open Pinwheel.Binary
open Pinwheel.Engine.Reactive
open Pinwheel.Engine.Reactive.Counted

private def ensure (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

private def checkImage (label : String) (image : Image) : IO Unit := do
  let bytes := encodeBytes image
  let some recovered := decodeBytes bytes | throw (IO.userError s!"{label}: valid image rejected")
  ensure (encodeBytes recovered == bytes) s!"{label}: bytes changed"
  ensure (recovered.store.idle == image.store.idle && recovered.store.last == image.store.last)
    s!"{label}: header changed"
  for pc in [:128] do
    ensure (recovered.store.fetch (Fin.ofNat 128 pc) == image.store.fetch (Fin.ofNat 128 pc))
      s!"{label}: instruction changed at {pc}"
  let cost := storage image
  ensure (cost.header + cost.instructions + cost.layout + cost.data + cost.padding == cost.total)
    s!"{label}: storage accounting mismatch"
  ensure (bytes.size == cost.total) s!"{label}: byte-array length mismatch"

private def goldenChecks : IO Unit := do
  let halt : Counted.Program := ⟨.emit .halt, #v[0x12, 0x34], {}, by decide, by decide, by decide⟩
  let golden : List Byte := [0x50, 0x57, 0x4c, 0, 1, 0, 0, 0x12, 0x34, 0, 4]
  ensure (encode (.counted halt) == golden) "halt image golden bytes"
  ensure (decodeBytes (toBytes golden) |>.isSome) "halt image golden decode"
  let complex : Template := .checked
    (.serial ⟨5, 6⟩ 2 false ⟨.loop 1, .literal 7, false, true⟩) 255 ⟨3, 1⟩
    (some ⟨0, .loop 0⟩) (some ⟨1, .literal 7⟩)
    (.select (.loop 0) 1 (.branch (.loop 1) (.absolute 127) .next) (.jump (.absolute 0)))
  let record : List Byte := [
    2,                              -- checked opcode
    1, 5, 6, 2, 0, 1, 1, 0, 7, 0, 1, -- serial pin expression
    255, 3, 1,                      -- duration, guard mask/value
    1, 0, 1, 0,                     -- entry capture
    1, 1, 0, 7,                     -- terminal capture
    3, 1, 0, 1, 2, 1, 1, 0, 127, 1, 1, 0, 0] -- conditional successor
  ensure (putTemplate complex == record) "complex record golden bytes"
  ensure (getTemplate (record ++ [99]) == some (complex, [99])) "complex record suffix/golden decode"
  let dynamic : Template := .action (.serial {} 0 false ⟨.literal 0, .literal 0, true, false⟩) 0
  ensure (getInstruction (putTemplate dynamic) |>.isNone) "explicit image accepted dynamic operands"
  for n in [:256] do
    let bytes := toBytes [Fin.ofNat 256 n]
    ensure (fromBytes bytes == [Fin.ofNat 256 n]) "native byte conversion"
  IO.println "Passed independent header/complex-record goldens, suffix preservation, and all 256 native byte values."

private def malformedChecks : IO Unit := do
  let p := Compile.I2CLoop.program ⟨3, 7⟩ ⟨0x53, 0xa6⟩
  let images := [Image.counted p, .explicit (Compile.I2C.program ⟨3, 7⟩ ⟨0x53, 0xa6⟩)]
  let mut truncations := 0
  for image in images do
    let bytes := encode image
    for n in [:bytes.length] do
      ensure ((decode (bytes.take n)).isNone) s!"accepted truncation {n}"
      truncations := truncations + 1
    ensure ((decode (bytes ++ [0])).isNone) "accepted trailing byte"
    for offset in [0, 1, 2, 3, 4, 5, 6] do
      ensure ((decode (bytes.set offset 255)).isNone) s!"accepted invalid header field {offset}"
  let header : List Byte := [0x50, 0x57, 0x4c, 0, 1, 0, 0, 0, 0]
  let halt := Code.emit Template.halt
  let three := Code.seq halt (.seq halt halt)
  let badSpan := Code.repeat 7 (.repeat 7 three)
  let badDepth := Code.repeat 0 (.repeat 0 (.repeat 0 halt))
  let badNodes := (List.replicate 32 halt).foldr Code.seq halt
  let badFuel := (List.replicate 65 ()).foldr (fun _ c => Code.repeat 0 c) halt
  for code in [badSpan, badDepth, badNodes, badFuel] do
    ensure ((decode (header ++ putCode code)).isNone) "accepted out-of-bounds code"
  ensure ((decode (header ++ [3])).isNone) "accepted unknown layout tag"
  ensure ((decode (header ++ [0, 5])).isNone) "accepted unknown instruction opcode"
  ensure ((decode (header ++ [2, 8, 0, 4])).isNone) "accepted oversized repeat count"
  let m : Fetch.Machine := ⟨p.store, Fetch.start p.store 3⟩
  let (afterBad, acceptedBad) := Binary.load m [0]
  ensure (!acceptedBad && afterBad.state == m.state) "invalid image changed machine"
  let (afterBusy, acceptedBusy) := Binary.load m (encode (.counted p))
  ensure (!acceptedBusy && afterBusy.state == m.state) "busy binary load accepted"
  let (loaded, accepted) := Binary.load ⟨p.store, Fetch.reset p.store⟩ (encode (.counted p))
  ensure (accepted && loaded.state == Fetch.reset p.store) "stopped binary load failed"
  IO.println s!"Rejected {truncations} truncated images, trailing bytes, invalid fields/tags, and program-bound violations; loading checks passed."

private def fixtures : IO Unit := do
  let dir := "build/binary"
  IO.FS.createDirAll dir
  let rows : List (String × Image) := [
    ("uart-explicit", .explicit (embedProgram (Compile.UART.program ⟨3⟩ 0x53))),
    ("spi-explicit", .explicit (embedProgram (Compile.SPI.program ⟨3⟩ 0xa6))),
    ("i2c-explicit", .explicit (Compile.I2C.program ⟨3, 7⟩ ⟨0x53, 0xa6⟩)),
    ("i2c-counted", .counted (Compile.I2CLoop.program ⟨3, 7⟩ ⟨0x53, 0xa6⟩))]
  let seed := Compile.I2CLoop.program ⟨0, 7⟩ ⟨0x53, 0xa6⟩
  let mut machine : Fetch.Machine := ⟨seed.store, Fetch.reset seed.store⟩
  let mut csv := "image,header_bytes,instruction_bytes,layout_bytes,data_bytes,padding_bytes,total_bytes\n"
  for (name, image) in rows do
    checkImage name image
    let cost := storage image
    csv := csv ++ s!"{name},{cost.header},{cost.instructions},{cost.layout},{cost.data},{cost.padding},{cost.total}\n"
    let path := s!"{dir}/{name}.pwl"
    IO.FS.writeBinFile path (encodeBytes image)
    let bytes ← IO.FS.readBinFile path
    ensure (bytes == encodeBytes image && (decodeBytes bytes).isSome) s!"{name}: file round trip"
    let (loaded, accepted) := Binary.load machine (fromBytes bytes)
    ensure accepted s!"{name}: file-backed replacement rejected"
    machine := {loaded with state := Fetch.start loaded.program 3}
    for _ in [:1024] do
      let bus : Pinwheel.I2C.Bus := ⟨!machine.state.pins.enabled[0], !machine.state.pins.enabled[1]⟩
      machine := {machine with state := Fetch.advance machine.program machine.state (Compile.I2C.encodeInputs bus)}
      if !busy machine.state then break
    ensure (machine.state.control == .stopped .completed) s!"{name}: file-backed execution failed"
    if name.startsWith "i2c" then
      ensure (Compile.I2C.outcome machine.state == some .addressNack) "file-backed I2C STOP/result"
    let mut fetched := "pc,record_bytes\n"
    for pc in [:128] do
      let some instruction := image.store.fetch (Fin.ofNat 128 pc)
        | throw (IO.userError "fixture fetch fault")
      fetched := fetched ++ s!"{pc},{String.intercalate ":" ((putInstruction instruction).map (fun b => toString b.val))}\n"
    IO.FS.writeFile s!"{dir}/{name}.fetch.csv" fetched
  IO.FS.writeFile s!"{dir}/storage.csv" csv
  IO.println "Passed file-backed UART -> SPI -> explicit I2C -> counted I2C replacement and execution."
  IO.println csv.trimAscii.toString

def main : IO Unit := do
  goldenChecks
  malformedChecks
  let mut count := 0
  for duration in ([0, 255] : List (Fin 256)) do
    for value in [:256] do
      let cfg : Pinwheel.I2C.Config := ⟨duration, duration⟩
      let request : Pinwheel.I2C.Request := ⟨0x53, BitVec.ofNat 8 value⟩
      checkImage "explicit payload boundary" (.explicit (Compile.I2C.program cfg request))
      checkImage "counted payload boundary" (.counted (Compile.I2CLoop.program cfg request))
      count := count + 2
  for address in [:128] do
    let request : Pinwheel.I2C.Request := ⟨Fin.ofNat 128 address, 0xa6⟩
    checkImage "explicit address" (.explicit (Compile.I2C.program ⟨3,7⟩ request))
    checkImage "counted address" (.counted (Compile.I2CLoop.program ⟨3,7⟩ request))
    count := count + 2
  fixtures
  IO.println s!"Passed {count} image round trips with all 128 fetched instructions checked per image."
