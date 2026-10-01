import Pinwheel.UART.BufferedSupervisor
import Pinwheel.Hardware.Storage.PairedImage
import Lean

open Pinwheel Pinwheel.Hardware
open Lean (toJson)
open Pinwheel.UART.Rx.BufferedSupervisor

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def config (cycles pin : Nat) : IO UART.Rx.Config :=
  match UART.Rx.Config.ofCycles cycles (Fin.ofNat 2 pin) with
  | some cfg => pure cfg
  | none => throw (IO.userError s!"Invalid UART period {cycles}")

/-- Untrusted deduplication; PairedImage.check validates every emitted token. -/
private def lowered (p : Execution.Image) : Storage.PairedImage.Image := Id.run do
  let parameters := (List.range (p.last.val + 1)).map (fun pc =>
    Storage.PairedImage.parameter (Storage.PairedImage.fields p (BitVec.ofNat 8 pc))) |>.eraseDups
  let token (node : Storage.PairedImage.Node) : BitVec 32 := match node with
    | none => 7
    | some pc =>
      let f := Storage.PairedImage.fields p pc
      if f.kind == 4 then 4 else
        (0#2) ++ pc ++ (BitVec.ofNat 5 (parameters.idxOf (Storage.PairedImage.parameter f))) ++
          f.duration ++ f.enabled ++ f.levels ++ f.kind
  return {
    parameters := Vector.ofFn fun k => parameters[k.val]?.getD 0
    rows := Vector.ofFn fun k => if k.val ≤ p.last.val then
      token (Storage.PairedImage.successor p (BitVec.ofFin k) true) ++
        token (Storage.PairedImage.successor p (BitVec.ofFin k) false)
      else (4#32) ++ (4#32)
    boot := token (some 0)
    idle := p.idle.enabled ++ p.idle.levels }

private def emit (out : System.FilePath) : IO Unit := do
  IO.FS.createDirAll out
  let mut lines : List String := []
  let mut metadata : Array Lean.Json := #[]
  let mut maxPositions := 0
  let mut maxRecords := 0
  for cycles in [8, 9, 16, 257, 6656] do
    for pin in [:2] do
      let cfg ← config cycles pin
      let name := s!"rx-b{cycles}-pin{pin}"
      let p := Compile.UARTRx.program cfg
      let words := UARTRx.words cfg
      let records := words.toList.eraseDups.length
      ensure (p.last.val < 256 && records ≤ 32) s!"UART capacity: {name}"
      let some indexed := Execution.lowerIndexed words
        | throw (IO.userError s!"UART indexed capacity: {name}")
      ensure (indexed.val.expand == words) s!"UART indexed certificate: {name}"
      let image := lowered p
      ensure (Storage.PairedImage.check p image (Storage.PairedImage.upload image))
        s!"UART paired certificate: {name}"
      let wrong := {image with parameters := image.parameters.set 0 (image.parameters[0] ^^^ 1)}
      ensure (!(Storage.PairedImage.check p wrong (Storage.PairedImage.upload wrong)))
        s!"UART wrong-parameter rejection: {name}"
      for pc in [:256] do
        ensure (Execution.decode words[pc]! == some (p.fetch (BitVec.ofNat 8 pc).toFin))
          s!"UART E64 decode: {name}/{pc}"
      lines := lines ++ [name ++ " " ++ String.intercalate " "
        (([p.last.val, p.idle.levels.toNat, p.idle.enabled.toNat] ++
          words.toList.map BitVec.toNat).map toString)]
      metadata := metadata.push (Lean.Json.mkObj [
        ("name", toJson name), ("bit_cycles", toJson cycles), ("input_pin", toJson pin),
        ("populated_positions", toJson (p.last.val + 1)), ("canonical_records", toJson records)])
      maxPositions := max maxPositions (p.last.val + 1)
      maxRecords := max maxRecords records
  IO.FS.writeFile (out / "images.txt") (String.intercalate "\n" lines ++ "\n")
  IO.FS.writeFile (out / "metadata.json") ((Lean.Json.arr metadata).pretty ++ "\n")
  IO.println s!"UART buffer fixtures: 10 images; maxima {maxPositions} positions, {maxRecords} canonical records; E64/indexed/paired checks and wrong-parameter rejection passed."

private def observed (core : Compile.UARTRx.RxState) (started : Bool) : Values Loader.Machine.Output
  | _, .core .busy => BitVec.ofBool (Engine.Reactive.busy core)
  | _, .core (.state .mode) => (Reactive.embed core).mode
  | _, .core (.state (.sample k)) => BitVec.ofBool core.samples[k.val]
  | _, .control .start => BitVec.ofBool started
  | _, _ => 0

private def frame (byte : BitVec 8) (start period now : Nat) (stop : Bool) : Bool :=
  if now < start then true else
    let symbol := (now - start) / period
    if symbol == 0 then false else if symbol ≤ 8 then byte.getLsbD (symbol - 1)
    else if symbol == 9 then stop else true

/-- Two absolute-time frames exercise the actual observer's extra edge, retention,
framing-error drop and sticky overrun; sender timing never uses the program counter. -/
private def phaseChecks : IO Unit := do
  let cfg ← config 16 0
  let mut s : State := {receiver := UART.Rx.initial, wasActive := true}
  let mut compiled := lift cfg s
  let mut host : HostResult.State := {resetFirst := true, resetSecond := true, wasActive := true}
  let pins : Chip.Pins := {}
  let firstComplete := 5 + cfg.half + 9 * cfg.bitCycles
  let secondStart := 5 + 12 * cfg.bitCycles
  let secondComplete := secondStart + cfg.half + 9 * cfg.bitCycles
  for now in [1:secondComplete + 3] do
    let line := if now < secondStart then frame 0xa6 5 cfg.bitCycles now true
      else frame 0x53 secondStart cfg.bitCycles now false
    let input : Input := {line := line, start := true}
    let edge := step cfg s input
    let actual := HostResult.next pins (observed compiled.core input.start) host
    ensure (HostResultBuffer.uartProject actual == edge.state.buffer)
      s!"Actual observer pre-step agreement at {now}"
    ensure (HostResultBuffer.uartReceipt (HostResultBuffer.receipt pins (observed compiled.core input.start) host)
      == edge.receipt) s!"Actual ownership receipt at {now}"
    let machine := decodedStep cfg compiled input (now % 3 == 0)
    ensure (machine.state == lift cfg edge.state && machine.receipt == edge.receipt)
      s!"Canonical E64 supervisor at {now}"
    ensure (actual.valid == (now > firstComplete)) s!"Mailbox completion phase at {now}"
    ensure (actual.overrun == (now > secondComplete)) s!"Mailbox drop phase at {now}"
    if now == firstComplete + 1 then
      ensure (edge.receipt.accepted == some (.byte 0xa6)) "First UART byte admission"
    if now == secondComplete + 1 then
      ensure (edge.receipt.dropped == some (.framingError 0x53)) "Bad-stop occurrence drop"
    if actual.valid then ensure (actual.samples.extractLsb' 0 8 == 0xa6) "Unread byte was replaced"
    s := edge.state
    compiled := machine.state
    host := actual

private def ownershipChecks : IO Unit := do
  let cfg ← config 8 1
  let old : UART.Rx.Outcome := .byte 0xa6
  let new : UART.Rx.Outcome := .framingError 0x53
  let slots := ((((Vector.replicate 16 false).set 0 true).set 1 true).set 4 true).set 6 true
  let full : State := {receiver := ⟨.finished, 0, slots⟩, buffer := ⟨some old, true⟩, wasActive := true}
  let simultaneous := step cfg full {take := true, clearOverrun := true, start := true}
  ensure (simultaneous.receipt.delivered == some old && simultaneous.receipt.accepted == some new &&
    simultaneous.state.buffer.pending == some new && !simultaneous.state.buffer.overrun)
    "Consume old/admit new ownership"
  let dropped := step cfg full {clearOverrun := true}
  ensure (dropped.receipt.dropped == some new && dropped.state.buffer.pending == some old &&
    dropped.state.buffer.overrun) "Fresh drop did not dominate sticky clear"
  let empty := step cfg {full with buffer := {}} {take := true}
  ensure (empty.receipt.delivered.isNone && empty.state.buffer.pending == some new)
    "Empty take bypassed arrival"
  let retained := step cfg {full with receiver := UART.Rx.initial} {receiverReset := true}
  ensure (retained.state.receiver == UART.Rx.reset && retained.state.buffer == full.buffer &&
    retained.receipt == {}) "Receiver abort flushed unread mailbox"
  let flushed := step cfg full {flush := true, receiverReset := true, take := true}
  ensure (flushed.state.buffer == {} && !flushed.state.wasActive && flushed.receipt.flushed == some old &&
    flushed.receipt.delivered.isNone && flushed.receipt.accepted.isNone)
    "External reset ownership priority"
  let duplicate := Hardware.HostResultBuffer.Retained.run
    (⟨some old, false⟩ : Hardware.HostResultBuffer.Retained.State UART.Rx.Outcome)
    [.cycle (some old) true false, .cycle (some old) false false, .reset]
  ensure (Hardware.HostResultBuffer.Retained.delivered duplicate.receipts == [old] &&
    Hardware.HostResultBuffer.Retained.dropped duplicate.receipts == [old] &&
    Hardware.HostResultBuffer.Retained.flushed duplicate.receipts == [old])
    "Identical-valued occurrences lost ownership"
  IO.println "UART buffered supervisor: pre-step completion phase, decoded E64 correspondence, framing-error drop, consume/admit, clear/drop, abort retention, external flush and duplicate occurrence checks passed."

def main (args : List String) : IO Unit := do
  match args with
  | [] => phaseChecks; ownershipChecks; emit "build/uart-buffered-supervisor"
  | ["--emit", path] => emit path
  | _ => throw (IO.userError "usage: UARTBufferedSupervisor.lean [--emit output-directory]")
