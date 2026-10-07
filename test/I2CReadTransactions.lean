import Pinwheel.Compile.I2CReadTransactionProofs
import Pinwheel.Hardware.Storage.PairedImage
import Lean

open Pinwheel Pinwheel.Hardware
open Pinwheel.I2C
open Pinwheel.Compile.I2CReadTransaction
open Lean (toJson)

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private structure Fixture where
  name : String
  address : Nat
  register : Nat
  payload : List Nat
  ack : List Nat
  phaseCycles : Nat := 4
  waitCycles : Nat := 32
  stretchCycles : Nat := 0
  stuck : Bool := false
  deriving Inhabited

private def config (f : Fixture) : Config :=
  ⟨⟨min (f.phaseCycles - 1) 255, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩,
   ⟨min (f.waitCycles - 1) 255, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩

private def request (f : Fixture) : RegisterReadTransaction.Request :=
  ⟨Fin.ofNat 128 f.address, BitVec.ofNat 8 f.register,
   ⟨min (f.payload.length - 1) 1, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩

private def payloadValue (f : Fixture) : Nat := f.payload.foldl (fun a b => 256 * a + b) 0

private def expectedClocks (f : Fixture) : Nat :=
  if f.stuck then 0 else if f.ack.contains 1 then 9 * (f.ack.idxOf 1 + 1)
  else 9 * (3 + f.payload.length)

private def expectedSamples (f : Fixture) : Nat :=
  if f.stuck then 0 else if f.ack.contains 1 then 2 ^ f.ack.idxOf 1 else
  f.payload.zipIdx.foldl (fun a (byte, n) =>
    a + (List.range 8).foldl (fun b k => b + if byte.testBit (7-k) then 2^(8*n+k) else 0) 0) 0

private def expectedStage (f : Fixture) : Option RegisterReadTransaction.NackStage :=
  if f.stuck then none else if f.ack[0]! == 1 then some .writeAddress
  else if f.ack[1]! == 1 then some .register else if f.ack[2]! == 1 then some .readAddress else none

private def metadata (f : Fixture) : Lean.Json := Lean.Json.mkObj [
  ("name", toJson f.name), ("address", toJson f.address), ("register", toJson f.register),
  ("payload_bytes", toJson f.payload), ("byte_count", toJson f.payload.length), ("ack_bits", toJson f.ack),
  ("phase_cycles", toJson f.phaseCycles), ("wait_cycles", toJson f.waitCycles),
  ("stretch_cycles", toJson f.stretchCycles), ("scl_stuck", toJson f.stuck),
  ("expected_samples", toJson (expectedSamples f)),
  ("expected_outcome", toJson (if f.stuck then 6 else if f.ack.contains 1 then 7 else (5 : Nat))),
  ("expected_clock_count", toJson (expectedClocks f))]

/-- Untrusted parameter deduplication; the independent certificate checks every token. -/
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

private def validateImage (f : Fixture) : IO String := do
  ensure (f.address < 128 && f.register < 256 && (f.payload.length == 1 || f.payload.length == 2) &&
    f.payload.all (· < 256) && f.ack.length == 3 && f.ack.all (· ≤ 1) &&
    1 ≤ f.phaseCycles && f.phaseCycles ≤ 256 && 1 ≤ f.waitCycles && f.waitCycles ≤ 256)
    s!"Invalid read fixture: {f.name}"
  let p := program (config f) (request f)
  let words := Execution.imageWords p
  ensure (p.last.val + 1 == 196 && words.toList.eraseDups.length ≤ 32)
    s!"Read E64 capacity: {f.name}"
  let some indexed := Execution.lowerIndexed words | throw (IO.userError s!"Indexed lowering: {f.name}")
  ensure (indexed.val.expand == words) s!"Indexed certificate: {f.name}"
  let paired := lowered p
  ensure (Storage.PairedImage.check p paired (Storage.PairedImage.upload paired))
    s!"Paired certificate: {f.name}"
  let wrong := {paired with parameters := paired.parameters.set 0 (paired.parameters[0] ^^^ 1)}
  ensure (!(Storage.PairedImage.check p wrong (Storage.PairedImage.upload wrong)))
    s!"Wrong parameter certified: {f.name}"
  for pc in [:256] do
    ensure (Execution.decode words[pc]! == some (p.fetch (BitVec.ofNat 8 pc).toFin))
      s!"E64 decode: {f.name}/{pc}"
  return f.name ++ " " ++ String.intercalate " " (([p.last.val, p.idle.levels.toNat,
    p.idle.enabled.toNat] ++ words.toList.map BitVec.toNat).map toString)

/-- Target decisions depend on observed edges and byte count, never reference phases or PCs. -/
private def validateWire (f : Fixture) (transform : ReadProgram → ReadProgram := id) : IO Nat := do
  let cfg := config f
  let request := request f
  let acks : Vector Bool 3 := Vector.ofFn fun k => f.ack[k.val]! == 0
  let stretch := fun (_ : Nat) => f.stretchCycles
  let p := transform (program cfg request)
  let store := Pinwheel.Hardware.Execution.directStore (Pinwheel.Hardware.Execution.imageWords p) p.idle p.last
  let mut reference := RegisterReadTransaction.initial cfg
  let mut core := Pinwheel.Engine.Reactive.Fetch.start store 3
  let mut target : Pins := {}
  let mut previous : Bus := {}
  let mut previousCommand : Pins := {}
  let mut stretchLeft := 0
  let mut releases := 0
  let mut clocks : Array Bool := #[]
  let mut pending : Option Bool := none
  let mut starts := 0
  let mut stopped := false
  let mut riseAt := 0
  let mut fallAt := 0
  let mut cycles := 0
    let limit := 220 * cfg.phaseCycles + 52 * (cfg.waitCycles + 2)
  for t in [:limit] do
    ensure (core == lift request reference) s!"reference mismatch at {t}"
    ensure (result request core == RegisterReadTransaction.result request reference) s!"result mismatch at {t}"
    let command : Pins := ⟨if core.pins.enabled[0] then .low else .release,
      if core.pins.enabled[1] then .low else .release⟩
    ensure (core.pins.levels == 0 && !core.pins.enabled[2]) "unsafe drive"
    if previousCommand.scl == .low && command.scl == .release then
      stretchLeft := stretch releases
      releases := releases + 1
    target := {target with scl := if f.stuck || stretchLeft > 0 then .low else .release}
    let bus := resolve command target
    if previous.scl && bus.scl && previous.sda != bus.sda then
      if previous.sda then
        starts := starts + 1
        ensure (starts == 1 || (starts == 2 && clocks.size == 18)) "unexpected START"
        ensure (t - riseAt >= cfg.phaseCycles) "START setup too short"
        pending := none
      else
        ensure (starts > 0 && t - riseAt >= cfg.phaseCycles) "invalid STOP"
        stopped := true
        pending := none
    if !previous.scl && bus.scl && starts > 0 && !stopped then
      ensure (t - fallAt >= cfg.phaseCycles) "low interval too short"
      riseAt := t
      pending := some bus.sda
    if previous.scl && !bus.scl then
      fallAt := t
      if let some bit := pending then
        ensure (t - riseAt >= cfg.phaseCycles) "high interval too short"
        clocks := clocks.push bit
        pending := none
    if !bus.scl then
      let low := if clocks.size == 8 then acks[0]
        else if clocks.size == 17 then acks[1]
        else if clocks.size == 26 then acks[2]
        else if acks[2] && 27 <= clocks.size && clocks.size < 35 then !f.payload[0]!.testBit (34 - clocks.size)
        else if f.payload.length == 2 && acks[2] && 36 <= clocks.size && clocks.size < 44 then !f.payload[1]!.testBit (43 - clocks.size)
        else false
      target := {target with sda := if low then .low else .release}
    let observed := resolve command target
    if observed.scl && pending.isSome && clocks.size < (expectedClocks f) &&
        (clocks.size == 8 || clocks.size == 17 || clocks.size == 26 ||
          (27 <= clocks.size && clocks.size < 35) || (36 <= clocks.size && clocks.size < 45) ||
          (clocks.size == 35 && f.payload.length == 1)) then
      ensure (command.sda == .release) "controller drove target data/ACK or final NACK"
    let inputs := Pinwheel.Compile.I2C.encodeInputs observed
    ensure ((Pinwheel.Engine.Reactive.Fetch.step store core true true inputs) ==
      Pinwheel.Engine.Reactive.Fetch.reset store) "reset priority/state"
    let (loaded, accepted) := Pinwheel.Engine.Reactive.Fetch.load ⟨store, core⟩ store
    ensure (!accepted && loaded.state == core) "busy reload changed running program"
    previous := observed
    previousCommand := command
    core := Pinwheel.Engine.Reactive.Fetch.advance store core inputs
    reference := RegisterReadTransaction.step cfg request reference observed
    stretchLeft := stretchLeft - 1
    cycles := t + 1
    if !Pinwheel.Engine.Reactive.busy core then break
  ensure (core == lift request reference) "terminal reference mismatch"
  let expected : RegisterReadTransaction.Outcome := if f.stuck then .timeout
    else if f.ack.contains 1 then .nackOrBusFault else .success (BitVec.ofNat 16 (payloadValue f))
  ensure (result request core == some expected) s!"wrong read result: {f.name}: {repr (result request core)}"
  ensure (if f.stuck then !stopped && starts == 0 else
      stopped && starts == if acks[0] && acks[1] then 2 else 1) "missing START/repeated START/STOP"
  ensure (reference.nackStage == expectedStage f) s!"wrong internal NACK stage: {f.name}"
  ensure (clocks.size == expectedClocks f) s!"wrong pulse count {clocks.size}"
  let outgoing := #[request.address.val * 2, request.register.toNat, request.address.val * 2 + 1] ++ f.payload.toArray
  for k in [:clocks.size] do
    let expectedBit := if k % 9 == 8 then (if k < 27 then !acks[k / 9]! else k == 44 || f.payload.length == 1)
      else outgoing[k / 9]!.testBit (7 - k % 9)
    ensure (clocks[k]! == expectedBit) s!"wire bit mismatch at {k}"
  ensure ((Pinwheel.Engine.Reactive.Fetch.advance store core 0) == core) "finished state not retained"
  let (reloaded, accepted) := Pinwheel.Engine.Reactive.Fetch.load ⟨store, core⟩ store
  ensure (accepted && reloaded.state == Pinwheel.Engine.Reactive.Fetch.reset store) "stopped reload"
  if !f.stuck && !f.ack.contains 1 then
    let raw := (List.range 16).foldl (fun a k => a + if core.samples[k]! then 2^k else 0) 0
    ensure (raw == expectedSamples f) s!"payload capture order: {f.name}"
  return cycles

private def fixtures : List Fixture := [
  ⟨"i2c-read-1-success", 0x53, 0xa6, [0x96], [0,0,0], 4, 32, 0, false⟩,
  ⟨"i2c-read-1-address-nack", 0x53, 0xa6, [0xff], [1,0,0], 4, 32, 0, false⟩,
  ⟨"i2c-read-1-register-nack", 0x53, 0xa6, [0xff], [0,1,0], 4, 32, 0, false⟩,
  ⟨"i2c-read-1-read-address-nack", 0x53, 0xa6, [0xff], [0,0,1], 4, 32, 0, false⟩,
  ⟨"i2c-read-2-success", 0x53, 0xa6, [0x96,0x69], [0,0,0], 4, 32, 0, false⟩,
  ⟨"i2c-read-2-all-ones", 0x53, 0xa6, [0xff,0xff], [0,0,0], 4, 32, 0, false⟩,
  ⟨"i2c-read-2-all-zero", 0x08, 0x00, [0x00,0x00], [0,0,0], 4, 32, 0, false⟩,
  ⟨"i2c-read-2-tag0-payload", 0x53, 0xa6, [0x80,0x00], [0,0,0], 4, 32, 0, false⟩,
  ⟨"i2c-read-2-tag1-payload", 0x53, 0xa6, [0x40,0x00], [0,0,0], 4, 32, 0, false⟩,
  ⟨"i2c-read-2-tag2-payload", 0x53, 0xa6, [0x20,0x00], [0,0,0], 4, 32, 0, false⟩,
  ⟨"i2c-read-2-address-nack", 0x53, 0xa6, [0xff,0xff], [1,0,0], 4, 32, 0, false⟩,
  ⟨"i2c-read-2-register-nack", 0x53, 0xa6, [0x00,0xff], [0,1,0], 4, 32, 0, false⟩,
  ⟨"i2c-read-2-read-address-nack", 0x53, 0xa6, [0xff,0x00], [0,0,1], 4, 32, 0, false⟩,
  ⟨"i2c-read-2-h3", 0x77, 0x00, [0xa5,0x5a], [0,0,0], 3, 32, 0, false⟩,
  ⟨"i2c-read-2-stretch3", 0x53, 0xa6, [0x3c,0xc3], [0,0,0], 4, 32, 3, false⟩,
  ⟨"i2c-read-2-scl-stuck", 0x53, 0xa6, [0xff,0xff], [0,0,0], 4, 32, 0, true⟩]

private def negatives : IO Unit := do
  let f := fixtures[4]!
  let variants : List (String × (ReadProgram → ReadProgram)) := [
    ("missing read capture", fun p => {p with memory := p.memory.map (fun i => match i with
      | .checked a => .checked {a with terminalCapture := none} | _ => i)}),
    ("missing repeated START", fun p => {p with memory := p.memory.set 77 (.halt)}),
    ("NACK completes as success", fun p => {p with memory := p.memory.set 195 (.halt)}),
    ("NACK skips STOP", fun p => {p with memory := p.memory.set 191 (.halt)})]
  for (name, transform) in variants do
    let fixture := if name.startsWith "NACK" then fixtures[12]! else f
    let error ← try
      let _ ← validateWire fixture transform
      pure none
    catch e => pure (some e.toString)
    ensure (error.isSome) s!"mutation not rejected: {name}"

def main (args : List String) : IO Unit := do
  let out : System.FilePath ← match args with
    | [] => pure "build/i2c-read-transactions"
    | [path] => pure path
    | _ => throw (IO.userError "usage: I2CReadTransactions.lean [output-directory]")
  IO.FS.createDirAll out
  let lines ← fixtures.mapM validateImage
  let cycles ← fixtures.mapM validateWire
  negatives
  IO.FS.writeFile (out / "images.txt") (String.intercalate "\n" lines ++ "\n")
  IO.FS.writeFile (out / "metadata.json") ((Lean.Json.arr (fixtures.map metadata).toArray).pretty ++ "\n")
  IO.FS.writeFile (out / "ideal-wire-cycles.json") ((toJson cycles).pretty ++ "\n")
  IO.println "I2C reads:16 one/two-byte images; ideal resolved-wire bytes/ACK/NACK/STOP, compact payload/failure results, E64/paired certificates and four semantic mutations passed."
