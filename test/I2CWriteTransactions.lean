import Pinwheel.Compile.I2CWriteTransactionProofs
import Pinwheel.Hardware.Storage.PairedImage
import Lean

open Pinwheel Pinwheel.Hardware
open Lean (toJson)
open Pinwheel.Compile.I2CWriteTransaction (program)

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private structure Fixture where
  name : String
  address : Nat
  payload : List Nat
  ack : List Nat
  phaseCycles : Nat := 4
  waitCycles : Nat := 32
  stretchCycles : Nat := 0
  stuck : Bool := false

private def cfg (f : Fixture) : I2C.Config :=
  ⟨⟨min (f.phaseCycles - 1) 255, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩,
   ⟨min (f.waitCycles - 1) 255, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩

private def request (f : Fixture) : I2C.WriteTransaction.Request :=
  ⟨Fin.ofNat 128 f.address,
   ⟨min (f.payload.length - 1) 1, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩,
   BitVec.ofNat 16 (f.payload.foldl (fun a b => 256 * a + b) 0)⟩

private def expectedClocks (f : Fixture) : Nat :=
  if f.stuck then 0 else 9 * (if f.ack.contains 1 then f.ack.idxOf 1 + 1 else f.ack.length)

private def expectedSamples (f : Fixture) : Nat :=
  if f.stuck then 0 else (f.ack.take (expectedClocks f / 9)).zipIdx.foldl
    (fun a (bit, index) => a + bit * 2^index) 0

private def metadata (f : Fixture) : Lean.Json := Lean.Json.mkObj [
  ("name", toJson f.name), ("address", toJson f.address), ("payload_bytes", toJson f.payload),
  ("ack_bits", toJson f.ack), ("phase_cycles", toJson f.phaseCycles),
  ("wait_cycles", toJson f.waitCycles), ("stretch_cycles", toJson f.stretchCycles),
  ("scl_stuck", toJson f.stuck), ("expected_samples", toJson (expectedSamples f)),
  ("expected_outcome", toJson (if f.stuck then 6 else (5 : Nat))),
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
  ensure (f.address < 128 && (f.payload.length == 1 || f.payload.length == 2) &&
    f.payload.all (· < 256) && f.ack.length == f.payload.length + 1 && f.ack.all (· ≤ 1) &&
    1 ≤ f.phaseCycles && f.phaseCycles ≤ 256 && 1 ≤ f.waitCycles && f.waitCycles ≤ 256)
    s!"Invalid write fixture: {f.name}"
  let p := program (cfg f) (request f)
  let words := Execution.imageWords p
  ensure (p.last.val + 1 == 115 && words.toList.eraseDups.length ≤ 32)
    s!"Write E64 capacity: {f.name}"
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

private def expectedResult (f : Fixture) : I2C.WriteTransaction.Outcome :=
  if f.stuck then .timeout else if f.ack[0]! == 1 then .addressNack
  else if f.ack[1]! == 1 then .payload1Nack
  else if f.payload.length == 2 && f.ack[2]! == 1 then .payload2Nack else .success

/-- An ideal resolved-wire target sees edges and byte count, never the program counter.
Typed and decoded execution are compared to the reference at every consumed edge. -/
private def validateWire (f : Fixture) : IO Nat := do
  let c := cfg f
  let r := request f
  let p := program c r
  let store := Execution.directStore (Execution.imageWords p) p.idle p.last
  let mut reference := I2C.WriteTransaction.initial c
  let mut core := Engine.Reactive.Fetch.start store 3
  let mut target : I2C.Pins := {}
  let mut previous : I2C.Bus := {}
  let mut previousCommand : I2C.Pins := {}
  let mut stretchLeft := 0
  let mut clocks : Array Bool := #[]
  let mut pending : Option Bool := none
  let mut starts := 0
  let mut stopped := false
  let mut cycles := 0
  for t in [:160 * c.phaseCycles + 40 * (c.waitCycles + 2)] do
    ensure (core == Compile.I2CWriteTransaction.lift r reference) s!"Reference mismatch: {f.name}/{t}"
    ensure (Compile.I2CWriteTransaction.result r core == I2C.WriteTransaction.result r reference)
      s!"Result refinement: {f.name}/{t}"
    let command : I2C.Pins := ⟨if core.pins.enabled[0] then .low else .release,
      if core.pins.enabled[1] then .low else .release⟩
    ensure (core.pins.levels == 0 && !core.pins.enabled[2]) s!"Unsafe drive: {f.name}/{t}"
    if previousCommand.scl == .low && command.scl == .release then stretchLeft := f.stretchCycles
    target := {target with scl := if f.stuck || stretchLeft > 0 then .low else .release}
    let bus := I2C.resolve command target
    if previous.scl && bus.scl && previous.sda != bus.sda then
      if previous.sda then
        starts := starts + 1
        ensure (starts == 1) s!"Extra START: {f.name}/{t}"
      else
        ensure (starts == 1) s!"STOP before START: {f.name}/{t}"
        stopped := true
      pending := none
    if !previous.scl && bus.scl && starts > 0 && !stopped then pending := some bus.sda
    if previous.scl && !bus.scl then
      if let some bit := pending then clocks := clocks.push bit
      pending := none
    if !bus.scl then
      target := {target with sda := if clocks.size % 9 == 8 && f.ack[clocks.size / 9]?.getD 1 == 0
        then .low else .release}
    let observed := I2C.resolve command target
    if observed.scl && clocks.size % 9 == 8 then
      ensure (command.sda == .release) s!"Controller drove ACK: {f.name}/{t}"
    let input := Compile.I2C.encodeInputs observed
    ensure ((Engine.Reactive.Fetch.step store core true true input).pins == ({} : Engine.Reactive.Pins))
      s!"Reset did not release: {f.name}/{t}"
    previous := observed
    previousCommand := command
    core := Engine.Reactive.Fetch.advance store core input
    reference := I2C.WriteTransaction.step c r reference observed
    stretchLeft := stretchLeft - 1
    cycles := t + 1
    if !Engine.Reactive.busy core then break
  ensure (core == Compile.I2CWriteTransaction.lift r reference) s!"Terminal refinement: {f.name}"
  ensure (Compile.I2CWriteTransaction.result r core == some (expectedResult f))
    s!"Wrong outcome: {f.name}: {repr (Compile.I2CWriteTransaction.result r core)}"
  ensure (clocks.size == expectedClocks f) s!"Wrong clock count: {f.name}: {clocks.size}"
  ensure (if f.stuck then starts == 0 && !stopped else starts == 1 && stopped)
    s!"START/STOP mismatch: {f.name}"
  let samples := (List.range 16).foldl (fun a k => a + if core.samples[k]! then 2^k else 0) 0
  ensure (samples == expectedSamples f) s!"Independent ACK slots: {f.name}: {samples}"
  let bytes := (f.address * 2) :: f.payload
  for k in [:clocks.size] do
    let expected := if k % 9 == 8 then f.ack[k / 9]! == 1 else bytes[k / 9]!.testBit (7 - k % 9)
    ensure (clocks[k]! == expected) s!"MSB-first byte order: {f.name}/{k}"
  ensure (core.pins == ({} : Engine.Reactive.Pins)) s!"Terminal pins not released: {f.name}"
  return cycles

private def fixtures : List Fixture := [
  ⟨"i2c-write-1-success", 0x53, [0xa6], [0,0], 4, 32, 0, false⟩,
  ⟨"i2c-write-1-address-nack", 0x53, [0xa6], [1,1], 4, 32, 0, false⟩,
  ⟨"i2c-write-1-payload1-nack", 0x53, [0xff], [0,1], 4, 32, 0, false⟩,
  ⟨"i2c-write-2-success", 0x53, [0xa6,0x53], [0,0,0], 4, 32, 0, false⟩,
  ⟨"i2c-write-2-address-nack", 0x53, [0xa6,0x53], [1,1,1], 4, 32, 0, false⟩,
  ⟨"i2c-write-2-payload1-nack", 0x53, [0x00,0xff], [0,1,1], 4, 32, 0, false⟩,
  ⟨"i2c-write-2-payload2-nack", 0x53, [0xff,0x00], [0,0,1], 4, 32, 0, false⟩,
  ⟨"i2c-write-2-h3", 0x08, [0x00,0xff], [0,0,0], 3, 32, 0, false⟩,
  ⟨"i2c-write-2-stretch1", 0x77, [0xff,0x00], [0,0,0], 4, 32, 1, false⟩,
  ⟨"i2c-write-2-stretch3", 0x53, [0x00,0xff], [0,0,0], 4, 32, 3, false⟩,
  ⟨"i2c-write-2-scl-stuck", 0x53, [0xa6,0x53], [0,0,0], 4, 32, 0, true⟩]

def main (args : List String) : IO Unit := do
  let out : System.FilePath ← match args with
    | [] => pure "build/i2c-write-transactions"
    | [path] => pure path
    | _ => throw (IO.userError "usage: I2CWriteTransactions.lean [output-directory]")
  IO.FS.createDirAll out
  let lines ← fixtures.mapM validateImage
  let cycles ← fixtures.mapM validateWire
  IO.FS.writeFile (out / "images.txt") (String.intercalate "\n" lines ++ "\n")
  IO.FS.writeFile (out / "metadata.json") ((Lean.Json.arr (fixtures.map metadata).toArray).pretty ++ "\n")
  IO.FS.writeFile (out / "ideal-wire-cycles.json") ((toJson cycles).pretty ++ "\n")
  IO.println "I2C writes: 11 one/two-byte images; ideal resolved-wire byte/ACK/STOP traces, E64 decoding, 32-record indexed capacity, paired certificates and wrong-parameter controls passed."
