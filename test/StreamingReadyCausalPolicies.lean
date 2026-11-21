import Lean.Data.Json
import Pinwheel.Hardware.StreamingReady.SegmentCadencedHost
import Pinwheel.Hardware.StreamingReady.SegmentCausalI2C
import Pinwheel.Hardware.StreamingReady.SegmentClockTable
import Pinwheel.Hardware.StreamingReady.SegmentPolicyTiming
import Pinwheel.Program.StreamingReadySegmentWire
import Pinwheel.Program.StreamingSWDBranching

/-! Source execution from cold reset through programming, START, and a
    causal combined read. The attached target sees only resolved pins and
    the host sees only the old core status. -/
open Lean
open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady
open SegmentCore
open Pinwheel.Program.StreamingReady (Pins)
open Pinwheel.Program.StreamingReadySegments

private abbrev Input := StreamingReady.Core.Input
private abbrev Target := Pinwheel.I2C.RegisterReadPeer.Target
private abbrev TargetState := Pinwheel.I2C.RegisterReadPeer.State

private theorem supported : (1 : Nat) = 1 ∨ (1 : Nat) = 2 := .inl rfl

private def requireFixture (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def writeWord (raw : BitVec 2) (address : Nat) (word : BitVec 64) : Values Input
  | _, .command => 1
  | _, .address => BitVec.ofNat 6 address
  | _, .word => word
  | _, .rawInputs => raw
  | _, _ => 0

private def install (machine : SegmentClockTable.Machine 1) (words : List (BitVec 64)) (idle : Pins) (raw : BitVec 2) :
    SegmentClockTable.Table (Register 1) :=
  let edge (before : SegmentClockTable.Table (Register 1)) (i : Values Input) :=
    machine.edge i (fun r => before.read r)
  let cold : Values Input := fun port => match port with
    | .initialize => 1
    | _ => 0
  let commit : Values Input := fun port => match port with
    | .command => 2
    | .count => BitVec.ofNat 7 words.length
    | .idleLevels => idle.levels
    | .idleEnabled => idle.enabled
    | .rawInputs => raw
    | _ => 0
  let reset := machine.edge cold (fun _ => 0)
  let loaded := (words.zipIdx).foldl (fun before (word, address) => edge before (writeWord raw address word)) reset
  edge loaded commit

private def start (machine : SegmentClockTable.Machine 1) (initial : SegmentClockTable.Table (Register 1)) (budget : Nat)
    (raw : BitVec 2) : SegmentClockTable.Table (Register 1) :=
  let offer : Values Input := fun port => match port with
    | .command => 3
    | .expectedGeneration => initial.read (.base .generation)
    | .startCount => BitVec.ofNat 16 budget
    | .rawInputs => raw
    | _ => 0
  machine.edge offer (fun r => initial.read r)

private def pack (bits : List Bool) : BitVec 32 :=
  (bits.foldl (fun (word : BitVec 32) bit => (word <<< 1) + BitVec.ofNat 32 bit.toNat) 0) <<< (32 - bits.length)

private abbrev Plan := List (Nat × SegmentCadencedHost.Chunk)

private def fixturePolicy (cooldown : Nat) (plan : Plan) : SegmentCadencedHost.Policy where
  cooldown := cooldown
  chunkAt offset := (plan.find? (·.1 == offset)).map (·.2)

private def i2cPlan : Plan :=
  let bits := registerReadTX Wire.fixtureRequest
  [(0, ⟨pack (bits.take 32), 31⟩), (32, ⟨pack (bits.drop 32), 3⟩)]

private def rowQuiet (rows : List Row) : Nat :=
  rows.foldl (fun bound row => match row with
    | .cell instruction => max bound (SegmentPolicyTiming.requiredQuiet instruction)
    | _ => bound) 0

/-- Check the numeric timing premises on every reached snapshot, including
    the last clock; the finite packet list gives the receive-only premise. -/
private def checkHorizon (registered : Bool) (rows : List Row) (cooldown : Nat) (plan : Plan)
    (states : List (SegmentCausal.State 1 Nat P)) : IO Unit := do
  let policy := fixturePolicy cooldown plan
  for row in rows do
    match row with
    | .cell (.stream _ none) =>
      requireFixture plan.isEmpty "Receive-only stream requires an empty TX plan"
    | .cell instruction =>
      requireFixture (SegmentPolicyTiming.requiredQuiet instruction ≤ cooldown)
        "Host cooldown did not cover the row's TX-quiet time"
    | _ => pure ()
  let count := states.length - 1
  for (s, k) in states.zipIdx do
    match (s.core (.base .phase)).toNat with
    | 1 =>
      let pc := (s.core (.base .pc)).toNat
      let slots := (s.core (.base .remaining)).toNat
      let required := match rows[pc]? with
        | some (.cell instruction) => max 1 (SegmentPolicyTiming.requiredClocks slots (cooldown + 1) instruction)
        | _ => 1
      requireFixture (required ≤ count - k) s!"FETCH at clock {k} had insufficient lookahead"
    | 2 =>
      requireFixture (cooldown + 2 ≤ count - k) s!"Reservation at clock {k} had insufficient lookahead"
      let ports : Values StreamingReady.Core.Output := SegmentCausal.status registered s
      if ports .waitingTX == 1#1 && cooldown ≤ s.host then
        let offset := (ports .txAccepted).toNat
        let some chunk := policy.chunkAt offset
          | throw (IO.userError s!"Missing TX chunk at offset {offset} and clock {k}")
        requireFixture (offset + chunk.sizeMinusOne.val + 1 ≤ (ports .total).toNat)
          s!"TX chunk at offset {offset} exceeded the START budget"
    | _ => pure ()

private def exportBits (ports : Values StreamingReady.Core.Output) : List Bool :=
  if ports .rxQueued = 0#4 then []
  else
    let width := (ports .rxBits).toNat
    (List.range width).map fun j => (ports .rxData).getLsbD (width - (j + 1))

private def traceBits (registered : Bool) (host : SegmentCausal.Host H) (peer : SegmentCausal.Peer P)
    (states : List (SegmentCausal.State 1 H P)) : SegmentTrace.Bits :=
  states.foldl (fun gathered s => gathered.append
    (SegmentTrace.edge (SegmentCausal.input registered host peer s) s.core)) {}

private def readI2C (registered : Bool) (target : Target) : IO Json := do
  let rows := registerReadRows .standard
  let words := registerReadImage.words
  let machine := SegmentClockTable.compile 1 supported registered
  let installed := install machine words {} 3
  requireFixture (installed.read (.base .valid) == 1#1 && installed.read (.base .generation) == 1#16 &&
    installed.read (.base .count) == BitVec.ofNat 7 words.length &&
    (words.zipIdx).all (fun (word, index) => installed.read (.base (.word (BitVec.ofNat 6 index))) == word))
    "I2C image installation did not follow the core word-store commands"
  let started := start machine installed 36 3
  let opened : SegmentCausal.State 1 Nat TargetState :=
    ⟨fun r => started.read r, 0, Pinwheel.I2C.RegisterReadPeer.initial⟩
  requireFixture (opened.core (.base .phase) == 1#3 && opened.core (.base .total) == 36#16 &&
    opened.core (.base .generation) == 1#16 && opened.core (.base .transfer) == 1#16)
    "I2C owner failed to start"
  let cooldown := rowQuiet rows
  let host := SegmentCadencedHost.host (fixturePolicy cooldown i2cPlan)
  let peer := SegmentCausalI2C.peer target
  let states := SegmentClockTable.history supported registered host peer opened 1600
  checkHorizon registered rows cooldown i2cPlan states
  let some edge := states.findIdx? (fun s => s.core (.base .phase) == 5#3 || s.core (.base .phase) == 6#3)
    | throw (IO.userError "I2C independent parties did not reach a retained terminal edge")
  let retired := (states.drop edge).head?.getD opened
  let wireEnd := (states.drop (edge + 1)).head?.getD opened
  let drained := states.getLast?.getD opened
  let sent := traceBits registered host peer (states.take edge)
  let returned := states.flatMap (fun s => exportBits (SegmentCausal.status registered s))
  let expected := expectedRegisterRead Wire.fixtureRequest target
  let requested := registerReadTX Wire.fixtureRequest
  requireFixture (sent.tx == requested.take target.stopAfter && sent.rx == expected && returned == expected)
    s!"I2C escaped expected TX/RX order for NACK {target.nack}"
  requireFixture (retired.core (.base .phase) == 5#3 && retired.core (.base .txConsumed) ==
    BitVec.ofNat 16 sent.tx.length && retired.core (.base .rxProduced) == BitVec.ofNat 16 expected.length &&
    (retired.core (.base .txAccepted)).toNat == (if target.nack.isSome then 32 else 36))
    "I2C terminal phase, reservation count or accepted offset changed"
  requireFixture (drained.core (.base .phase) == 5#3 && drained.core (.base .generation) == 1#16 &&
    drained.core (.base .transfer) == 1#16 && drained.core (.base .rxCount) == 0#4 &&
    drained.core (.base .rxPopped) == BitVec.ofNat 16 expected.length &&
    drained.core (.base .txCount) == 0#4 && drained.core (.base .txValid) == 0#6 &&
    drained.core .txClosed == BitVec.ofBool target.nack.isSome)
    "I2C post-drain owner or unspent TX accounting changed"
  -- The terminal edge releases SDA. The peer observes that release on the following edge.
  requireFixture (wireEnd.peer.stopped && wireEnd.peer.slots == target.stopAfter &&
    wireEnd.peer.starts == target.startCount && projectRegisterRead Wire.fixtureRequest returned == some target.outcome)
    s!"I2C target or verdict differed after clock {edge}: {repr wireEnd.peer}; expected {target.stopAfter} slots, {target.startCount} starts and {repr target.outcome}; decoded {repr (projectRegisterRead Wire.fixtureRequest returned)}"
  return Json.mkObj [
    ("scenario", toJson (target.nack.map Fin.val)),
    ("clocks_from_start", toJson edge),
    ("clock_stretch", toJson target.initialStretch.val),
    ("tx_accepted", toJson (retired.core (.base .txAccepted)).toNat),
    ("tx_reserved", toJson sent.tx),
    ("rx_captured", toJson sent.rx),
    ("rx_exported", toJson returned),
    ("generation", toJson (drained.core (.base .generation)).toNat),
    ("transfer", toJson (drained.core (.base .transfer)).toNat)]

private structure SwdState where
  rises : Nat := 0
  clock : Bool := false
  drive : Option Bool := none
  request : List Bool := []

/-- A reply-only peer advances on the resolved SWCLK edges. It has no
    access to the core PC, host offers, fetches or capture strobes. -/
private def swdPeer (reply : List Bool) : SegmentCausal.Peer SwdState where
  resolve peer pads :=
    let clock := pads.enabled.getLsbD 0 && pads.levels.getLsbD 0
    let data := if pads.enabled.getLsbD 1 then pads.levels.getLsbD 1 else peer.drive.getD true
    BitVec.ofBool data ++ BitVec.ofBool clock
  next peer raw :=
    let clock := raw.getLsbD 0
    let rise := !peer.clock && clock
    let request := if rise && peer.rises < 8 then peer.request ++ [raw.getLsbD 1] else peer.request
    let rises := peer.rises + if rise then 1 else 0
    let drive := if peer.clock && !clock then
      if 9 ≤ rises && request == Pinwheel.Program.StreamingSWDBranching.requestBits then reply[rises - 9]? else none
      else peer.drive
    ⟨rises, clock, drive, request⟩

private def readSWD (registered : Bool) (short : Bool) : IO Json := do
  let expected := if short then [false, true, false] else Pinwheel.Program.StreamingSWD.replyBits 0x96a65ac3
  let expectedClockPairs := if short then 21 else 54
  let rows := Pinwheel.Program.StreamingSWDBranching.rows 3 .standard
  let compiled := Pinwheel.Program.StreamingSWDBranching.image .standard
  let machine := SegmentClockTable.compile 1 supported registered
  let installed := install machine compiled.words Pinwheel.Program.StreamingSWD.idlePins 2
  requireFixture (installed.read (.base .valid) == 1#1 && installed.read (.base .generation) == 1#16 &&
    installed.read (.base .count) == BitVec.ofNat 7 compiled.words.length &&
    (compiled.words.zipIdx).all (fun (word, index) => installed.read (.base (.word (BitVec.ofNat 6 index))) == word))
    "SWD image installation did not follow the core word-store commands"
  let started := start machine installed 0 2
  let opened : SegmentCausal.State 1 Nat SwdState := ⟨fun r => started.read r, 0, {}⟩
  let cooldown := rowQuiet rows
  let host := SegmentCadencedHost.host (fixturePolicy cooldown [])
  let peer := swdPeer expected
  let states := SegmentClockTable.history supported registered host peer opened 600
  checkHorizon registered rows cooldown [] states
  let some edge := states.findIdx? (fun s => s.core (.base .phase) == 5#3 || s.core (.base .phase) == 6#3)
    | throw (IO.userError "SWD independent parties did not reach a retained terminal edge")
  let retired := (states.drop edge).head?.getD opened
  let drained := states.getLast?.getD opened
  let active := states.take edge
  let sent := traceBits registered host peer active
  let returned := states.flatMap (fun s => exportBits (SegmentCausal.status registered s))
  requireFixture (sent.tx.isEmpty && sent.rx == expected && returned == expected)
    "SWD reply did not survive exact chronological capture and drain"
  requireFixture (active.all (fun s => !(s.peer.drive.isSome && (SegmentCausal.pads registered s).enabled.getLsbD 1)) &&
    retired.peer.rises == expectedClockPairs && retired.peer.drive.isNone && !retired.peer.clock &&
    retired.peer.request == Pinwheel.Program.StreamingSWDBranching.requestBits)
    "SWD turnaround, contention or response length changed"
  requireFixture (retired.core (.base .phase) == 5#3 && drained.core (.base .generation) == 1#16 &&
    drained.core (.base .transfer) == 1#16 && drained.core (.base .txAccepted) == 0#16 &&
    drained.core (.base .txConsumed) == 0#16 && drained.core (.base .rxCount) == 0#4 &&
    drained.core (.base .rxPopped) == BitVec.ofNat 16 expected.length &&
    Pinwheel.Program.StreamingSWDBranching.decode returned == (if short then .wait else .ok 0x96a65ac3))
    "SWD post-drain owner, receipt or decoder changed"
  return Json.mkObj [("status", toJson (if short then "wait" else "ok")), ("clocks_from_start", toJson edge),
    ("wire_clock_pairs", toJson retired.peer.rises), ("request", toJson retired.peer.request),
    ("rx_captured", toJson sent.rx), ("rx_exported", toJson returned)]

def main : IO Unit := do
  let cases : List Target := [⟨0x96, none, 5⟩, ⟨0x96, some 0, 5⟩, ⟨0x96, some 1, 0⟩, ⟨0x96, some 2, 0⟩]
  let direct ← cases.mapM (readI2C false)
  let registered ← cases.mapM (readI2C true)
  let swdDirect ← [false, true].mapM (readSWD false)
  let swdRegistered ← [false, true].mapM (readSWD true)
  requireFixture (direct.map Json.compress == registered.map Json.compress)
    "Causal policies changed observable behavior across instruction stores"
  requireFixture (swdDirect.map Json.compress == swdRegistered.map Json.compress)
    "Causal SWD reply changed across instruction stores"
  IO.println (Json.mkObj [("schema", toJson "pinwheel.ready-causal-policies.v1"),
    ("i2c", Json.arr direct.toArray), ("swd", Json.arr swdDirect.toArray),
    ("stores", toJson ["direct", "registered"])]).compress
