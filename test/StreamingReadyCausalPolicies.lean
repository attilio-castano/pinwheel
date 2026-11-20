import Lean.Data.Json
import Pinwheel.Hardware.StreamingReady.SegmentCadencedHost
import Pinwheel.Hardware.StreamingReady.SegmentCausalI2C
import Pinwheel.Hardware.StreamingReady.SegmentClockTable
import Pinwheel.Hardware.StreamingReady.SegmentPolicyTiming
import Pinwheel.Hardware.StreamingReady.SegmentUARTTx
import Pinwheel.Program.StreamingJTAG
import Pinwheel.Program.StreamingReadyDuplex
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

private def upload (machine : SegmentClockTable.Machine 1) (initial : SegmentClockTable.Table (Register 1))
    (words : List (BitVec 64)) (idle : Pins) (raw : BitVec 2) :
    SegmentClockTable.Table (Register 1) :=
  let edge (before : SegmentClockTable.Table (Register 1)) (i : Values Input) :=
    machine.edge i (fun r => before.read r)
  let commit : Values Input := fun port => match port with
    | .command => 2
    | .count => BitVec.ofNat 7 words.length
    | .idleLevels => idle.levels
    | .idleEnabled => idle.enabled
    | .rawInputs => raw
    | _ => 0
  let loaded := (words.zipIdx).foldl (fun before (word, address) => edge before (writeWord raw address word)) initial
  edge loaded commit

private def install (machine : SegmentClockTable.Machine 1) (words : List (BitVec 64)) (idle : Pins) (raw : BitVec 2) :
    SegmentClockTable.Table (Register 1) :=
  let cold : Values Input := fun port => match port with
    | .initialize => 1
    | _ => 0
  upload machine (machine.edge cold (fun _ => 0)) words idle raw

private def start (machine : SegmentClockTable.Machine 1) (initial : SegmentClockTable.Table (Register 1)) (budget : Nat)
    (raw : BitVec 2) : SegmentClockTable.Table (Register 1) :=
  let offer : Values Input := fun port => match port with
    | .command => 3
    | .expectedGeneration => initial.read (.base .generation)
    | .startCount => BitVec.ofNat 16 budget
    | .rawInputs => raw
    | _ => 0
  machine.edge offer (fun r => initial.read r)

private def releaseOwner (machine : SegmentClockTable.Machine 1) (state : Values (Register 1)) (raw : BitVec 2) :
    SegmentClockTable.Table (Register 1) :=
  let release : Values Input := fun p => match p with
    | .command => 4
    | .expectedGeneration => state (.base .generation)
    | .expectedTransfer => state (.base .transfer)
    | .rawInputs => raw
    | _ => 0
  machine.edge release state

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
    the last clock. -/
private def checkHorizon (registered : Bool) (rows : List Row) (cooldown : Nat) (plan : Plan)
    (states : List (SegmentCausal.State 1 Nat P)) : IO Unit := do
  let policy := fixturePolicy cooldown plan
  for row in rows do
    match row with
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

private inductive Duplex
  | spi (mode : Pinwheel.Program.StreamingSPI.Mode)
  | jtag

private def Duplex.name : Duplex → String
  | .spi .mode0 => "spi-mode0"
  | .spi .mode2 => "spi-mode2"
  | .jtag => "jtag"

private def Duplex.rows (protocol : Duplex) (duration : Fin 256) (count : BitVec 16) : List Row :=
  match protocol with
  | .spi mode => Pinwheel.Program.StreamingReadyDuplex.spiRows mode duration count
  | .jtag => Pinwheel.Program.StreamingReadyDuplex.jtagRows duration count

private def Duplex.image (protocol : Duplex) (duration : Fin 256) (count : BitVec 16) :
    Except String (Image (protocol.rows duration count) count.toNat) :=
  match protocol with
  | .spi mode => Pinwheel.Program.StreamingReadyDuplex.spi mode duration count
  | .jtag => Pinwheel.Program.StreamingReadyDuplex.jtag duration count

private def Duplex.idle : Duplex → Pins
  | .spi mode => Pinwheel.Program.StreamingSPI.idlePins mode
  | .jtag => ⟨0, 7⟩

private def Duplex.clockActive (protocol : Duplex) (pins : Pins) : Bool :=
  pins.levels.getLsbD 1 != protocol.idle.levels.getLsbD 1

private def Duplex.preamble : Duplex → Nat
  | .spi _ => 0
  | .jtag => 9

private structure DuplexPeerState where
  count : Nat := 0
  active : Bool := false

/-- The target indexes its reply only by physical leading clock edges.
    The second raw input loops back the clock, and the stream samples input zero. -/
private def duplexPeer (protocol : Duplex) (reply : List Bool) : SegmentCausal.Peer DuplexPeerState where
  resolve state pins :=
    let response := protocol.preamble ≤ state.count && reply[state.count - protocol.preamble]?.getD false
    BitVec.ofBool (protocol.clockActive pins) ++ BitVec.ofBool response
  next state raw :=
    let clock := raw.getLsbD 1
    ⟨state.count + if !state.active && clock then 1 else 0, clock⟩

private def duplexBits (count : Nat) : List Bool × List Bool :=
  ((List.range count).map fun n => (7 * n + 3) % 11 < 5,
   (List.range count).map fun n => (5 * n + 1) % 13 < 6)

private def readDuplex (registered : Bool) (protocol : Duplex) (slow : Bool)
    (omitSecond := false) : IO (Json × Option (SegmentClockTable.Table (Register 1))) := do
  let duration : Fin 256 := 3
  let count : BitVec 16 := 33
  let (tx, rx) := duplexBits count.toNat
  let cut := if slow then 17 else 32
  let chunk (bits : List Bool) : IO SegmentCadencedHost.Chunk := do
    if h : bits.length - 1 < 32 then pure ⟨pack bits, ⟨bits.length - 1, h⟩⟩
    else throw (IO.userError "Invalid duplex TX chunk")
  let first ← chunk (tx.take cut)
  let last ← chunk (tx.drop cut)
  let plan := if omitSecond then [(0, first)] else [(0, first), (cut, last)]
  let rows := protocol.rows duration count
  let .ok image := protocol.image duration count
    | throw (IO.userError "Checked duplex compilation failed")
  let machine := SegmentClockTable.compile 1 supported registered
  let installed := install machine image.words protocol.idle 0
  requireFixture (installed.read (.base .valid) == 1#1 &&
    installed.read (.base .count) == BitVec.ofNat 7 image.words.length &&
    (image.words.zipIdx).all (fun (word, index) => installed.read (.base (.word (BitVec.ofNat 6 index))) == word))
    "Duplex image installation differed from its checked plan"
  let started := start machine installed count.toNat 0
  let opened : SegmentCausal.State 1 Nat DuplexPeerState := ⟨fun r => started.read r, 0, {}⟩
  let cooldown := rowQuiet rows + if slow then 5 else 0
  let host := SegmentCadencedHost.host (fixturePolicy cooldown plan)
  let peer := duplexPeer protocol rx
  let states := SegmentClockTable.history supported registered host peer opened 1000
  if omitSecond then
    let refused ← try
      checkHorizon registered rows cooldown plan states
      pure false
    catch
      | .userError reason => pure (reason.startsWith s!"Missing TX chunk at offset {cut} ")
      | error => throw error
    let parked := states.getLast?.getD opened
    let progress := traceBits registered host peer states
    requireFixture (refused && progress.tx == tx.take cut && progress.rx == rx.take cut &&
      SegmentCausal.status registered parked .waitingTX == 1#1 &&
      parked.core (.base .phase) == 2#3 && !protocol.clockActive (SegmentCausal.pads registered parked) &&
      parked.core (.base .generation) == 1#16 && parked.core (.base .transfer) == 1#16)
      "Missing TX chunk did not reject the horizon and preserve the live owner"
    return ⟨Json.mkObj [("protocol", toJson protocol.name), ("missing_tx_offset", toJson cut)], none⟩
  checkHorizon registered rows cooldown plan states
  let some terminal := states.findIdx? (fun s =>
    s.core (.base .phase) == 5#3 || s.core (.base .phase) == 6#3)
    | throw (IO.userError s!"{protocol.name} did not reach its terminal edge")
  let retired := states[terminal]?.getD opened
  let drained := states.getLast?.getD opened
  let active := states.take terminal
  let sent := traceBits registered host peer active
  let returned := states.flatMap (fun s => exportBits (SegmentCausal.status registered s))
  let pins := (states.take (terminal + 1)).map (SegmentCausal.pads registered)
  let edges := (pins.zip (pins.drop 1)).zipIdx
  let leading := edges.filterMap fun ((old, next), k) =>
    if !protocol.clockActive old && protocol.clockActive next then some (k, next) else none
  let trailing := edges.filterMap fun ((old, next), k) =>
    if protocol.clockActive old && !protocol.clockActive next then some k else none
  let data := (leading.drop protocol.preamble).take count.toNat
  let widths := (data.zip ((trailing.drop protocol.preamble).take count.toNat)).map
    (fun ((edge, _), leave) => leave - edge)
  requireFixture (sent.tx == tx && sent.rx == rx && returned == rx &&
    data.map (·.2.levels.getLsbD 0) == tx && widths == List.replicate count.toNat 4)
    s!"{protocol.name} changed wire data, capture order, or active clock width"
  let waiting := (active.zip (states.drop 1)).filter fun (old, _) =>
    SegmentCausal.status registered old .waitingTX == 1#1
  let offsets := waiting.map fun (s, _) => (SegmentCausal.status registered s .txAccepted).toNat
  requireFixture (offsets == List.replicate (cooldown + 1) 0 ++ List.replicate (cooldown + 1) cut &&
    waiting.all (fun (old, next) =>
      let before := SegmentCausal.pads registered old
      let after := SegmentCausal.pads registered next
      !protocol.clockActive before && before.levels == after.levels && before.enabled == after.enabled))
    s!"{protocol.name} failed to park at its public refill boundary"
  let tms := leading.map (·.2.levels.getLsbD 2)
  match protocol with
  | .spi _ =>
    let selects := edges.filterMap (fun ((old, next), _) =>
      if old.levels.getLsbD 2 != next.levels.getLsbD 2 then some (next.levels.getLsbD 2) else none)
    requireFixture (selects == [false, true] && leading.length == count.toNat &&
      tms == List.replicate count.toNat false) "SPI chip select interrupted the transfer"
  | .jtag =>
    let expected := Pinwheel.Program.StreamingJTAG.beforeScan duration ++
      List.replicate (count.toNat - 1) false ++ [true] ++ Pinwheel.Program.StreamingJTAG.afterScan duration
    requireFixture (tms == expected &&
      decide ((Pinwheel.Program.StreamingJTAG.walk .reset tms).1 = .idle)) "JTAG changed its TAP route"
  requireFixture (retired.peer.count == leading.length && leading.length == trailing.length &&
    retired.core (.base .phase) == 5#3 && drained.core (.base .generation) == 1#16 &&
    drained.core (.base .transfer) == 1#16 && drained.core (.base .txAccepted) == count &&
    drained.core (.base .txConsumed) == count && drained.core (.base .rxPopped) == count &&
    drained.core (.base .rxCount) == 0#4)
    s!"{protocol.name} changed terminal ownership or clock accounting"
  let freed := releaseOwner machine drained.core (SegmentCausal.resolved registered peer drained)
  requireFixture (freed.read (.base .phase) == 0#3 && freed.read (.base .valid) == 1#1)
    s!"{protocol.name} refused matched RELEASE after drain"
  return ⟨Json.mkObj [ ("protocol", toJson protocol.name), ("cooldown", toJson cooldown),
    ("tx_chunk_boundary", toJson cut), ("wire_clocks", toJson leading.length),
    ("clocks_from_start", toJson terminal), ("parked_edges", toJson waiting.length),
    ("tx", toJson sent.tx), ("rx", toJson returned)], some freed⟩

private def uartTx (registered : Bool) (predecessor : SegmentClockTable.Table (Register 1)) (mutated : Bool) : IO Json := do
  let hold : Fin 253 := 12
  let byte : BitVec 8 := 0xa5
  let config := Pinwheel.Program.StreamingReadyUARTTx.config hold
  let rows := Pinwheel.Program.StreamingReadyUARTTx.rows hold byte
  let first := Row.cell (.pulse (Pinwheel.Program.StreamingReadyUARTTx.cell 13 false))
  let (rows, words) ← if mutated then do
      let rows := rows.set 0 first
      let .ok image := compile rows 0
        | throw (IO.userError "UART TX mutation did not compile through the ordinary API")
      pure (rows, image.words)
    else do
      let .ok image := Pinwheel.Program.StreamingReadyUARTTx.image hold byte
        | throw (IO.userError "UART TX holdout did not compile through the ordinary API")
      pure (rows, image.words)
  let idle := Pinwheel.Program.StreamingReadyUARTTx.pins true
  let machine := SegmentClockTable.compile 1 supported registered
  let installed := upload machine predecessor words idle 0
  let previousGeneration := predecessor.read (.base .generation)
  let previousTransfer := predecessor.read (.base .transfer)
  let generation := previousGeneration + 1
  let transfer := previousTransfer + 1
  requireFixture (predecessor.read (.base .phase) == 0#3 && installed.read (.base .phase) == 0#3 &&
    installed.read (.base .valid) == 1#1 && installed.read (.base .generation) == generation &&
    installed.read (.base .transfer) == previousTransfer &&
    installed.read (.base .count) == BitVec.ofNat 7 words.length &&
    (words.zipIdx).all (fun (word, index) => installed.read (.base (.word (BitVec.ofNat 6 index))) == word))
    "SPI RELEASE did not allow a new UART TX COMMIT with continuous owner tags"
  let stale : Values Input := fun p => match p with
    | .command => 3
    | .expectedGeneration => previousGeneration
    | _ => 0
  let stillFree := machine.edge stale (fun r => installed.read r)
  requireFixture (stillFree.read (.base .phase) == 0#3 && stillFree.read (.base .transfer) == previousTransfer)
    "Stale SPI generation started a UART TX owner"
  let started := start machine stillFree 0 0
  requireFixture (started.read (.base .phase) == 1#3 && started.read (.base .transfer) == transfer)
    "UART TX START did not acquire the expected new owner"
  let opened : SegmentCausal.State 1 Nat Unit := ⟨fun r => started.read r, 0, ()⟩
  let cooldown := rowQuiet rows
  let host := SegmentCadencedHost.host (fixturePolicy cooldown [])
  let peer : SegmentCausal.Peer Unit := ⟨fun _ _ => 0, fun _ _ => ()⟩
  let states := SegmentClockTable.history supported registered host peer opened (config.frameCycles + 6)
  checkHorizon registered rows cooldown [] states
  let observed := (states.drop 1).map (SegmentCausal.pads registered)
  let mismatch := (observed.zipIdx.find? fun (pad, k) =>
    pad != Pinwheel.Program.StreamingReadyUARTTx.pins (Pinwheel.UART.expected config byte k)).map Prod.snd
  requireFixture (mismatch == if mutated then some config.cycles else none)
    "UART TX waveform oracle did not identify the exact held-bit mismatch"
  let terminal := states.findIdx? (fun s => s.core (.base .phase) == 5#3 || s.core (.base .phase) == 6#3)
  requireFixture (terminal == some (config.frameCycles + (if mutated then 2 else 1)))
    "UART TX terminal edge differed from its independent waveform duration"
  let retained := states.getLast?.getD opened
  requireFixture (retained.core (.base .phase) == 5#3 && retained.core (.base .generation) == generation &&
    retained.core (.base .transfer) == transfer && retained.core (.base .txAccepted) == 0#16 &&
    retained.core (.base .txConsumed) == 0#16 && retained.core (.base .rxProduced) == 0#16)
    "UART TX changed ownership or reserved host data during its authored frame"
  let released := releaseOwner machine retained.core 0
  requireFixture (released.read (.base .phase) == 0#3 && released.read (.base .valid) == 1#1 &&
    released.read (.base .levels) == idle.levels && released.read (.base .enabled) == idle.enabled)
    "UART TX did not release the warm owner and hold its configured idle pad"
  return Json.mkObj [("cycles_per_bit", toJson config.cycles), ("byte", toJson byte.toNat),
    ("terminal_clock", toJson terminal), ("first_wire_mismatch", toJson mismatch),
    ("generation", toJson generation.toNat), ("transfer", toJson transfer.toNat)]

def main : IO Unit := do
  let cases : List Target := [⟨0x96, none, 5⟩, ⟨0x96, some 0, 5⟩, ⟨0x96, some 1, 0⟩, ⟨0x96, some 2, 0⟩]
  let direct ← cases.mapM (readI2C false)
  let registered ← cases.mapM (readI2C true)
  let swdDirect ← [false, true].mapM (readSWD false)
  let swdRegistered ← [false, true].mapM (readSWD true)
  let duplex := ([Duplex.spi .mode0, .spi .mode2, .jtag]).flatMap (fun p => [(p, false), (p, true)])
  let duplexDirect ← duplex.mapM (fun (p, slow) => readDuplex false p slow)
  let duplexRegistered ← duplex.mapM (fun (p, slow) => readDuplex true p slow)
  let missingDirect ← readDuplex false (.spi .mode0) false true
  let missingRegistered ← readDuplex true (.spi .mode0) false true
  let some (_, some precedingDirect) := duplexDirect.head?
    | throw (IO.userError "Direct UART TX has no released SPI predecessor")
  let some (_, some precedingRegistered) := duplexRegistered.head?
    | throw (IO.userError "Registered UART TX has no released SPI predecessor")
  let uartDirect ← [false, true].mapM (uartTx false precedingDirect)
  let uartRegistered ← [false, true].mapM (uartTx true precedingRegistered)
  requireFixture (direct.map Json.compress == registered.map Json.compress)
    "Causal policies changed observable behavior across instruction stores"
  requireFixture (swdDirect.map Json.compress == swdRegistered.map Json.compress)
    "Causal SWD reply changed across instruction stores"
  requireFixture (duplexDirect.map (·.1.compress) == duplexRegistered.map (·.1.compress))
    "Causal full-duplex behavior changed across instruction stores"
  requireFixture (missingDirect.1.compress == missingRegistered.1.compress)
    "Causal missing-credit control changed across instruction stores"
  requireFixture (uartDirect.map Json.compress == uartRegistered.map Json.compress)
    "Warm UART TX waveform or mutation changed across instruction stores"
  IO.println (Json.mkObj [("schema", toJson "pinwheel.ready-causal-policies.v3"),
    ("i2c", Json.arr direct.toArray), ("swd", Json.arr swdDirect.toArray),
    ("duplex", Json.arr (duplexDirect.map Prod.fst).toArray), ("duplex_missing_credit", missingDirect.1),
    ("uart_tx", Json.arr uartDirect.toArray),
    ("stores", toJson ["direct", "registered"])]).compress
