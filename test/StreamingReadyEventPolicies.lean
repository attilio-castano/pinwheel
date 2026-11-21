import Lean.Data.Json
import Pinwheel.Hardware.StreamingReady.SegmentCadencedHost
import Pinwheel.Hardware.StreamingReady.SegmentClockTable
import Pinwheel.Program.StreamingReadyReceiveImages
import Pinwheel.Program.StreamingCANCodec
import Pinwheel.Program.StreamingPS2Spec

/-! Independent peers drive the raw pins from their own clock, while a
    command-zero host drains using the public ownership tags. -/
open Lean
open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady SegmentCore
open Pinwheel.Program.StreamingReadySegments
open Pinwheel.Program.StreamingReadyReceiveImages

private abbrev Input := StreamingReady.Core.Input
private abbrev State := SegmentCausal.State 1 Nat Nat
private abbrev Table := SegmentClockTable.Table (Register 1)

private theorem depth : (1 : Nat) = 1 ∨ (1 : Nat) = 2 := .inl rfl

private def requireFixture (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def launch (machine : SegmentClockTable.Machine 1) (words : List (BitVec 64)) (idle : BitVec 2) :
    Table × Table :=
  let edge (before : Table) (input : Values Input) := machine.edge input (fun r => before.read r)
  let cold : Values Input := fun port => match port with
    | .initialize => 1
    | _ => 0
  let write (before : Table) (word : BitVec 64) (address : Nat) := edge before (fun port => match port with
    | .command => 1
    | .word => word
    | .address => BitVec.ofNat 6 address
    | .rawInputs => idle
    | _ => 0)
  let reset := machine.edge cold (fun _ => 0)
  let loaded := words.zipIdx.foldl (fun before (w, pos) => write before w pos) reset
  let installed := edge loaded (fun port => match port with
    | .command => 2
    | .count => BitVec.ofNat 7 words.length
    | .rawInputs => idle
    | _ => 0)
  let started := edge installed (fun port => match port with
    | .command => 3
    | .expectedGeneration => installed.read (.base .generation)
    | .rawInputs => idle
    | _ => 0)
  (installed, started)

private def peer (wire : Nat → BitVec 2) : SegmentCausal.Peer Nat where
  resolve tick _ := wire tick
  next tick _ := tick + 1

private def host := SegmentCadencedHost.host ⟨0, fun _ => none⟩

private def exported (registered : Bool) (s : State) : List Bool :=
  let ports : Values StreamingReady.Core.Output := SegmentCausal.status registered s
  if ports .rxQueued = 0#4 then []
  else
    let width := (ports .rxBits).toNat
    (List.range width).map (fun j => (ports .rxData).getLsbD (width - (j + 1)))

private def terminal (s : State) : Bool :=
  s.core (.base .phase) == 5#3 || s.core (.base .phase) == 6#3

private def runFixture (registered : Bool) (name : String) (words : List (BitVec 64)) (idle : BitVec 2)
    (wire : Nat → BitVec 2) (limit : Nat) (expected : List Bool) (cuts : List Nat)
    (ending : Option (Nat × BitVec 3)) : IO Json := do
  let machine := SegmentClockTable.compile 1 depth registered
  let (installed, initial) := launch machine words idle
  requireFixture (installed.read (.base .valid) == 1#1 && installed.read (.base .generation) == 1#16 &&
    (words.zipIdx).all (fun (word, index) => installed.read (.base (.word (BitVec.ofNat 6 index))) == word))
    s!"{name}: cold upload differs from checked words"
  let opened : State := ⟨fun r => initial.read r, 0, 0⟩
  requireFixture (opened.core (.base .phase) == 1#3 && opened.core (.base .transfer) == 1#16)
    s!"{name}: owner failed to start"
  let target := peer wire
  let states := SegmentClockTable.history depth registered host target opened limit
  let first := states.findIdx? terminal
  let received := states.zipIdx.flatMap (fun (s, k) =>
    (SegmentTrace.edge (SegmentCausal.input registered host target s) s.core).rx.map (fun bit => (k, bit)))
  let returned := states.flatMap (exported registered)
  let final := states.getLast?.getD opened
  requireFixture (states.all fun s => s.core (.base .generation) == 1#16 && s.core (.base .transfer) == 1#16 &&
    (SegmentCausal.pads registered s).enabled == 0#3 && s.core (.base .txAccepted) == 0#16 &&
    s.core (.base .txConsumed) == 0#16 && (s.core (.base .rxCount)).toNat ≤ 1)
    s!"{name}: output drive, queue bound or custody changed"
  requireFixture (received.map Prod.fst == cuts && received.map Prod.snd == expected && returned == expected)
    s!"{name}: capture/export differed, captured indices {received.map Prod.fst}, first terminal {first}"
  requireFixture (final.core (.base .rxCount) == 0#4 && final.core (.base .rxPopped) == BitVec.ofNat 16 expected.length)
    s!"{name}: RX did not drain to the acknowledged offset"
  match ending with
  | none =>
    requireFixture (first.isNone && final.core (.base .phase) == 7#3)
      s!"{name}: no-event wait did not keep its live owner"
  | some (edge, phase) =>
    requireFixture (first == some edge && final.core (.base .phase) == phase)
      s!"{name}: expected terminal {edge} in phase {phase}, observed {first} in phase {final.core (.base .phase)}"
  return Json.mkObj [("case", toJson name), ("first_terminal", toJson first),
    ("capture_edges", toJson cuts), ("rx", toJson returned)]

private def receiveCAN (registered : Bool) (bad : Bool) : IO Json := do
  let bits := if bad then Pinwheel.Program.StreamingCAN.badCRCBits 0x321 0x96
    else Pinwheel.Program.StreamingCAN.frameBits 0x321 0x96
  requireFixture (Pinwheel.Program.StreamingCAN.decodeFrame bits == (if bad then none else some (0x321, 0x96)))
    "CAN independent decoder changed"
  let fall := 326
  let boundary (slot : Nat) := fall + 32 * slot + if slot == 0 then 0 else slot % 5
  let wire (tick : Nat) := BitVec.ofNat 2 (if tick < fall then 1 else
    let slot := min 63 ((tick - fall) / 32)
    (bits[if tick < boundary slot then slot - 1 else slot]?.getD true).toNat)
  let cuts := (Pinwheel.Program.StreamingCANCore.apertures fall).map (· + 2)
  runFixture registered (if bad then "can-bad-crc" else "can-valid") can.words 1 wire (fall + 2062)
    bits cuts (some (fall + 2054, 5))

private def receivePS2 (registered : Bool) (bad : Bool) : IO Json := do
  let bits := if bad then Pinwheel.Program.StreamingPS2.badParityBits 0xB2
    else Pinwheel.Program.StreamingPS2.frameBits 0xB2
  requireFixture (Pinwheel.Program.StreamingPS2.decodeFrame bits == (if bad then none else some 0xB2))
    "PS/2 independent decoder changed"
  let falls := (List.range 11).map fun slot => 322 + 320 * slot
  let wire (tick : Nat) :=
    let fall := 322
    let slot := (tick - fall) / 320
    let low := if slot % 2 == 0 then 120 else 200
    let clock := tick < fall || 11 ≤ slot || low ≤ (tick - fall) % 320
    BitVec.ofBool (bits[slot]?.getD true) ++ BitVec.ofBool clock
  let doneAt := 322 + 320 * 10 + 221
  runFixture registered (if bad then "ps2-bad-parity" else "ps2-mixed-periods") ps2.words 3 wire (doneAt + 7)
    bits (falls.map (· + 2)) (some (doneAt, 5))

private def receiveUART (registered : Bool) (caseId : Nat) : IO Json := do
  let p : Pinwheel.Program.StreamingUART.Profile := ⟨8, 1⟩
  let .ok image := uart p | throw (IO.userError "UART profile failed checked compilation")
  let data := (List.range 8).map (fun k => (0x53#8).getLsbD k)
  let fall := 301
  let wire (tick : Nat) : BitVec 2 :=
    let bit := if tick < fall || caseId == 3 then true
      else if caseId == 1 then tick != fall
      else ([false] ++ data ++ [caseId != 2])[(tick - fall) / (4 * p.Q)]?.getD (caseId != 2)
    BitVec.ofBool bit ++ 0#1
  let captures := if caseId == 0 || caseId == 2 then data else []
  let cuts := (List.range captures.length).map (fun k => fall + (6 + 4 * k) * p.Q + 2)
  let ending := match caseId with
    | 0 => some (fall + 38 * p.Q + 4, 5)
    | 1 => some (fall + 2 * p.Q + 3, 6)
    | 2 => some (fall + 38 * p.Q + 3, 6)
    | _ => none
  let name := ["uart-data", "uart-false-start", "uart-bad-stop", "uart-no-event"][caseId]?.getD "uart"
  runFixture registered name image.words 2 wire (fall + 38 * p.Q + 14) captures cuts ending

private def scenarios (registered : Bool) : IO (List Json) := do
  let canCases ← [false, true].mapM (receiveCAN registered)
  let ps2Cases ← [false, true].mapM (receivePS2 registered)
  let ps2Idle ← runFixture registered "ps2-no-event" ps2.words 3 (fun _ => 3) 720 [] [] none
  let uartCases ← (List.range 4).mapM (receiveUART registered)
  pure (canCases ++ ps2Cases ++ [ps2Idle] ++ uartCases)

def main : IO Unit := do
  let direct ← scenarios false
  let registered ← scenarios true
  requireFixture (direct.map Json.compress == registered.map Json.compress) "Event receipts differ across stores"
  IO.println (Json.mkObj [("schema", toJson "pinwheel.ready-event-policies.v1"),
    ("stores", toJson ["direct", "registered"]), ("cases", Json.arr direct.toArray)]).compress
