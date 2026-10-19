import Pinwheel.Hardware.Buffered.SerialSourceAdministrative
import Pinwheel.Hardware.Buffered.SerialSourceRelease
import Pinwheel.Hardware.Buffered.I2cSource
import Pinwheel.Hardware.Buffered.SramModel

/-! Independent finite native control of the initialized sampled serial/SRAM
path. Patterned controller, arrays and Q are reset through physical pins;
all upload and execution commands enter as 160-bit frames and all receipts
leave as 192 MISO samples. Expected source execution uses ordinary transfer
operations and Buffered.advance, never a refinement theorem or decoded actual
post-state. MemoEval/MemoBind accelerate the frozen typed equations only.
This finite runner does not establish native compiler or analog correctness. -/
namespace Pinwheel.Test.SerialInitializedBoundary
open Pinwheel.Hardware Pinwheel.Program Pinwheel.Hardware.Buffered
open Pinwheel.Engine.Reactive

private def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError ("Serial initialized boundary: " ++ label))

private def frontValues (bank : Array Nat) : Values Serial.Register := fun {w} r =>
  BitVec.ofNat w (bank[Serial.registerIndex r]?.getD 0)
private def frontSnapshot (values : Values Serial.Register) : Array Nat :=
  Serial.registers.map fun ⟨_,r⟩ => (values r).toNat

private structure Machine where
  frontend : Array Nat
  controller : SramModel.State

def Machine.actual (s : Machine) : SerialPackage.State :=
  ⟨frontValues s.frontend, ⟨s.controller.registers.values,
    fun port => ⟨s.controller.contents port,
      BitVec.ofNat 64 (s.controller.q[port.val]?.getD 0)⟩⟩⟩

private def frontendExpressions : Array (Sigma (Expr Serial.Input Serial.Register)) :=
  Serial.registers.map fun ⟨w,r⟩ => ⟨w,Serial.circuit.next r⟩

private def Machine.step (s : Machine) (pin : SerialPackage.Pins) : Machine :=
  let actual := s.actual
  ⟨MemoEval.evalMany (actual.inputs pin).values actual.frontend frontendExpressions,
    s.controller.step (actual.coreInputs pin)⟩

private structure Run where
  machine : Machine
  program : Program.Buffered.Program
  source : Option Program.Buffered.State := none
  buffers : Transfer.State := {}
  first : BitVec 2 := 0
  second : BitVec 2 := 0
  payload : BitVec 32 := 0
  edges : Nat := 0
  ordinary : Nat := 0
  policy : Bool := false

private inductive Action where
  | clock
  | start (payload : BitVec 32) (txLength rxCapacity : Nat)
  | release

private def sourceStep (r : Run) (pin : SerialPackage.Pins) (action : Action) :
    Option Program.Buffered.State × Transfer.State × BitVec 32 := Id.run do
  match action with
  | .clock =>
    let source := r.source.map fun s => Program.Buffered.advance r.program Refinement.capacity s pin.rawInputs
    return (source, (source.map (·.buffers)).getD r.buffers, r.payload)
  | .start payload txLength rxCapacity =>
    let tx := (List.range txLength).map payload.getLsbD
    let prepared := Transfer.step Refinement.capacity r.buffers (.prepare 1 tx rxCapacity)
    let owner : Transfer.Identity := ⟨r.buffers.epoch, r.buffers.nextSequence⟩
    let started := Transfer.step Refinement.capacity prepared.state (.start owner 1)
    let seed : Program.Buffered.State := {
      core := ⟨.stopped .ready, r.program.idle, Vector.replicate 16 false⟩
      buffers := started.state
      owner := owner
      samplerFirst := r.first
      samplerSecond := r.second }
    let entered := Program.Buffered.start r.program Refinement.capacity seed
    let source := {entered with samplerFirst := pin.rawInputs, samplerSecond := r.first}
    return (some source, source.buffers, payload)
  | .release =>
    let source := r.source.map fun s =>
      {s with buffers := (Transfer.step Refinement.capacity s.buffers (.release s.owner)).state}
    return (source, (source.map (·.buffers)).getD r.buffers, r.payload)

private def compareSource (r : Run) : IO Unit := do
  let some s := r.source | return
  let core : Values Reactive.Register := r.machine.controller.core
  match s.buffers.slot with
  | .free =>
    check (core .phase == 0 && core .retained == 0) s!"edge{r.edges} released hardware free"
  | .preparing _ => throw (IO.userError "unexpected preparing source fixture")
  | .running e | .completed ⟨e,_⟩ =>
    check ((core .txConsumed).toNat == e.txConsumed &&
      (core .rxLength).toNat == e.rx.length && core .rxData == SpiPacking.rxWord e.rx)
      s!"edge{r.edges} source TX/RX diagnostic"
    check (core .txData == (r.payload >>> e.txConsumed)) s!"edge{r.edges} full payload suffix"
    check ((core .generation).toNat == e.request.programGeneration &&
      (core .transfer).toNat == e.request.identity.sequence) s!"edge{r.edges} owned identity"
    check (core .levels == s.core.pins.levels && core .enabled == s.core.pins.enabled)
      s!"edge{r.edges} source pins"
    check (core .phase == Refinement.controlPhase s.core.control)
      s!"edge{r.edges} source control phase {repr s.core.control} vs {(core .phase).toNat}"
    check ((core .retained == 1) == Refinement.slotRetained s.buffers.slot)
      s!"edge{r.edges} source retention"
    for k in [:16] do
      check ((core .scratch).getLsbD k == s.core.samples[k]!) s!"edge{r.edges} scratch{k}"
    if Engine.Reactive.busy s.core then
      check (core .stage1 == s.samplerFirst && core .stage2 == s.samplerSecond)
        s!"edge{r.edges} running samplers"

private def ordinaryStep (before : Machine) (pin : SerialPackage.Pins) (after : Machine) : IO Unit := do
  let actual := before.actual.step pin
  check (frontSnapshot actual.frontend == after.frontend) "ordinary frontend boundary"
  check ((SramModel.snapshot actual.controller.registers).bank == after.controller.registers.bank)
    "ordinary all SRAM register roots"
  for p in [:2] do
    let port : Fin 2 := Fin.ofNat 2 p
    check ((actual.controller.arrays port).q.toNat == after.controller.q[p]!) "ordinary SRAM Q"
    for k in [:64] do
      check (((actual.controller.arrays port).contents (BitVec.ofNat 6 k)).toNat ==
        (after.controller.arrays[p]!)[k]!) "ordinary SRAM banks"

/-- The synthetic input script is selected only from the independent source.
A two-instruction lookahead raises SDA during the DRIVE→WAIT prefix before a
CHECKED both-high guard, so its pre-edge stage2 is already high at guard entry.
Other data/ACK samples retain SDA0. This is not an electrical peer model. -/
private def bothHighSoon (p : Program.Buffered.Program) (pc : Program.Buffered.PC) : Bool :=
  (List.range 3).any fun distance =>
    match p.fetch (Fin.ofNat 1024 (pc.val + distance)) with
    | some {operation := .checked _ guard _ _, ..} => guard.mask == 3 && guard.value == 3
    | _ => false

private def policyRaw (p : Program.Buffered.Program) (source : Option Program.Buffered.State) : BitVec 2 :=
  match source with
  | none => 1
  | some s => match s.core.control with
    | .qualifying .. => 3
    | .active pc _ | .waiting pc _ | .checked pc _ => if bothHighSoon p pc then 3 else 1
    | .stopped _ => 1

private def tick (r : Run) (pin : SerialPackage.Pins) (action : Action := .clock)
    (ordinary : Bool := false) : IO Run := do
  let pin := if r.policy then {pin with rawInputs := policyRaw r.program r.source} else pin
  let machine := r.machine.step pin
  if ordinary then
    IO.println s!"Serial initialized boundary: ordinary step at edge {r.edges}"
    ordinaryStep r.machine pin machine
    IO.println s!"Serial initialized boundary: ordinary step checked at edge {r.edges}"
  let (source,buffers,payload) := sourceStep r pin action
  let next : Run := {r with
    machine := machine, source := source, buffers := buffers,
    payload := payload, first := pin.rawInputs, second := r.first,
    edges := r.edges+1, ordinary := r.ordinary+(if ordinary then 1 else 0)}
  compareSource next
  return next

private def pins (sck csn mosi : Bool) (raw : Nat := 0) : SerialPackage.Pins :=
  {sck,csn,mosi,rawInputs := BitVec.ofNat 2 raw}
private def idle : SerialPackage.Pins := pins false true false
private def frame (opcode sequence payload : Nat) : BitVec 160 :=
  BitVec.ofNat 160 ((0xA710+opcode)*2^144 + sequence*2^128 + payload)
private def record (r : Run) : Serial.State := r.machine.actual.record
private def field (word : BitVec 192) (start width : Nat) : Nat := (word.extractLsb' start width).toNat

private def initial : Run := {
  machine := ⟨Serial.registers.mapIdx (fun k ⟨w,_⟩ => (997*7919+k*104729+23) % 2^w),
    SramModel.State.initial 73⟩
  program := I2cSource.source }

private def rowPayload (k : Nat) : Nat :=
  (I2cSource.word (BitVec.ofNat 6 k)).toNat +
  (I2cSource.control (BitVec.ofNat 6 k)).toNat*2^64 +
  (I2cSource.branchIndex (BitVec.ofNat 6 k)).toNat*2^88 + k*2^92

private def dictionaryPayload (k : Nat) : Nat :=
  (I2cSource.dictionary (BitVec.ofNat 4 k)).toNat + k*2^56

/-- Physical samples only. Vary dwell and raw inputs without changing frame bits. -/
private def request (r : Run) (word : BitVec 160) (raw : Nat := 3) : IO Run := do
  check (!(record r).ready && !(record r).active) "request frontend available"
  let mut r ← tick r (pins false true false raw)
  r ← tick r (pins false false false raw)
  for k in [:160] do
    let bit := word.getLsbD (159-k)
    r ← tick r (pins false false bit raw)
    if k % 37 == 0 then r ← tick r (pins false false (!bit) raw)
    r ← tick r (pins true false bit raw)
    if k % 41 == 0 then r ← tick r (pins true false (!bit) raw)
  r ← tick r (pins false true false raw)
  check ((record r).dispatch && (record r).code == 0 && (record r).request == word)
    "physical frame decodes requested word"
  return r

/-- An independent numeric packing of the documented receipt ABI, from the
pre-capture public state. This does not call Serial.capturedResponse. -/
private def expectedReceipt (r : Run) (raw : Nat) : BitVec 192 := Id.run do
  let core : Values Reactive.Register := r.machine.controller.core
  let current := record r
  let phase := (core .phase).toNat
  let busy := phase != 0 && phase < 5
  let mode := if busy then 1 else if phase == 5 then 2 else if phase == 6 || phase == 7 then 3 else 0
  let depth := (core .currentControl).toNat % 4
  let env0 := if depth == 2 then (core .inner).toNat else if depth == 1 then (core .outer).toNat else 0
  let env1 := if depth == 2 then (core .outer).toNat else 0
  let index := (r.machine.actual.coreInputs (pins false true false raw) .readIndex).toNat
  let readable := core .retained == 1 && index < (core .rxLength).toNat
  let fields : List (Nat × Nat) := [
    (0,(core .valid).toNat), (1,busy.toNat), (2,(core .retained).toNat),
    (3,(core .pending).toNat), (4,current.rejected.toNat), (5,mode),
    (7,(core .pc).toNat), (15,(core .remaining).toNat), (23,(core .levels).toNat),
    (26,(core .enabled).toNat), (29,(core .txConsumed).toNat),
    (35,(core .rxLength).toNat), (41,(core .rxData).toNat), (73,readable.toNat),
    (74,(readable && (core .rxData).getLsbD index).toNat),
    (75,(core .generation).toNat), (91,(core .transfer).toNat),
    (107,(core .generation == 65535 || core .transfer == 65535).toNat),
    (108,(core .stage1).toNat), (110,(core .stage2).toNat),
    (112,(core .virtualPC).toNat), (122,env0), (125,env1),
    (128,phase), (131,(core .waitLeft).toNat), (139,(core .scratch).toNat)]
  let code := if current.code == 0 && current.rejected then 4 else current.code.toNat
  return BitVec.ofNat 192 ((0x5A10+code)*2^176 + current.sequence.toNat*2^160 +
    fields.foldl (fun packed item => packed + item.2*2^item.1) 0)

private def capture (r : Run) (raw : Nat := 3) : IO Run := do
  check (record r).capture "capture pending after dispatch"
  let expected := expectedReceipt r raw
  let next ← tick r (pins false true false raw)
  check ((record next).ready && (record next).response == expected) "complete independent pre-capture receipt ABI"
  return next

private def read (r : Run) (raw : Nat := 3) : IO Run := do
  let frozen := (record r).response
  let mut r ← tick r (pins false true false raw)
  r ← tick r (pins false false false raw)
  let mut received := 0
  for k in [:192] do
    r ← tick r (pins false false (k % 3 == 0) raw)
    let high := pins true false (k % 3 != 0) raw
    let bit := r.machine.actual.observe high .miso
    received := 2*received+bit.toNat
    r ← tick r high
    check ((record r).response == frozen) "frozen response during 192-bit wire read"
  r ← tick r (pins false true false raw)
  check (!(record r).ready && !(record r).active && received == frozen.toNat) "exact full MISO response and frontend reuse"
  return r

private def transact (r : Run) (opcode sequence payload : Nat) (rejected : Bool := false)
    (action : Action := .clock) (raw : Nat := 3) (ordinary : Bool := false) : IO (Run × BitVec 192) := do
  let r ← request r (frame opcode sequence payload) raw
  check ((r.machine.actual.status idle .rejected == 1) == rejected) s!"dispatch diagnostic opcode{opcode} sequence{sequence}"
  let r ← tick r (pins false true false raw) action ordinary
  let r ← capture r raw
  let receipt := (record r).response
  check (field receipt 160 16 == sequence && field receipt 4 1 == rejected.toNat &&
    field receipt 176 4 == (if rejected then 4 else 0)) "captured delivery identity and rejection"
  let r ← read r raw
  return (r,receipt)

private def installedImage (r : Run) (original : Machine) : IO Unit := do
  let registers : Values Sram.Register := r.machine.controller.registers.values
  let core : Values Reactive.Register := r.machine.controller.core
  check (core .valid == 1 && core .count == 50 && core .virtualSpan == 270 &&
    core .idleLevels == 0 && core .idleEnabled == 0 && registers .branchWritten == 65535 &&
    core .written == BitVec.ofNat 64 (2^50-1)) "installed geometry, coverage and idle profile"
  check (registers .startWord == I2cSource.word 0) "actual row-zero START mirror"
  for k in [:16] do
    check (registers (.branch (BitVec.ofNat 4 k)) == I2cSource.dictionary (BitVec.ofNat 4 k))
      s!"actual dictionary{k}"
  for k in [:64] do
    let address := BitVec.ofNat 6 k
    let metadata := (registers (.metadata address)).toNat
    let expectedMetadata := if k < 50 then (I2cSource.control address).toNat +
      (I2cSource.branchIndex address).toNat*2^24 else 0
    check (metadata == expectedMetadata) s!"actual metadata{k}, including COMMIT tail projection"
    for p in [:2] do
      let cell := r.machine.controller.arrays[p]![k]!
      if k < 50 then
        check (cell == (I2cSource.word address).toNat) s!"physical bank{p} live row{k}"
        let branch := (registers (.branch (BitVec.ofNat 4 (metadata/2^24)))).toNat
        let expanded := cell + (metadata % 2^24)*2^64 + branch*2^88
        let expected := (I2cSource.word address).toNat + (I2cSource.control address).toNat*2^64 +
          (I2cSource.dictionary (I2cSource.branchIndex address)).toNat*2^88
        check (expanded == expected) s!"physical bank{p} expanded resident row{k}"
      else
        check (cell == original.controller.arrays[p]![k]!) s!"physical SRAM tail{k} stays arbitrary"

private def sourceOutcome (r : Run) (outcome : Transfer.Outcome) (tx rx : Nat) : IO Unit := do
  let some source := r.source | throw (IO.userError "missing independent source")
  match source.buffers.slot with
  | .completed result =>
    check (result.outcome == outcome && result.execution.txConsumed == tx &&
      result.execution.rx.length == rx) s!"ordinary source outcome {repr outcome}, exact partial data"
    let read := Transfer.step Refinement.capacity source.buffers (.read source.owner)
    check (read.reply == .result result && read.state == source.buffers) "ordinary owned result read"
  | _ => throw (IO.userError "source has not completed")

private def start (r : Run) (sequence : Nat) (payload : BitVec 32) (tx rx raw : Nat)
    (ordinary : Bool := false) : IO Run := do
  let r ← request r (frame 3 sequence (payload.toNat+tx*2^32+rx*2^38+2^44)) raw
  check (Reactive.starting.eval (r.machine.actual.coreInputs idle) r.machine.controller.core == 1 &&
    r.machine.actual.status idle .rejected == 0) "actual serialized START admission"
  let r ← tick r (pins false true false raw) (.start payload tx rx) ordinary
  capture r raw

private def retainedPoll (r : Run) (sequence phase transfer tx rx : Nat) (raw : Nat := 0) : IO Run := do
  let (r,response) ← transact r 0 sequence 31 false .clock raw
  check (field response 128 3 == phase && field response 2 1 == 1 && field response 1 1 == 0 &&
    field response 75 16 == 1 && field response 91 16 == transfer &&
    field response 29 6 == tx && field response 35 6 == rx) "retained source result in actual wire receipt"
  check (field response 73 1 == (if rx == 32 then 1 else 0) && field response 74 1 == 0)
    "indexed result bit31 from retained RX prefix"
  return r

private def release (r : Run) (sequence transfer : Nat) (ordinary : Bool := false) : IO Run := do
  let (r,response) ← transact r 4 sequence (1+transfer*2^16) false .release 0 ordinary
  check (field response 0 1 == 1 && field response 2 1 == 0 && field response 128 3 == 0 &&
    r.machine.controller.core .phase == 0 && r.machine.controller.core .retained == 0 &&
    r.machine.controller.core .generation == 1 && r.machine.controller.core .transfer == BitVec.ofNat 16 transfer)
    "matching serialized RELEASE leaves installed reusable state"
  check (r.buffers.slot == .free && r.buffers.nextSequence == transfer+1) "ordinary released allocator carried to next START"
  return r

private def policyWitness : IO Unit := do
  let payload : BitVec 32 := 0x80000000
  let tx := (List.range 24).map payload.getLsbD
  let prepared := Transfer.step Refinement.capacity {} (.prepare 1 tx 32)
  let started := Transfer.step Refinement.capacity prepared.state (.start ⟨0,1⟩ 1)
  let seed : Program.Buffered.State := {
    core := ⟨.stopped .ready,I2cSource.source.idle,Vector.replicate 16 false⟩
    buffers := started.state,owner := ⟨0,1⟩,samplerFirst := 1,samplerSecond := 1 }
  let mut source := Program.Buffered.start I2cSource.source Refinement.capacity seed
  for _ in [:4096] do
    source := Program.Buffered.advance I2cSource.source Refinement.capacity source
      (policyRaw I2cSource.source (some source))
  match source.buffers.slot with
  | .completed completion =>
    check (completion.outcome == .complete && completion.execution.txConsumed == 24 &&
      completion.execution.rx == List.replicate 32 false)
      "independent synthetic source script completes TX24/RX32zero across repeated START"
  | _ => throw (IO.userError "synthetic source script did not reach retained completion")

private def run : IO Unit := do
  policyWitness
  IO.println "Serial initialized boundary: patterned cold startup and missing-dictionary control"
  let original := initial.machine
  check (original.controller.arrays[0]! != original.controller.arrays[1]! &&
    original.controller.q[0]! != original.controller.q[1]!) "unrelated patterned startup SRAM replicas and Q"
  let mut r ← tick initial {cold := true,rawInputs := 2}
  check (!(record r).ready && !(record r).active && !(record r).dispatch && !(record r).capture &&
    r.machine.controller.core .phase == 0 && r.machine.controller.core .retained == 0 &&
    r.machine.controller.core .valid == 0 && r.machine.controller.core .generation == 0 &&
    r.machine.controller.core .transfer == 0 && r.machine.controller.registers.values .branchWritten == 0 &&
    r.machine.controller.core .written == 0) "physical cold clears ownership, validity and upload coverage"
  for k in [:16] do
    if k != 1 then
      let result ← transact r 6 (100+k) (dictionaryPayload k)
      r := result.1
      check (r.machine.controller.core .valid == 0) "dictionary writes cannot establish VALID"
  for k in [:50] do
    let result ← transact r 1 (200+k) (rowPayload k) false .clock 3 (k == 0)
    r := result.1
    check (r.machine.controller.core .valid == 0 &&
      r.machine.controller.core .written == BitVec.ofNat 64 (2^(k+1)-1)) "each actual row write establishes exactly its prefix"
    if k % 10 == 9 then IO.println s!"Serial initialized boundary: {k+1}/50 physical rows delivered"
  check (r.machine.controller.registers.values .branchWritten == 65533 &&
    I2cSource.dictionary 1 != 0) "only the nonzero ACK dictionary slot remains unwritten"
  let (negative,rejected) ← transact r 2 500 (50+270*2^7) true .clock 3 true
  r := negative
  check (field rejected 0 1 == 0 && r.machine.controller.core .valid == 0 &&
    r.machine.controller.core .generation == 0) "COMMIT rejects despite all live rows when ACK dictionary coverage missing"
  let repaired ← transact r 6 501 (dictionaryPayload 1)
  r := repaired.1
  let committed ← transact r 2 502 (50+270*2^7) false .clock 3 true
  r := committed.1
  check (r.machine.controller.core .generation == 1 && r.machine.controller.core .transfer == 0 &&
    field committed.2 0 1 == 1 && field committed.2 75 16 == 1) "repaired wire COMMIT establishes actual VALID and generation"
  installedImage r original

  IO.println "Serial initialized boundary: retained checked fault, timeout and reuse"
  r ← start r 600 0x80000002 1 0 3 true
  let startReceipt := (record r).response
  check (field startReceipt 128 3 == 4 && field startReceipt 1 1 == 1) "START capture witnesses busy QUALIFY"
  for _ in [:8] do
    if r.machine.controller.core .phase == 4 then r ← tick r (pins false true false 3)
  check (r.machine.controller.core .phase == 3) "qualified bus-free prefix reaches checked phase"
  for _ in [:5] do r ← tick r (pins false true false 0)
  sourceOutcome r .fault 0 0
  check (r.machine.controller.core .phase == 7 && r.machine.controller.core .retained == 1 &&
    (record r).response == startReceipt) "checked guard fault retained while earlier START receipt stays frozen"
  r ← read r 0
  r ← retainedPoll r 601 7 1 0 0
  r ← release r 602 1 true
  installedImage r original

  r ← start r 603 0xF0000002 0 1 0
  r ← read r 0
  sourceOutcome r .timeout 0 0
  check (r.machine.controller.core .phase == 6 && r.machine.controller.core .retained == 1)
    "unready zero-input QUALIFY retains timeout"
  r ← retainedPoll r 604 6 2 0 0
  r ← release r 605 2

  IO.println "Serial initialized boundary: synthetic digital ready/ACK0 completion"
  r := {r with policy := true}
  r ← start r 606 0x80000000 24 32 1
  r ← read r 1
  for _ in [:4096] do
    if r.machine.controller.core .retained != 1 then r ← tick r idle
  sourceOutcome r .complete 24 32
  check (r.machine.controller.core .phase == 5 && r.machine.controller.core .retained == 1 &&
    r.machine.controller.core .txConsumed == 24 && r.machine.controller.core .rxLength == 32 &&
    r.machine.controller.core .rxData == 0 && r.machine.controller.core .txData == 0x80)
    "synthetic ready history completes all24TX/all32zeroRX; unused payload high bits remain"
  r ← retainedPoll r 607 5 3 24 32 1
  r ← release r 608 3 true
  installedImage r original
  IO.println s!"Serial initialized boundaries: 68 upload transactions, 1 dictionary omission/repaired COMMIT, 3 retained outcomes and RELEASE/reuse; {r.edges} sampled edges; {r.ordinary} ordinary package boundaries; passed"

end Pinwheel.Test.SerialInitializedBoundary

def main : IO Unit := Pinwheel.Test.SerialInitializedBoundary.run

