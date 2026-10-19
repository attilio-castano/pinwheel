import Pinwheel.Hardware.Buffered.SerialSourceAdministrative
import Pinwheel.Hardware.Buffered.SerialSourceRelease
import Pinwheel.Hardware.Buffered.SramModel

/-! Independent finite sampled-wire controls for the actual serial/SRAM
package. Every edge evaluates the typed frontend and cached typed SRAM roots.
Selected edges additionally compare the ordinary product-state step, including
both banks and registered Q. Source execution uses ordinary prepare/start,
advance and release; it is not extracted from actual post-state registers. -/
namespace Pinwheel.Test.SerialSourceBoundary
open Pinwheel.Hardware Pinwheel.Program Pinwheel.Hardware.Buffered
open Pinwheel.Engine.Reactive

private def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError ("Serial source boundary: " ++ label))

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

private def Machine.step (s : Machine) (pin : SerialPackage.Pins) : Machine :=
  let actual := s.actual
  ⟨frontSnapshot (Serial.circuit.step (actual.inputs pin).values actual.frontend),
    s.controller.step (actual.coreInputs pin)⟩

private def drive (duration : Fin 256) : Program.Buffered.Instruction :=
  {operation := .drive ⟨⟨5, 7⟩, duration, none⟩}
private def shift : Program.Buffered.Instruction :=
  {operation := .shift 0 false false ⟨⟨0, 7⟩, 0, none⟩}
private def halt : Program.Buffered.Instruction := {operation := .halt}

private def immediate : Program.Buffered.Program :=
  ⟨.emit shift, ⟨0,0⟩, by decide, by decide, by decide⟩
private def captureCompletion : Program.Buffered.Program :=
  ⟨.seq (.emit (drive 0)) (.emit halt), ⟨0,0⟩, by decide, by decide, by decide⟩
private def longRunning : Program.Buffered.Program :=
  ⟨.repeat 7 (.emit (drive 255)), ⟨0,0⟩, by decide, by decide, by decide⟩

private def fixture (words : Array (BitVec 64)) (control : BitVec 24) (span : Nat) : Machine :=
  let registers : Values Sram.Register := fun {w} r => match r with
    | .metadata k => if k.toNat < words.size then BitVec.ofNat 28 control.toNat else 0
    | .branch _ => 0
    | .branchWritten => 1
    | .startWord => words[0]?.getD 0
    | .core .count => BitVec.ofNat 7 words.size
    | .core .virtualSpan => BitVec.ofNat 11 span
    | .core .valid => 1
    | .core .generation => 1
    | .core _ => BitVec.ofNat w 0
  let cells := Array.ofFn fun k : Fin 64 => (words[k.val]?.getD 0).toNat
  ⟨frontSnapshot ({} : Serial.State).values,
    ⟨SramModel.snapshot registers, #[cells,cells], #[0x1234,0x9876]⟩⟩

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

private def tick (r : Run) (pin : SerialPackage.Pins) (action : Action := .clock)
    (ordinary : Bool := false) : IO Run := do
  let machine := r.machine.step pin
  if ordinary then
    IO.println s!"Serial source boundary: ordinary step at edge {r.edges}"
    ordinaryStep r.machine pin machine
    IO.println s!"Serial source boundary: ordinary step checked at edge {r.edges}"
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

/-- Stop at the real post-frame, pre-dispatch admission cut. -/
private def request (r : Run) (word : BitVec 160) : IO Run := do
  check (!(record r).ready && !(record r).active) "request requires free frontend"
  let mut r ← tick r idle
  r ← tick r (pins false false false 1)
  for k in [:160] do
    let bit := word.getLsbD (159-k)
    r ← tick r (pins false false bit (k+2))
    r ← tick r (pins true false bit (k+3))
  r ← tick r idle
  check ((record r).dispatch && (record r).code == 0) "raw frame valid dispatch"
  return r

private def capture (r : Run) : IO Run := do
  check (record r).capture "capture pipeline pending"
  let expected := (record r).capturedResponse (r.machine.actual.inputs idle)
  let next ← tick r idle
  check ((record next).ready && (record next).response == expected) "pre-edge frozen capture"
  return next

private def read (r : Run) (bits : Nat) : IO (Run × Nat) := do
  let frozen := (record r).response
  let mut r ← tick r idle
  r ← tick r (pins false false false 2)
  let mut received := 0
  for k in [:bits] do
    r ← tick r (pins false false false (k+3))
    let high := pins true false true (k+4)
    let bit := r.machine.actual.observe high .miso
    received := 2*received+bit.toNat
    r ← tick r high
    check ((record r).response == frozen) "read preserves frozen receipt"
  r ← tick r idle
  check ((record r).ready == (bits != 192)) "exact read releases; short read retained"
  return (r,received)

private def start (r : Run) (sequence : Nat) (payload : BitVec 32) (tx rx : Nat)
    (ordinary : Bool := false) : IO Run := do
  let r ← request r (frame 3 sequence (payload.toNat+tx*2^32+rx*2^38+2^44))
  let input : Values Reactive.Input := r.machine.actual.coreInputs idle
  check (Reactive.starting.eval input r.machine.controller.core == 1) "actual START admission"
  check (r.machine.actual.status idle .rejected == 0) "accepted START diagnostic"
  tick r idle (.start payload tx rx) ordinary

private def faultAndRetry : IO (Nat × Nat) := do
  let r : Run := {machine := fixture #[GenericEncoding.encode shift] 0 1, program := immediate}
  let r ← start r 0x1234 0x80000002 0 1 true
  check (r.machine.controller.core .phase == 7 && r.machine.controller.core .retained == 1)
    "accepted START immediately faults underflow"
  let r ← capture r
  let response := (record r).response
  check (field response 176 16 == 0x5A10 && field response 4 1 == 0 &&
    field response 128 3 == 7 && field response 2 1 == 1 && field response 160 16 == 0x1234)
    "accepted immediate fault receipt is not rejection"
  let (r,short) ← read r 17
  check (short == response.toNat / 2^175 && (record r).response == response)
    "short read returns prefix and retains exact response"
  let (r,full) ← read r 192
  check (full == response.toNat) "short-read retry returns same complete response"
  return (r.edges,r.ordinary)

private def completionAndRelease : IO (Nat × Nat) := do
  let r : Run := {
    machine := fixture #[GenericEncoding.encode (drive 0),GenericEncoding.encode halt] 0 2
    program := captureCompletion}
  let r ← start r 3 0 0 0
  check (r.machine.controller.core .phase == 1) "zero-duration first action active at dispatch"
  let r ← capture r
  let response := (record r).response
  check (field response 1 1 == 1 && field response 2 1 == 0 && field response 128 3 == 1 &&
    r.machine.controller.core .phase == 5 && r.machine.controller.core .retained == 1)
    "capture response describes pre-edge busy state; capture edge completes"
  let (r,full) ← read r 192
  check (full == response.toNat) "completion receipt remains frozen during read"
  let r ← request r (frame 4 4 (1+2*2^16))
  check (r.machine.actual.status idle .rejected == 1) "stale RELEASE rejected"
  let r ← tick r idle .clock true
  let r ← capture r
  let stale := (record r).response
  check (field stale 176 16 == 0x5A14 && field stale 4 1 == 1 && field stale 2 1 == 1 &&
    field stale 91 16 == 1) "stale release receipt retains owner"
  let (r,readback) ← read r 192
  check (readback == stale.toNat) "stale release wire response"
  let r ← request r (frame 4 5 (1+1*2^16))
  check (Reactive.releasing.eval (r.machine.actual.coreInputs idle) r.machine.controller.core == 1)
    "matching RELEASE admitted"
  let r ← tick r idle .release true
  let r ← capture r
  let released := (record r).response
  check (field released 176 16 == 0x5A10 && field released 4 1 == 0 &&
    field released 0 1 == 1 && field released 1 1 == 0 && field released 2 1 == 0 &&
    field released 128 3 == 0) "matching release frees engine and preserves installation"
  let (r,readback) ← read r 192
  check (readback == released.toNat) "matching release wire response"
  return (r.edges,r.ordinary)

private def busyAdministrative : IO (Nat × Nat) := do
  let word := GenericEncoding.encode (drive 255)
  let r : Run := {machine := fixture #[word] (BitVec.ofNat 24 (1+7*2^8+2^20)) 8, program := longRunning}
  let r ← start r 10 0xF0000002 1 0
  let r ← capture r
  let (r,_) ← read r 192
  let banks := r.machine.controller.arrays
  let metadata := r.machine.controller.registers.values (.metadata 0)
  let r ← request r (frame 1 11 ((GenericEncoding.encode halt).toNat))
  check (r.machine.actual.status idle .busy == 1 && r.machine.actual.status idle .rejected == 1)
    "administrative write arrives while busy"
  let r ← tick r idle
  let r ← capture r
  let rejected := (record r).response
  check (field rejected 176 16 == 0x5A14 && field rejected 4 1 == 1 && field rejected 1 1 == 1)
    "busy write receipt rejection"
  check (r.machine.controller.arrays == banks &&
    r.machine.controller.registers.values (.metadata 0) == metadata)
    "busy rejected write preserves installed image"
  let (r,readback) ← read r 192
  check (readback == rejected.toNat) "busy rejection exact wire response"
  return (r.edges,r.ordinary)

private def run : IO Unit := do
  IO.println "Serial source boundary: immediate fault and retry"
  let fault ← faultAndRetry
  IO.println "Serial source boundary: capture completion and RELEASE"
  let completion ← completionAndRelease
  IO.println "Serial source boundary: busy administrative rejection"
  let busy ← busyAdministrative
  IO.println s!"Serial source boundaries: 6 controls; {fault.1+completion.1+busy.1} sampled edges; {fault.2+completion.2+busy.2} ordinary package boundaries; passed"

end Pinwheel.Test.SerialSourceBoundary

def main : IO Unit := Pinwheel.Test.SerialSourceBoundary.run
