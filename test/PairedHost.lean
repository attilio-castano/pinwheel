import Pinwheel.Hardware.Storage.PairedHost

open Pinwheel.Hardware Pinwheel.Hardware.Storage PairedController

private abbrev CoreState := Values Register × Memory.Sram.State 9 64

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def input (command : BitVec 3 := 0) (incoming : BitVec 2 := 0)
    (reset : Bool := false) (data : BitVec 64 := 0) (init : Bool := false) :
    Values Loader.Machine.Input
  | _, .command => command | _, .data => data | _, .init => BitVec.ofBool init
  | _, .reset => BitVec.ofBool reset | _, .incoming => incoming

-- Snapshot lazy register closures so a history evaluates each edge only once.
private def freeze (state : CoreState) : CoreState :=
  let s : Values Register := state.1
  let p0 := Vector.ofFn fun k : Fin 32 => s (.parameter false (BitVec.ofFin k))
  let p1 := Vector.ofFn fun k : Fin 32 => s (.parameter true (BitVec.ofFin k))
  let boot := (s (.boot false), s (.boot true))
  let idle := (s (.idle false), s (.idle true))
  let active := s .active; let valid := s .valid; let pending := s .pending; let cursor := s .cursor
  let current := s .current; let cached := s .cached; let mode := s .mode
  let remaining := s .remaining; let waitLeft := s .waitLeft; let levels := s .levels
  let enabled := s .enabled; let samples := s .samples; let payload := s .payload
  let words := Vector.ofFn fun k : Fin 512 => state.2.contents (BitVec.ofFin k)
  (fun {_} r => match r with
    | .parameter b k => (if b then p1 else p0)[k.toNat]
    | .boot b => if b then boot.2 else boot.1
    | .idle b => if b then idle.2 else idle.1
    | .active => active | .valid => valid | .pending => pending | .cursor => cursor
    | .current => current | .cached => cached | .mode => mode
    | .remaining => remaining | .waitLeft => waitLeft | .levels => levels
    | .enabled => enabled | .samples => samples | .payload => payload,
    ⟨fun k => words[k.toNat], state.2.q⟩)

private abbrev PackageState := PairedPackage.State (Memory.Sram.State 9 64)
private def memory : Memory.SinglePort.Contract (Memory.Sram.State 9 64) 9 64 :=
  ⟨id, fun request state => Memory.SinglePort.step state request, fun _ _ => rfl⟩

private def program : Execution.Image := {
  memory := Vector.ofFn fun pc => match pc.val with
    | 0 => .action ⟨⟨1, 7⟩, 0, some ⟨0, 0⟩⟩
    | 1 => .action ⟨⟨6, 5⟩, 0, some ⟨1, 15⟩⟩
    | _ => .halt
  idle := ⟨5, 2⟩
  last := 2 }

private def replacement : Execution.Image := {
  memory := Vector.replicate 256 .halt
  idle := ⟨2, 7⟩
  last := 0 }

private def token (p : Execution.Image) (node : PairedImage.Node) : BitVec 32 :=
  match node with
  | none => 7
  | some pc =>
    let f := PairedImage.fields p pc
    if f.kind == 4 then 4 else
      (0#2) ++ pc ++ (BitVec.ofNat 5 pc.toNat) ++ f.duration ++ f.enabled ++ f.levels ++ f.kind

private def image (p : Execution.Image) : PairedImage.Image := {
  parameters := Vector.ofFn fun k => PairedImage.parameter (PairedImage.fields p (BitVec.ofNat 8 k.val))
  rows := Vector.ofFn fun k =>
    if k.val ≤ p.last.val then
      token p (PairedImage.successor p (BitVec.ofFin k) true) ++
        token p (PairedImage.successor p (BitVec.ofFin k) false)
    else (4#32) ++ (4#32)
  boot := token p (some 0)
  idle := p.idle.enabled ++ p.idle.levels }

private def serialInputs (v : Values Serial.Input) : Serial.Inputs :=
  ⟨v .init == 1, v .sck == 1, v .mosi == 1, v .csn == 1, v .incoming⟩

-- Snapshot the actual package, including every sampler, receiver and mailbox
-- register. The core and SRAM are never substituted with reference results.
private def unpack (actual : Values FullRegister × Memory.Sram.State 9 64) : PackageState :=
  let s : Values FullRegister := actual.1
  let core : Values Register := fun {_} r => s (.inner (.inner (.inner (.inner r))))
  let rx : Values Serial.Register := fun {_} r => s (.inner (.inner (.inner (.extra r))))
  let first : Values Serial.Input := fun {_} r => s (.inner (.inner (.extra (.first r))))
  let second : Values Serial.Input := fun {_} r => s (.inner (.inner (.extra (.second r))))
  let result : Values HostResult.Register := fun {_} r => s (.extra r)
  { core := freeze (core, actual.2)
    adapters := ⟨serialInputs first, serialInputs second,
      ⟨rx .sckPrev == 1, rx .count, rx .shift, rx .command, rx .fire == 1⟩⟩
    result := {
      resetFirst := result .resetFirst == 1, resetSecond := result .resetSecond == 1
      pageFirst := result .pageFirst, pageSecond := result .pageSecond
      controlFirst := result .controlFirst, controlSecond := result .controlSecond
      consumePrev := result .consumePrev == 1, clearPrev := result .clearPrev == 1
      wasActive := result .wasActive == 1, samples := result .samples, outcome := result .outcome
      valid := result .valid == 1, overrun := result .overrun == 1, rejected := result .rejected == 1 } }

private def ports (o : Values Chip.Output) : BitVec 8 × BitVec 8 × BitVec 8 :=
  (o .uoOut, o .uioOut, o .uioOe)

private def snapshot (s : PairedHost.ReferenceState) : PairedHost.ReferenceState :=
  let core := freeze s.storage.physical
  {s with storage := ⟨core.1, core.2, s.storage.ledger⟩}

private def idle : Chip.Pins := {uioIn := 3}

-- One serial sample at each low/high phase; header byte and payload are MSB
-- first. The final quiet samples flush the two samplers and result mailbox.
private def frame (command : BitVec 3) (data : BitVec 64 := 0) : List Chip.Pins :=
  let bits := ((List.range 8).map fun k => (command.setWidth 8).getLsbD (7-k)) ++
    ((List.range 64).map fun k => data.getLsbD (63-k))
  idle :: (bits.flatMap fun bit =>
    [{idle with uiIn := if bit then 2 else 0}, {idle with uiIn := if bit then 3 else 1}]) ++
      List.replicate 8 idle

private def updateLedger (s : PackageState) (l : PairedLoader.Ledger)
    (i : Values Loader.Machine.Input) : PairedLoader.Ledger :=
  let g : Values GraphInput := PairedCoverage.graphInputs i ⟨s.core.1, s.core.2, l⟩
  PairedLoader.record (PairedUpload.inputs g s.core.1) (PairedUpload.admitted g s.core.1)
    (PairedUpload.control s.core.1) l

-- Preparation uses real accepted decoded writes. Complete 290-word uploads
-- are not replayed bit by bit in this finite test; serial delivery is proved.
private def stage (n : Netlist Register (SramController.Out Loader.Machine.Output) Input)
    (s : PackageState) (l : PairedLoader.Ledger) (p : Execution.Image) : IO (PackageState × PairedLoader.Ledger) := do
  let c := PairedClosed.model n.component
  let mut state := s
  let mut ledger := l
  for i in ((input 1 : Values Loader.Machine.Input) :: (PairedImage.upload (image p)).map (fun w => input 2 (data := w))) do
    ledger := updateLedger state ledger i
    state := {state with core := freeze (c.step i state.core)}
  ensure (state.core.1 .pending == 1 && state.core.1 .cursor == 290) "Preparation did not accept all words"
  ensure (PairedImage.check p (image p) ledger.staged) "Accepted staged transcript is not certified"
  return (state, ledger)

private def sendCommit (n : Netlist Register (SramController.Out Loader.Machine.Output) Input)
    (s : PackageState) (l : PairedLoader.Ledger) (p : Execution.Image) : IO (PackageState × PairedLoader.Ledger × Nat) := do
  let chip := PairedPackage.executable (PairedComposition.package n).component memory
  let mut state := s
  let mut ledger := l
  let mut commits := 0
  let mut edges := 0
  for pin in frame 3 do
    let dec : Values Loader.Machine.Input := (PairedPackage.decoded state.adapters).values
    let o : Values Loader.Machine.Output := (PairedClosed.model n.component).observe dec state.core
    let expected := (PairedPackage.interpreted memory).step pin state
    let before := ports (chip.observe pin state.physical)
    ensure (before == ports ((PairedPackage.interpreted memory).observe pin state)) "Commit-frame pre-edge mismatch"
    ledger := updateLedger state ledger dec
    let next := unpack (chip.step pin state.physical)
    ensure (ports (chip.observe pin next.physical) == ports ((PairedPackage.interpreted memory).observe pin expected))
      "Commit-frame post-edge mismatch"
    if o (.control .commit) == 1 then
      ensure (PairedImage.check p (image p) ledger.active) "Committed transcript was not the certified staged image"
      ensure (PairedEntry.view next.core.1 == Reactive.embed (Pinwheel.Engine.Reactive.reset p))
        "Commit did not establish the execution relation without reset"
      ensure (next.result == expected.result) "Commit changed mailbox lifecycle"
      commits := commits + 1
    state := next
    edges := edges + 1
  ensure (commits == 1) "Serial frame did not deliver exactly one accepted commit"
  return (state, ledger, edges)

private def execute (n : Netlist Register (SramController.Out Loader.Machine.Output) Input)
    (p : Execution.Image) (s : PackageState) (r : PairedHost.ReferenceState) (pins : List Chip.Pins) :
    IO (PackageState × PairedHost.ReferenceState × Nat) := do
  let chip := PairedPackage.executable (PairedComposition.package n).component memory
  let mut state := s
  let mut reference := r
  let mut edges := 0
  for pin in pins do
    let dec := PairedPackage.decoded reference.adapters
    ensure (!dec.init && dec.command != 3) "Execution segment violates its input rule"
    ensure (ports (chip.observe pin state.physical) == ports ((PairedHost.reference p).observe pin reference))
      s!"Package pre-edge mismatch at {edges}"
    ensure (PairedEntry.view state.core.1 == Reactive.embed reference.execution) "Core pre-edge mismatch"
    state := unpack (chip.step pin state.physical)
    reference := snapshot ((PairedHost.reference p).step pin reference)
    ensure (ports (chip.observe pin state.physical) == ports ((PairedHost.reference p).observe pin reference))
      s!"Package post-edge mismatch at {edges}"
    ensure (PairedEntry.view state.core.1 == Reactive.embed reference.execution) "Core post-edge mismatch"
    ensure (state.result == reference.result) "Mailbox edge does not match E64 observation"
    edges := edges + 1
  return (state, reference, edges)

def main : IO Unit := do
  let .ok n := PairedValidation.core | throw (IO.userError "Retained constructor failed")
  let chip := PairedPackage.executable (PairedComposition.package n).component memory
  let mut s : PackageState := {
    core := (fun {w} _ => BitVec.ofNat w 0x55, ⟨fun _ => 0xdeadbeef, 0x12345678⟩)
    adapters := {
      first := {init := false, sck := true}, second := {init := false},
      receiver := {count := 71, shift := 0xabcdef, command := 5, fire := true} }
    result := {samples := 0xffff, valid := true, overrun := true, wasActive := true} }
  for pin in List.replicate 3 {idle with rstN := false} ++ List.replicate 3 idle do
    let expected := (PairedPackage.interpreted memory).step pin s
    ensure (ports (chip.observe pin s.physical) == ports ((PairedPackage.interpreted memory).observe pin s))
      "Initialization pre-edge mismatch"
    s := unpack (chip.step pin s.physical)
    ensure (ports (chip.observe pin s.physical) == ports ((PairedPackage.interpreted memory).observe pin expected))
      "Initialization post-edge mismatch"
  ensure (s.core.1 .valid == 0 && s.core.1 .mode == 0 && !s.result.valid && s.result.samples == 0)
    "Three reset-low samples did not initialize arbitrary state"
  let mut ledger : PairedLoader.Ledger := {}
  let mut count := 6
  let mut mutations := 0
  for (p, bank) in [(program, true), (replacement, false)] do
    (s, ledger) ← stage n s ledger p
    let previous := s.result
    let (committed, committedLedger, commitEdges) ← sendCommit n s ledger p
    s := committed
    ledger := committedLedger
    count := count + commitEdges
    ensure (s.core.1 .active == BitVec.ofBool bank) "Commit did not change banks"
    if !bank then ensure (s.result.samples == previous.samples && s.result.valid) "Replacement lost an unread result"
    let immediate := freeze ((PairedClosed.model n.component).step (input 5 3) s.core)
    ensure (PairedEntry.view immediate.1 == Reactive.embed (Pinwheel.Engine.Reactive.step p
      (Pinwheel.Engine.Reactive.reset p) false true 3)) "Immediate commit/start needs an extra edge"
    let mut r : PairedHost.ReferenceState := ⟨⟨s.core.1, s.core.2, ledger⟩,
      Pinwheel.Engine.Reactive.reset p, s.adapters, s.result⟩
    let (ran, expected, edges) ← execute n p s r (frame 5)
    s := ran; r := expected; count := count + edges
    ensure (s.result.valid && s.result.outcome == 5) "Completion did not reach the mailbox"
    ensure (s.result.samples == 0x8001) "Unread capture changed or pin inputs were sampled incorrectly"
    if !bank then ensure s.result.overrun "Immediate halt did not register a second completion"
    for (page, value) in [(1#2, 1#8), (2#2, 128#8)] do
      let pins := List.replicate 3 {idle with uiIn := 4 ||| (page.setWidth 8 <<< 3)}
      let (shown, expected, edges) ← execute n p s r pins
      s := shown; r := expected; count := count + edges
      ensure ((chip.observe idle s.physical) .uoOut == value) "Result page order changed"
    if bank then
      let pin := {idle with uiIn := 12}
      let (paged, expected, edges) ← execute n p s r (List.replicate 3 pin)
      s := paged; r := expected; count := count + edges
      let altered : List (PackageState × String) := [
        ({s with result := {s.result with samples := s.result.samples ^^^ 1}}, "mailbox sample"),
        ({s with core := (fun {_} reg => match reg with | .enabled => s.core.1 .enabled ^^^ 1 | q => s.core.1 q, s.core.2)}, "drive enable"),
        ({s with result := {s.result with pageFirst := 2}}, "page pipeline")]
      for (bad, label) in altered do
        let actual := unpack (chip.step pin bad.physical)
        let expected := snapshot ((PairedHost.reference p).step pin r)
        ensure (ports (chip.observe pin actual.physical) != ports ((PairedHost.reference p).observe pin expected))
          s!"Executed {label} corruption escaped package comparison"
        mutations := mutations + 1
    else
      let (cleared, expected, edges) ← execute n p s r
        (List.replicate 4 {idle with uiIn := 124} ++ List.replicate 4 idle)
      s := cleared; r := expected; count := count + edges
      ensure (!s.result.valid && !s.result.overrun) "Consume/clear did not release the retained result"
      let (last, _, edges) ← execute n p s r (frame 5)
      s := last; count := count + edges
      ensure (s.result.valid && s.result.samples == 0 && s.result.outcome == 5 && !s.result.overrun)
        "Halt-only restart did not deliver a fresh empty result"
  IO.println s!"Paired host controls: retained package; both banks; {count} pin edge pairs; commit/start without reset; replacement retains mailbox; serial frames and pages; {mutations} executed mutations rejected."
