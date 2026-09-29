import Pinwheel.Hardware.Storage.PairedTimed

open Pinwheel.Hardware Pinwheel.Hardware.Storage PairedController

private abbrev State := Values Register × Memory.Sram.State 9 64

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def input (command : BitVec 3 := 0) (incoming : BitVec 2 := 0)
    (reset : Bool := false) (data : BitVec 64 := 0) (init : Bool := false) :
    Values Loader.Machine.Input
  | _, .command => command | _, .data => data | _, .init => BitVec.ofBool init
  | _, .reset => BitVec.ofBool reset | _, .incoming => incoming

-- Snapshot lazy register closures so a history evaluates each edge only once.
private def freeze (state : State) : State :=
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

private def program : Execution.Image := {
  memory := Vector.ofFn fun pc => match pc.val with
    | 0 => .checked ⟨⟨⟨1, 7⟩, 0, none⟩, ⟨0, 0⟩, some ⟨0, 0⟩, .branch 0 1 3⟩
    | 1 => .action ⟨⟨6, 5⟩, 0, some ⟨1, 0⟩⟩
    | 2 => .wait ⟨⟨2, 3⟩, ⟨1, true⟩, 0⟩
    | 3 => .qualify ⟨⟨4, 5⟩, ⟨1, 1⟩, 0, 0⟩
    | 4 => .checked ⟨⟨⟨3, 7⟩, 0, none⟩, ⟨3, 3⟩, some ⟨1, 15⟩, .jump 5⟩
    | 5 => .action ⟨⟨2, 7⟩, 255, some ⟨0, 15⟩⟩
    | _ => .halt
  idle := ⟨5, 2⟩
  last := 6 }

private def loopProgram : Execution.Image := {
  memory := Vector.replicate 256
    (.checked ⟨⟨⟨3, 6⟩, 0, some ⟨1, 0⟩⟩, ⟨0, 0⟩, some ⟨0, 0⟩, .jump 0⟩)
  idle := ⟨5, 2⟩
  last := 0 }

-- This producer is test-only. Its complete image must pass the independent
-- source certificate before any controller execution is compared.
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

private structure Edge where
  command : BitVec 3 := 0
  incoming : BitVec 2 := 0
  reset : Bool := false

private def scenarios : List (String × List Edge × BitVec 3) := [
  ("capture/branch/entry overwrite and maximum duration",
    [⟨5,0,false⟩, ⟨0,1,false⟩, (Edge.mk 0 0 false), ⟨0,2,false⟩, ⟨0,1,false⟩, ⟨0,3,false⟩] ++
      List.replicate 255 (Edge.mk 0 0 false) ++ [(Edge.mk 0 0 false)], 5),
  ("zero-budget wait timeout", [⟨5,0,false⟩, ⟨0,1,false⟩, (Edge.mk 0 0 false), (Edge.mk 0 0 false)], 6),
  ("zero-budget qualify timeout", [⟨5,0,false⟩, (Edge.mk 0 0 false), (Edge.mk 0 0 false)], 6),
  ("guard beats zero-duration dispatch", [⟨5,0,false⟩, (Edge.mk 0 0 false), ⟨0,1,false⟩, ⟨0,1,false⟩], 7),
  ("reset beats start and command reset restarts", [⟨5,0,false⟩, ⟨5,3,true⟩,
    ⟨5,1,false⟩, ⟨7,3,false⟩, ⟨5,0,false⟩], 3)]

def main : IO Unit := do
  let .ok n := PairedValidation.core | throw (IO.userError "Retained constructor failed")
  let c := PairedClosed.model n.component
  let tick (s : State) (i : Values Loader.Machine.Input) := freeze (c.step i s)
  let actualView (s : State) (i : Values Loader.Machine.Input) := PairedTimed.observe (c.observe i s)
  let mut edges := 0
  let mut mutationChecks := 0
  for (p, paths) in [(program, scenarios), (loopProgram,
      [("backward jump and repeated capture overwrite", ⟨5,0,false⟩ ::
        (List.range 64).map (fun k => Edge.mk (BitVec.ofNat 3 (k % 3)) (BitVec.ofNat 2 k) false), 3)])] do
    let img := image p
    ensure (PairedImage.check p img (PairedImage.upload img)) "Timed fixture image is not certified"
    let mut loaded : State := (fun {w} _ => BitVec.ofNat w 0x55, ⟨fun _ => 0xdeadbeef, 0x12345678⟩)
    let mut ledger : PairedLoader.Ledger := {}
    -- Track acceptance from the actual pre-edge controller. No list of merely
    -- offered words is treated as the committed transcript.
    let loadTick (s : State) (l : PairedLoader.Ledger) (i : Values Loader.Machine.Input) :=
      let g : Values GraphInput := PairedCoverage.graphInputs i ⟨s.1, s.2, l⟩
      (tick s i, PairedLoader.record (PairedUpload.inputs g s.1)
        (PairedUpload.admitted g s.1) (PairedUpload.control s.1) l)
    (loaded, ledger) := loadTick loaded ledger (input (init := true))
    for bank in [true, false] do
      (loaded, ledger) := loadTick loaded ledger (input 1)
      for word in PairedImage.upload img do
        (loaded, ledger) := loadTick loaded ledger (input 2 (data := word))
      (loaded, ledger) := loadTick loaded ledger (input 3)
      ensure (loaded.1 .valid == 1 && loaded.1 .active == BitVec.ofBool bank) "Timed fixture did not commit"
      ensure (PairedImage.check p img ledger.active) "Actual accepted transcript is not certified"
      for (name, history, expected) in paths do
        let mut s := tick loaded (input 7)
        let mut reference := Pinwheel.Engine.Reactive.reset p
        ensure (actualView s (input) == Reactive.embed reference) "Reset did not establish the trace relation"
        for (edge, k) in history.zipIdx do
          let request : Values Loader.Machine.Input := input edge.command edge.incoming edge.reset
          ensure (request .init == 0 && request .command != 3) "Execution segment violates its rule"
          ensure (actualView s request == Reactive.embed reference) s!"Pre-edge mismatch: {bank}/{name}/{k}"
          s := tick s request
          reference := Pinwheel.Engine.Reactive.step p reference (edge.reset || edge.command == 7)
            (edge.command == 5) edge.incoming
          let observed := actualView s request
          ensure (observed == Reactive.embed reference) s!"Post-edge mismatch: {bank}/{name}/{k}"
          if name == "capture/branch/entry overwrite and maximum duration" then
            if k == 0 then
              -- Changing the terminal capture input must change this branch.
              let badCapture : Values Register := fun {_} r => match r with
                | .cached => s.1 .cached ^^^ 128 | other => s.1 other
              let correct := Pinwheel.Engine.Reactive.step p reference false false 1
              ensure (actualView (tick (badCapture, s.2) (input 0 1)) (input) != Reactive.embed correct)
                "Wrong terminal-capture input survived execution comparison"
              mutationChecks := mutationChecks + 1
            if k == 5 then
              -- Corrupt live state and execute another edge, rather than
              -- changing an already observed result of the comparison.
              let badCounter : Values Register := fun {_} r => match r with
                | .remaining => s.1 .remaining - 1 | other => s.1 other
              let badPins : Values Register := fun {_} r => match r with
                | .levels => s.1 .levels ^^^ 1 | other => s.1 other
              let badSample : Values Register := fun {_} r => match r with
                | .samples => s.1 .samples ^^^ 32768 | other => s.1 other
              let correct := Reactive.embed (Pinwheel.Engine.Reactive.step p reference false false 0)
              let mutations : List (Values Register × String) :=
                [(badCounter, "counter"), (badPins, "pin"), (badSample, "sample")]
              for (bad, label) in mutations do
                ensure (actualView (tick (bad, s.2) (input)) (input) != correct)
                  s!"Live {label} mutation survived the next edge"
                mutationChecks := mutationChecks + 1
            if k == 1 then
              ensure (observed.pc == 1 && !observed.samples[0] && observed.pins.levels == 6)
                "Branch did not use the terminal capture before the successor overwrote its slot"
            if k == 3 then ensure (observed.pc == 3) "Ready-at-deadline wait did not win"
            if k == 4 then ensure (observed.pc == 4) "Ready-at-deadline qualification did not win"
            if k == 5 then ensure (observed.remaining == 255) "Maximum duration was truncated"
            if k == 260 then ensure (observed.pc == 5 && observed.remaining == 0) "Maximum duration ended early"
          edges := edges + 1
        ensure (s.1 .mode == expected) s!"Timed path did not reach its expected outcome: {name}"
  IO.println s!"Paired timed controls: retained outputs; certified accepted transcripts; both active banks; {edges} before/after edge pairs; six scenarios; {mutationChecks} state/parameter mutations rejected."
