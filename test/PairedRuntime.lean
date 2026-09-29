import Pinwheel.Hardware.Storage.PairedRuntime

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
    | 0 => .action ⟨⟨1, 7⟩, 2, some ⟨0, 1⟩⟩
    | 1 => .wait ⟨⟨2, 3⟩, ⟨1, true⟩, 2⟩
    | 2 => .checked ⟨⟨⟨3, 7⟩, 1, some ⟨0, 4⟩⟩, ⟨2, 2⟩,
        some ⟨0, 7⟩, .branch 7 3 5⟩
    | 3 => .qualify ⟨⟨4, 5⟩, ⟨3, 3⟩, 1, 2⟩
    | _ => .halt
  idle := ⟨5, 2⟩
  last := 4 }

-- Test-only image construction. The independent certificate checks every
-- source field, parameter, row and successor, including the invalid target 5.
private def token (node : PairedImage.Node) : BitVec 32 :=
  match node with
  | none => 7
  | some pc =>
    let f := PairedImage.fields program pc
    if f.kind == 4 then 4 else
      (0#2) ++ pc ++ (BitVec.ofNat 5 pc.toNat) ++ f.duration ++ f.enabled ++ f.levels ++ f.kind

private def image : PairedImage.Image := {
  parameters := Vector.ofFn fun k => PairedImage.parameter (PairedImage.fields program (BitVec.ofNat 8 k.val))
  rows := Vector.ofFn fun k =>
    if k.val ≤ program.last.val then
      token (PairedImage.successor program (BitVec.ofFin k) true) ++
        token (PairedImage.successor program (BitVec.ofFin k) false)
    else (4#32) ++ (4#32)
  boot := token (some 0)
  idle := program.idle.enabled ++ program.idle.levels }

private def owned (s : State) : Bool :=
  if s.1 .mode != 0 && (s.1 .mode).toNat < 5 then
    let word := s.1 .current
    s.1 .valid == 1 &&
      s.1 .cached == s.1 (.parameter (s.1 .active == 1) (PairedImage.index word)) &&
      s.1 .cached == image.parameters[(PairedImage.index word).toNat] &&
      s.2.q == s.2.contents (s.1 .active ++ PairedImage.row word) &&
      s.2.q == image.rows[(PairedImage.row word).toNat] &&
      decide (PairedImage.Matches program image (some (PairedImage.row word)) word)
  else true

private def agrees (s : State) (reference : Reactive.Model) : Bool :=
  let r := Reactive.embed reference
  s.1 .mode == r.mode && s.1 .levels == r.pins.levels && s.1 .enabled == r.pins.enabled &&
    s.1 .remaining == r.remaining && s.1 .waitLeft == r.waitLeft &&
    (Vector.ofFn (fun k : Fin 16 => (s.1 .samples)[k.val])) == r.samples &&
    (r.mode == 0 || 5 ≤ r.mode.toNat || PairedImage.row (s.1 .current) == r.pc)

private structure Edge where
  command : BitVec 3 := 0
  incoming : BitVec 2 := 0
  reset : Bool := false

-- Each path starts from the committed image; loader commands while busy must
-- leave execution alone. Expected terminal modes prevent a vacuous short path.
private def scenarios : List (String × List Edge × BitVec 3) := [
  ("capture/branch/qualify/halt", [⟨5,1,false⟩, ⟨1,0,false⟩, ⟨2,0,false⟩,
    ⟨5,0,false⟩, ⟨3,0,false⟩, ⟨4,2,false⟩, ⟨0,2,false⟩, ⟨0,3,false⟩,
    ⟨0,3,false⟩, ⟨0,0,false⟩, ⟨0,3,false⟩, ⟨0,3,false⟩, ⟨0,0,false⟩], 5),
  ("wait timeout", [⟨5,0,false⟩, {}, {}, {}, {}, {}, {}], 6),
  ("guard fault", [⟨5,0,false⟩, {}, {}, {}, ⟨0,2,false⟩, {}], 7),
  ("false branch/out of range", [⟨5,1,false⟩, {}, {}, {}, ⟨0,2,false⟩,
    ⟨0,2,false⟩, ⟨0,2,false⟩], 7),
  ("qualify timeout", [⟨5,1,false⟩, {}, {}, {}, ⟨0,2,false⟩,
    ⟨0,2,false⟩, ⟨0,3,false⟩, {}, {}, {}], 6),
  ("reset and restart", [⟨5,1,false⟩, ⟨5,3,true⟩, ⟨5,0,false⟩, {},
    ⟨7,3,false⟩, ⟨5,1,false⟩, ⟨0,0,true⟩], 0)]

def main : IO Unit := do
  ensure (PairedImage.check program image (PairedImage.upload image)) "Fixture image failed its E64 certificate"
  let .ok n := PairedValidation.core | throw (IO.userError "Retained constructor failed")
  let c := PairedClosed.model n.component
  let tick (s : State) (i : Values Loader.Machine.Input) : State := freeze (c.step i s)
  let mut loaded : State := (fun {w} _ => BitVec.ofNat w 0x55, ⟨fun _ => 0xdeadbeef, 0x12345678⟩)
  loaded := tick loaded (input (init := true))
  let mut edges := 0
  let mut runningEdges := 0
  for bank in [true, false] do
    loaded := tick loaded (input 1)
    for word in PairedImage.upload image do loaded := tick loaded (input 2 (data := word))
    loaded := tick loaded (input 3)
    ensure (loaded.1 .active == BitVec.ofBool bank && loaded.1 .valid == 1) "Runtime image did not commit"
    for (name, history, expected) in scenarios do
      let mut s := loaded
      let mut reference := Pinwheel.Engine.Reactive.reset program
      for (edge, k) in history.zipIdx do
        let before := s
        s := tick s (input edge.command edge.incoming edge.reset)
        reference := Pinwheel.Engine.Reactive.step program reference (edge.reset || edge.command == 7)
          (edge.command == 5) edge.incoming
        ensure (owned s) s!"Runtime ownership: {bank}/{name}/{k}"
        ensure (agrees s reference) s!"Reference mismatch: {bank}/{name}/{k}; mode {(s.1 .mode).toNat}; expected {repr reference}"
        if s.1 .mode != 0 && (s.1 .mode).toNat < 5 then runningEdges := runningEdges + 1
        else ensure (s.2.q == before.2.q) s!"Stopped Q did not hold: {bank}/{name}/{k}"
        edges := edges + 1
      ensure (s.1 .mode == expected) s!"Scenario did not reach expected stop: {name}"
    let started := tick loaded (input 5 1)
    let waited := tick (tick (tick started (input)) (input)) (input)
    ensure (owned started && owned waited && started.2.q != waited.2.q) "Old/new row control not discriminating"
    ensure (!owned (waited.1, {waited.2 with q := started.2.q})) "Stale Q mutation survived"
    let badCache : Values Register := fun {_} r => match r with
      | .cached => waited.1 .cached ^^^ 1 | other => waited.1 other
    ensure (!owned (badCache, waited.2)) "Wrong parameter mutation survived"
    let badToken : Values Register := fun {_} r => match r with
      | .current => waited.1 .current ^^^ 0x40000000 | other => waited.1 other
    ensure (!owned (badToken, waited.2)) "Invalid source token mutation survived"
  IO.println s!"Paired runtime controls: retained core; certified image; both active banks; {edges} reference edges; {runningEdges} running edges; six scenarios; stale-Q/parameter/token mutations rejected."
