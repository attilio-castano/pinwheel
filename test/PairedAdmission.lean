import Pinwheel.Hardware.Storage.PairedSession

open Pinwheel.Hardware Pinwheel.Hardware.Storage PairedController

private abbrev State := Values Register × Memory.Sram.State 9 64

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def input (command : BitVec 3) (data : BitVec 64 := 0)
    (init : BitVec 1 := 0) (reset : BitVec 1 := 0) : Values Loader.Machine.Input
  | _, .command => command | _, .data => data | _, .init => init | _, .reset => reset | _, .incoming => 0

-- Force each state once so long histories do not repeatedly evaluate old
-- register closures. This snapshots all registers and all 512 physical words.
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

-- Two permutations exercise producer-chosen parameter locations. Unused
-- slots deliberately contain values that would fail some token checks.
private def slot (variant : Bool) (pc : BitVec 8) : BitVec 5 :=
  BitVec.ofNat 5 (if variant then pc.toNat + 17 else 31 - pc.toNat)

private def token (variant : Bool) (node : PairedImage.Node) : BitVec 32 :=
  match node with
  | none => 7
  | some pc =>
    let f := PairedImage.fields program pc
    if f.kind == 4 then 4 else
      (0#2) ++ pc ++ slot variant pc ++ f.duration ++ f.enabled ++ f.levels ++ f.kind

private def fixture (variant : Bool) : PairedImage.Image := {
  parameters := Vector.ofFn fun k =>
    let pc := if variant then (k.val + 15) % 32 else 31 - k.val
    if pc < 6 then PairedImage.parameter (PairedImage.fields program (BitVec.ofNat 8 pc)) else 0xfffff
  rows := Vector.ofFn fun k =>
    if k.val ≤ program.last.val then
      token variant (PairedImage.successor program (BitVec.ofFin k) true) ++
        token variant (PairedImage.successor program (BitVec.ofFin k) false)
    else (4#32) ++ (4#32)
  boot := token variant (some 0)
  idle := program.idle.enabled ++ program.idle.levels }

private def imageAt (s : State) (bank : Bool) (image : PairedImage.Image) : IO Unit := do
  for k in [:32] do
    ensure (s.1 (.parameter bank (BitVec.ofNat 5 k)) == image.parameters[k]!) s!"Parameter {bank}/{k}"
  for k in [:256] do
    ensure (s.2.contents (Memory.Sram.bankAddress bank (BitVec.ofNat 8 k)) == image.rows[k]!) s!"Row {bank}/{k}"
  ensure (s.1 (.boot bank) == image.boot && s.1 (.idle bank) == image.idle) s!"Metadata {bank}"

def main : IO Unit := do
  let .ok n := PairedValidation.core | throw (IO.userError "Retained constructor failed")
  let c := PairedClosed.model n.component
  let tick (s : State) (i : Values Loader.Machine.Input) : State := freeze (c.step i s)
  let mut s : State := (fun {w} _ => BitVec.ofNat w 0xfffff, ⟨fun _ => 0xfeedface, 0x12345678⟩)
  s := tick s (input 0 0 1)
  let mut pushes := 0
  let mut quietEdges := 0
  let mut refusals := 0
  let mut certificateRefusals := 0
  for variant in [false, true] do
    let img := fixture variant
    ensure (PairedImage.check program img (PairedImage.upload img)) "Permuted image is not certified"
    -- A canonical but wrong guard is a source-certificate failure; it is not
    -- claimed to be a hardware syntax rejection.
    let guardSlot := (slot variant 3).toFin
    let wrong := {img with parameters := img.parameters.set guardSlot.val (img.parameters[guardSlot.val] ^^^ 4096)}
    ensure (!(PairedImage.check program wrong (PairedImage.upload wrong))) "Wrong guard certified"
    certificateRefusals := certificateRefusals + 1
    let oldActive := s.1 .active
    let oldBank := oldActive == 1
    s := tick s (input 1 0xbeef)
    for (word, k) in (PairedImage.upload img).zipIdx do
      if k % 7 == 0 then
        for _ in [:2] do
          let q : Values Loader.Machine.Input := input 0 0xffffffffffffffff
          ensure (c.observe q s (.control .push) == 0) "Quiet data became a push"
          s := tick s q
          ensure ((s.1 .cursor).toNat == k) "Quiet gap advanced the cursor"
          quietEdges := quietEdges + 1
      if k == 32 then
        let badRegisters : Values Register := fun {_} r => match r with
          | .parameter b address =>
            if b != oldBank && address == slot variant 1 then 2 else s.1 (.parameter b address)
          | other => s.1 other
        let bad : State := (badRegisters, s.2)
        let request : Values Loader.Machine.Input := input 2 word
        ensure (c.observe request bad (.control .push) == 0 &&
          c.observe request bad (.control .rejected) == 1) "Bad inactive capture passed row validation"
        let refused := tick bad request
        ensure (refused.1 .cursor == 32 && refused.1 .active == oldActive)
          "Executed row rejection changed upload progress or active bank"
        refusals := refusals + 1
      if k == 289 then
        let short := tick s (input 3)
        ensure (c.observe (input 3) s (.control .commit) == 0 &&
          short.1 .cursor == 289 && short.1 .active == oldActive) "Short upload committed"
        refusals := refusals + 1
      let request : Values Loader.Machine.Input := input 2 word
      ensure (c.observe request s (.control .push) == 1 &&
        c.observe request s (.control .rejected) == 0) s!"Certified word refused: {variant}/{k}"
      s := tick s request
      ensure ((s.1 .cursor).toNat == k + 1 && s.1 .active == oldActive) "Accepted prefix drifted"
      pushes := pushes + 1
    ensure (c.observe (input 3) s (.control .commit) == 1) "Complete certified image refused commit"
    s := tick s (input 3 0xcafe)
    ensure (s.1 .active == ~~~oldActive && s.1 .valid == 1 && s.1 .pending == 0 &&
      s.1 .cursor == 0) "Commit failed to install the image"
    imageAt s (!oldBank) img
    ensure (PairedTimed.observe (c.observe (input 0) s) == Reactive.embed (Pinwheel.Engine.Reactive.reset program))
      "Commit did not establish ready E64 state without reset"
    if variant then imageAt s true (fixture false)
  IO.println s!"Paired admission controls: retained core; two certified parameter permutations; {pushes} accepted pushes; {quietEdges} quiet edges; {refusals} executed refusals; {certificateRefusals} wrong-source certificates rejected; commit establishes E64 without reset."
