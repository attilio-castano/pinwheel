import Pinwheel.Hardware.Storage.PairedCoverage

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

private def fixture (variant : Bool) : PairedImage.Image :=
  ⟨Vector.ofFn (fun k => BitVec.ofNat 20 (if variant then 63 - k.val else k.val)),
    Vector.ofFn (fun k => (4 : BitVec 32) ++
      (if variant || k.val == 255 then (7 : BitVec 32) else 4)),
    BitVec.ofNat 32 (255 * 2^22 + (if variant then 0 else 31) * 2^17),
    if variant then 21 else 45⟩

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
  let observe (s : State) (i : Values Loader.Machine.Input) : Values Loader.Machine.Output := c.observe i s
  let mut s : State := (fun {w} _ => BitVec.ofNat w 0x55, ⟨fun _ => 0xdeadbeef, 0x12345678⟩)
  s := tick s (input 0 0 1)
  ensure (s.1 .valid == 0 && s.1 .pending == 0 && s.1 .cursor == 0 &&
    s.2.contents 0 == 0xdeadbeef && s.2.q == 0x12345678) "Initialization fabricated a known image or cleared memory"
  s := tick s (input 3)
  ensure (s.1 .valid == 0) "Empty commit accepted"
  s := tick s (input 1)
  ensure (observe s (input 2 0x100000) (.control .rejected) == 1) "Invalid parameter not rejected"
  s := tick s (input 2 0x100000)
  ensure (s.1 .cursor == 0) "Rejected word advanced cursor"
  let a := fixture false
  let b := fixture true
  let words := PairedImage.upload a
  for (word, k) in (words.take 289).zipIdx do
    if k == 32 || k == 288 then
      let bad : BitVec 64 := if k == 32 then 0xc0000000 else 0x100000000
      ensure (observe s (input 2 bad) (.control .rejected) == 1) "Malformed row/boot accepted"
      s := tick s (input 2 bad)
      ensure ((s.1 .cursor).toNat == k) "Malformed row/boot advanced cursor"
    ensure (observe s (input 2 word) (.control .push) == 1) "Valid upload refused"
    s := tick s (input 2 word)
  ensure (s.1 .cursor == 289 && s.1 .valid == 0) "Partial image became valid"
  ensure (observe s (input 2 64) (.control .rejected) == 1) "Malformed idle accepted"
  s := tick s (input 2 64)
  ensure (observe s (input 3) (.control .commit) == 0) "Short upload committed"
  s := tick s (input 3)
  ensure (s.1 .cursor == 289 && s.1 .pending == 1) "Short commit destroyed staging"
  s := tick s (input 2 (words.getD 289 0))
  ensure (s.1 .cursor == 290) "Last idle word not counted"
  ensure (observe s (input 2 0) (.control .push) == 0) "Extra word accepted"
  s := tick s (input 2 0)
  ensure (s.1 .cursor == 290 && s.2.q == 0x12345678) "Full upload wrapped cursor or changed Q"
  s := tick s (input 3)
  ensure (s.1 .valid == 1 && s.1 .active == 1 && s.1 .pending == 0) "Complete image not committed"
  imageAt s true a
  s := tick s (input 5)
  ensure (s.1 .current == a.boot && s.2.q == a.rows[255]!) "Start read used stale Q or wrong row"
  s := tick s (input 1)
  ensure (s.1 .pending == 0 && s.1 .current == 7) "Busy begin was accepted or old Q was not used"
  s := tick s (input 1)
  for word in (PairedImage.upload b).take 33 do s := tick s (input 2 word)
  imageAt s true a
  s := tick s (input 4)
  ensure (s.1 .pending == 0 && s.1 .cursor == 0) "Abort left an accepted prefix"
  s := tick s (input 3)
  ensure (s.1 .active == 1) "Aborted upload committed"
  s := tick s (input 1)
  s := tick s (input 2 1)
  s := tick s (input 0 0 0 1)
  ensure (s.1 .pending == 0 && s.1 .valid == 1 && s.1 .active == 1) "Reset broke image ownership"
  imageAt s true a
  s := tick s (input 1)
  s := tick s (input 2 1)
  s := tick s (input 7)
  ensure (s.1 .cursor == 0 && s.1 .pending == 0 && s.1 .valid == 1) "Reset command broke ownership"
  s := tick s (input 1)
  s := tick s (input 2 1)
  s := tick s (input 1)
  ensure (s.1 .cursor == 0 && s.1 .pending == 1) "Begin did not restart the accepted prefix"
  for word in PairedImage.upload b do
    ensure (observe s (input 2 word) (.control .push) == 1) "Replacement upload refused"
    s := tick s (input 2 word)
  s := tick s (input 3)
  ensure (s.1 .active == 0 && s.1 .valid == 1) "Replacement did not switch banks"
  imageAt s false b
  imageAt s true a
  s := tick s (input 0 0 1)
  ensure (s.1 .valid == 0 && s.1 .pending == 0) "Reinitialization retained ownership"
  imageAt s false b
  imageAt s true a
  IO.println "Paired upload controls: retained core; two complete images; rejected/short/extra/busy/abort/reset/restart controls; all banks and metadata; row 255 and old Q; arbitrary initial storage."
