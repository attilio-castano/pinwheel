import Pinwheel
import Pinwheel.Hardware.Storage.RepetitionEmit

open Pinwheel Pinwheel.Hardware

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def numbers (line : String) : IO (Array Nat) :=
  (line.splitOn " ").toArray.mapM fun s => match s.toNat? with
    | some n => pure n | none => throw (IO.userError s!"invalid number {s}")

private def image (raw : Vector (BitVec 64) 322) : Loader.Store.Image :=
  fun {w} r => raw[(Loader.Store.offset r).toNat]!.extractLsb' 0 w

private def snapshot (s : Loader.State) (core : Reactive.State) : Array Nat :=
  #[s.active.toNat, s.valid.toNat, s.pending.toNat, s.cursor.toNat,
    core.mode.toNat, core.pc.toNat, core.remaining.toNat, core.waitLeft.toNat,
    core.pins.levels.toNat, core.pins.enabled.toNat,
    (List.range 16).foldl (fun acc k => acc + if core.samples[k]! then 2^k else 0) 0]

private def check : IO Unit := do
  let mut banks := #[Vector.replicate 322 (0#64), Vector.replicate 322 (0#64)]
  let mut control : Loader.State := {}
  let mut core : Reactive.State := ⟨0, 0, 0, 0, {}, Vector.replicate 16 false⟩
  let mut cached := 0#64
  let mut count := 0
  for line in (← IO.FS.lines "build/storage/repetition/vectors.txt") do
    let v ← numbers line
    let i : Loader.Machine.Inputs := ⟨v[0]! == 1, v[1]! == 1, BitVec.ofNat 3 v[2]!,
      BitVec.ofNat 64 v[3]!, BitVec.ofNat 2 v[4]!⟩
    let state : Loader.Machine.State := ⟨control, core, fun b => image banks[b.toNat]!⟩
    let ci := Storage.Repetition.host (Loader.Machine.controlInput i state) state.control.cursor
    let gates := #[Loader.pushGate, Loader.commitGate, Loader.startGate, Loader.rejectedGate].map
      (fun e => (e.eval ci.values control.values).toNat)
    ensure (gates == v.extract 5 9) s!"Loader gates edge {count}: {gates} expected {v.extract 5 9}"
    -- Evaluate each structural component, using the proved wiring cut points.
    let cv : Values Loader.Register := Loader.circuit.step ci.values control.values
    control := ⟨(cv .active)[0], (cv .valid)[0], (cv .pending)[0], cv .cursor⟩
    let base := Loader.Machine.baseInput i state
    let selected := Loader.Machine.selected i state
    let read (address : BitVec 8) : BitVec 64 :=
      let raw := banks[selected.toNat]!
      let m : Storage.Repetition.Image := {
        templates := Vector.ofFn fun k => raw[k.val]!
        bytes := Vector.ofFn fun k => (raw[15+k.val]!).extractLsb' 0 8
        descriptors := Vector.ofFn fun k => (raw[17+k.val]!).extractLsb' 0 8 }
      Storage.Repetition.reader.eval (fun .address => address) m.values
    let base := {base with current := cached}
    let target := Reactive.target.eval base.values core.values
    core := Reactive.tick {base with successor := read target} core
    if !Reactive.runningValue state.core || core.pc != state.core.pc then cached := read target
    if Reactive.runningValue core then
      ensure (cached == read core.pc && cached.toNat == v[20]!) s!"Cache invariant edge {count}"
    for b in [false, true] do
      let mi : Loader.Store.Inputs := ⟨Loader.push ci state.control && (b != state.control.active), state.control.cursor, i.data, 0⟩
      if mi.write then
        let mut raw := banks[b.toNat]!
        let rv : Values Storage.Repetition.BankRegister := fun {w} r =>
          (raw[(Storage.Repetition.offset r).toNat]!).extractLsb' 0 w
        for ⟨_, r⟩ in Storage.Repetition.bankRegisters do
          let value := (Storage.Repetition.next r).eval mi.values rv
          raw := raw.set! (Storage.Repetition.offset r).toNat (BitVec.ofNat 64 value.toNat)
        banks := banks.set! b.toNat raw
    ensure (snapshot control core == v.extract 9 20)
      s!"Loader state edge {count}: {snapshot control core} expected {v.extract 9 20}"
    count := count + 1
  IO.println s!"Repetition loader components matched {count} independent oracle edges."

def main : IO Unit := check
