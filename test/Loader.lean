import Pinwheel
import Pinwheel.Hardware.Loader.Emit

open Pinwheel Pinwheel.Hardware

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def emit : IO Unit := do
  IO.FS.createDirAll "build/loader"
  match Loader.Machine.moduleText with
  | .ok text => IO.FS.writeFile "build/loader/atomic.mlir" text
  | .error e => throw (IO.userError e)
  let examples : List (String × Execution.Image) := [
    ("uart", Execution.widenProgram (Engine.Reactive.embedProgram (Compile.UART.program ⟨3⟩ 0x53))),
    ("spi", Execution.widenProgram (Engine.Reactive.embedProgram (Compile.SPI.program ⟨3⟩ 0xa6))),
    ("i2c-write", Execution.widenProgram (Compile.I2C.program ⟨3, 7⟩ ⟨0x53, 0xa6⟩)),
    ("i2c-read", Compile.I2CRead.program ⟨3, 7⟩ ⟨0x53, 0xa6⟩),
    ("uart-rx", Compile.UARTRx.program ⟨16, by decide, by decide, 0⟩),
    ("uart-rx-split", Compile.UARTRx.program ⟨257, by decide, by decide, 1⟩)]
  let lines := examples.map fun (name, p) =>
    name ++ " " ++ String.intercalate " " (([p.last.val, p.idle.levels.toNat, p.idle.enabled.toNat] ++
      (Execution.imageWords p).toList.map BitVec.toNat).map toString)
  IO.FS.writeFile "build/loader/images.txt" (String.intercalate "\n" lines ++ "\n")
  IO.println "Emitted atomic indexed loader and six compiler-produced images."

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
  let mut count := 0
  for line in (← IO.FS.lines "build/loader/vectors.txt") do
    let v ← numbers line
    let i : Loader.Machine.Inputs := ⟨v[0]! == 1, v[1]! == 1, BitVec.ofNat 3 v[2]!,
      BitVec.ofNat 64 v[3]!, BitVec.ofNat 2 v[4]!⟩
    let state : Loader.Machine.State := ⟨control, core, fun b => image banks[b.toNat]!⟩
    let ci := Loader.Machine.controlInput i state
    let gates := #[Loader.pushGate, Loader.commitGate, Loader.startGate, Loader.rejectedGate].map
      (fun e => (e.eval ci.values control.values).toNat)
    ensure (gates == v.extract 5 9) s!"Loader gates edge {count}: {gates} expected {v.extract 5 9}"
    -- Evaluate each structural component, using the proved wiring cut points.
    let cv : Values Loader.Register := Loader.circuit.step ci.values control.values
    control := ⟨(cv .active)[0], (cv .valid)[0], (cv .pending)[0], cv .cursor⟩
    let base := Loader.Machine.baseInput i state
    let selected := Loader.Machine.selected i state
    let read (address : BitVec 8) : BitVec 64 :=
      let ri : Loader.Store.Inputs := ⟨false, 0, 0, address⟩
      (Loader.Store.readExpr (.input Loader.Store.Input.address)).eval ri.values (state.memory selected)
    let base := {base with current := read core.pc}
    let target := Reactive.target.eval base.values core.values
    core := Reactive.tick {base with successor := read target} core
    for b in [false, true] do
      let mi := Loader.Machine.memoryInput i state b
      if mi.write then
        let mut raw := banks[b.toNat]!
        for ⟨_, r⟩ in Loader.Store.registers do
          let value := (Loader.Store.next r).eval mi.values (state.memory b)
          raw := raw.set! (Loader.Store.offset r).toNat (BitVec.ofNat 64 value.toNat)
        banks := banks.set! b.toNat raw
    ensure (snapshot control core == v.extract 9 20)
      s!"Loader state edge {count}: {snapshot control core} expected {v.extract 9 20}"
    count := count + 1
  IO.println s!"Atomic loader components matched {count} independent oracle edges."

def main (args : List String) : IO Unit := do
  if args == ["check"] then check
  else
    ensure args.isEmpty "usage: Loader.lean [check]"
    emit
