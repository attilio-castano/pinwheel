import Pinwheel
import Pinwheel.Hardware.Reactive.Emit

open Pinwheel Pinwheel.Hardware

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def emit : IO Unit := do
  IO.FS.createDirAll "build/reactive-core"
  for (name, result) in [("direct", Reactive.Core.directModule), ("indexed", Reactive.Core.indexedModule)] do
    match result with
    | .ok text => IO.FS.writeFile s!"build/reactive-core/{name}.mlir" text
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
  IO.FS.writeFile "build/reactive-core/images.txt" (String.intercalate "\n" lines ++ "\n")
  IO.println "Emitted both integrated reactive cores and six compiler-produced images."

private def numbers (line : String) : IO (Array Nat) :=
  (line.splitOn " ").toArray.mapM fun s => match s.toNat? with
    | some n => pure n | none => throw (IO.userError s!"invalid number {s}")

/-- Evaluate the same named component boundaries used by the integrated emitter. -/
private def structuralStep (state : Reactive.State) (idle : Engine.Reactive.Pins) (last : BitVec 8)
    (read : BitVec 8 → BitVec 64) (request : Reactive.Request) : Reactive.State :=
  let base : Reactive.Inputs := ⟨request.reset, request.start, request.incoming, idle, last, read state.pc, 4⟩
  let address := Reactive.target.eval base.values state.values
  Reactive.tick {base with successor := read address} state

private def snapshot (s : Reactive.State) : Array Nat :=
  #[s.mode.toNat, s.pc.toNat, s.remaining.toNat, s.waitLeft.toNat, s.pins.levels.toNat,
    s.pins.enabled.toNat, (List.range 16).foldl (fun acc k => acc + if s.samples[k]! then 2^k else 0) 0]

private def check (indexed : Bool) : IO Unit := do
  let name := if indexed then "indexed" else "direct"
  let mut words : Execution.Words := Vector.replicate 256 0
  let mut image : Execution.Indexed := ⟨Vector.replicate 64 0, Vector.replicate 256 0⟩
  let mut idle : Engine.Reactive.Pins := {}
  let mut last : BitVec 8 := 0
  let mut state : Reactive.State := ⟨0, 0, 0, 0, {}, Vector.replicate 16 false⟩
  let mut count := 0
  for line in (← IO.FS.lines s!"build/reactive-core/{name}-vectors.txt") do
    let v ← numbers line
    let i : Reactive.Core.Inputs := ⟨⟨v[0]! == 1, v[1]! == 1, BitVec.ofNat 2 v[2]!⟩,
      v[3]! == 1, BitVec.ofNat 2 v[4]!, BitVec.ofNat 8 v[5]!, BitVec.ofNat 64 v[6]!⟩
    let before := state
    let read := fun address =>
      let ri : Execution.Inputs := ⟨false, false, false, 0, 0, address, 0⟩
      if indexed then (Execution.indexedRead (.input .readA)).eval ri.values (Execution.indexedValues image)
      else (Execution.directRead (.input .readA)).eval ri.values (Execution.directValues words)
    state := structuralStep before idle last read i.request
    if i.write && !Reactive.runningValue before && !i.request.reset && !i.request.start then
      if i.bank == 2 then
        if i.address == 0 then idle := ⟨i.data.extractLsb' 0 3, i.data.extractLsb' 3 3⟩
        else if i.address == 1 then last := i.data.extractLsb' 0 8
      else if i.bank.toNat < 2 then
        let write : Execution.Inputs := ⟨true, false, i.bank == 1, i.address, i.data, 0, 0⟩
        if indexed then image := Execution.indexedTick write image else words := Execution.directTick write words
    if v[7]! == 1 then ensure (snapshot state == v.extract 8 15) s!"{name} structural mismatch edge {count}: {snapshot state}, expected {v.extract 8 15}"
    count := count + 1
  IO.println s!"{name}: structural scheduler and store reads matched {count} independent oracle edges."

def main (args : List String) : IO Unit := do
  if args == ["check"] then
    check false
    check true
  else
    ensure args.isEmpty "usage: ReactiveCore.lean [check]"
    emit
