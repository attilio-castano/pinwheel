import Pinwheel

open Pinwheel Pinwheel.Hardware

private instance : Inhabited Raw.Program := ⟨⟨Vector.replicate 32 0x8000, 0⟩⟩

private def ensure (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

private def imageLine (name : String) (duration byte : Nat) (p : Raw.Program) : String :=
  s!"{name} {duration} {byte} {p.idle.toNat} " ++
    String.intercalate " " (p.memory.toList.map (fun w => toString w.toNat))

private def emit : IO Unit := do
  IO.FS.createDirAll "build/core"
  for (name, moduleText) in [("decoder", Emit.decoder), ("core", Emit.core)] do
    match moduleText with
    | .error e => throw (IO.userError e)
    | .ok text => IO.FS.writeFile s!"build/core/{name}.mlir" text
  let mut images : Array String := #[]
  for d in ([0, 3, 255] : List (Fin 256)) do
    for byte in [:256] do
      if d.val != 255 || [0, 83, 166, 255].contains byte then
        images := images.push (imageLine "uart" (d.val + 1) byte (Raw.encodeProgram (Compile.UART.program ⟨d⟩ (BitVec.ofNat 8 byte))))
        images := images.push (imageLine "spi" (d.val + 1) byte (Raw.encodeProgram (Compile.SPI.program ⟨d⟩ (BitVec.ofNat 8 byte))))
  let custom := fun (words : List (BitVec 16)) (idle : Engine.Levels) =>
    Raw.Program.mk (Vector.ofFn (fun k => words[k.val]?.getD 0x8000)) idle
  let action := fun (levels duration slot : Nat) =>
    BitVec.ofNat 16 (levels * 4096 + (duration - 1) * 16 + (if slot < 8 then 8 + slot else 0))
  images := images.push (imageLine "two" 0 0 (custom [action 1 1 0, action 6 1 7] 7))
  images := images.push (imageLine "mixed" 0 0 (custom [action 1 1 0, action 6 4 7, action 3 256 0, action 0 1 8] 7))
  images := images.push (imageLine "halt0" 0 0 (custom [] 6))
  images := images.push (imageLine "halt31" 0 0 (custom (List.replicate 31 (action 3 1 8)) 0))
  images := images.push (imageLine "overflow" 0 0 (custom (List.replicate 32 (action 3 1 8)) 0))
  for (name, word) in [("bad_halt", 0x8001), ("bad_slot", 1), ("bad_high", 0xffff)] do
    images := images.push (imageLine name 0 0 (custom [action 2 1 0, word] 5))
  IO.FS.writeFile "build/core/images.txt" (String.intercalate "\n" images.toList ++ "\n")
  -- Both the structural interpretation and the functional decoder are exercised exhaustively.
  for n in [:65536] do
    let word := BitVec.ofNat 16 n
    let inputs : Values Emit.WordInput := fun p => match p with | .word => word
    let registers : Values Emit.NoRegister := fun r => nomatch r
    let fields := Decode.observe (Emit.decoderCircuit.observe inputs registers)
    ensure (fields.instruction == Encoding.decode word) s!"decoder mismatch at {n}"
  IO.println s!"Emitted core/decoder circuits and {images.size} images; checked all 65,536 decoder words."

private def numbers (line : String) : IO (Array Nat) := do
  (line.splitOn " ").toArray.mapM (fun s => match s.toNat? with
    | some n => pure n | none => throw (IO.userError s!"invalid numeric field: {s}"))

private def check : IO Unit := do
  let mut images : Array Raw.Program := #[]
  for line in (← IO.FS.lines "build/core/images.txt") do
    let ns ← numbers (String.intercalate " " (line.splitOn " ").tail)
    images := images.push ⟨Vector.ofFn (fun k => BitVec.ofNat 16 ns[k.val + 3]!), BitVec.ofNat 3 ns[2]!⟩
  let seed := images[0]!
  let mut state := Core.embed seed (Raw.reset seed)
  let mut edge := 0
  let output ← IO.FS.Handle.mk "build/core/lean.csv" .write
  output.putStrLn "edge,valid,status,pc,remaining,active,levels,rx"
  for line in (← IO.FS.lines "build/core/stimuli.txt") do
    let v ← numbers line
    ensure (v.size == 14) "stimulus width"
    let flags := v[0]!
    let i : Core.Inputs := {
      init := flags.testBit 0
      reset := flags.testBit 1
      start := flags.testBit 2
      commit := flags.testBit 3
      sample := flags.testBit 4
      image := images[v[1]!]! }
    state := Core.tick i state
    let actual := #[if state.valid then 1 else 0, state.status.toNat, state.pc.toNat,
      state.timer.remaining.toNat, state.timer.active.toNat, state.levels.toNat,
      (Engine.samplesByte state.samples).toNat]
    ensure (actual == v.extract 2 9) s!"core mismatch at edge {edge}: {actual} expected {v.extract 2 9}"
    if v[9]! != 0 then
      ensure (state.program.memory == images[v[10]!]!.memory) s!"memory changed at edge {edge}"
    ensure (state.program.idle.toNat == v[11]!) s!"idle register mismatch at edge {edge}"
    ensure (decide (state.status == 1) == (v[12]! == 1)) s!"busy mismatch at edge {edge}"
    ensure (decide (state.status == 2) == (v[13]! == 1)) s!"completion mismatch at edge {edge}"
    output.putStrLn (toString edge ++ "," ++ String.intercalate "," (actual.toList.map toString))
    edge := edge + 1
  IO.println s!"Matched independent deadline oracle on {edge} structural core edges."

def main (args : List String) : IO Unit := do
  if args == ["check"] then check else emit
