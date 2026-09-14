import Pinwheel
import Pinwheel.Hardware.Execution.Emit

open Pinwheel Pinwheel.Hardware Pinwheel.Hardware.Execution

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def numbers (line : String) : IO (Array Nat) :=
  (line.splitOn " ").toArray.mapM fun s => match s.toNat? with
    | some n => pure n | none => throw (IO.userError s!"invalid number {s}")

private def imageLine (name : String) (words : Words) (image : Indexed) : String :=
  name ++ " " ++ String.intercalate " " ((words.toList.map (toString ∘ BitVec.toNat)) ++
    (image.dictionary.toList.map (toString ∘ BitVec.toNat)) ++ (image.addresses.toList.map (toString ∘ BitVec.toNat)))

private def emit : IO Unit := do
  IO.FS.createDirAll "build/execution"
  for (name, moduleText) in [("decoder", decoderModule), ("direct", directModule), ("indexed", indexedModule)] do
    match moduleText with
    | .error e => throw (IO.userError e)
    | .ok text => IO.FS.writeFile s!"build/execution/{name}.mlir" text
  let mut images : Array String := #[]
  let mut storage := "image,distinct_records,logical_addresses,direct_bits,indexed_bits\n"
  let examples : List (String × Image) := [
    ("uart", widenProgram (Engine.Reactive.embedProgram (Compile.UART.program ⟨3⟩ 0x53))),
    ("spi", widenProgram (Engine.Reactive.embedProgram (Compile.SPI.program ⟨3⟩ 0xa6))),
    ("i2c-write", widenProgram (Compile.I2C.program ⟨3, 7⟩ ⟨0x53, 0xa6⟩)),
    ("i2c-read", Compile.I2CRead.program ⟨3, 7⟩ ⟨0x53, 0xa6⟩)]
  for (name, p) in examples do
    let words := imageWords p
    let some lowered := lowerIndexed words | throw (IO.userError s!"dictionary overflow: {name}")
    ensure (lowered.val.expand == words) "lowered lookup mismatch"
    for pc in [:256] do
      ensure (decode words[pc]! == some (p.fetch (Fin.ofNat 256 pc))) "typed record roundtrip"
    images := images.push (imageLine name words lowered.val)
    storage := storage ++ s!"{name},{words.toList.eraseDups.length},{p.last.val + 1},16384,5632\n"
  -- Read actual native V0 files and resolve both representations to the same E64 words.
  let some explicit ← pure (Binary.decodeBytes (← IO.FS.readBinFile "build/binary/i2c-explicit.pwl"))
    | throw (IO.userError "explicit V0 file rejected")
  let some counted ← pure (Binary.decodeBytes (← IO.FS.readBinFile "build/binary/i2c-counted.pwl"))
    | throw (IO.userError "counted V0 file rejected")
  ensure (lowerV0 explicit == lowerV0 counted && lowerV0 explicit == imageWords (widenProgram (Compile.I2C.program ⟨3, 7⟩ ⟨0x53, 0xa6⟩)))
    "V0 explicit/counted lowering changed instructions"
  let some countedLayout := lowerIndexed (lowerV0 counted) | throw (IO.userError "counted V0 overflow")
  images := images.push (imageLine "i2c-counted-v0" (lowerV0 counted) countedLayout.val)
  IO.FS.writeFile "build/execution/images.txt" (String.intercalate "\n" images.toList ++ "\n")
  IO.FS.writeFile "build/execution/storage.csv" storage
  let oversized : Words := Vector.ofFn fun k => BitVec.ofNat 64 k.val
  ensure ((lowerIndexed oversized).isNone) "dictionary overflow silently wrapped"
  let exactly64 : Words := Vector.ofFn fun k => BitVec.ofNat 64 (k.val % 64)
  ensure ((lowerIndexed exactly64).isSome) "64-entry dictionary rejected"
  let sixtyFive : Words := Vector.ofFn fun k => BitVec.ofNat 64 (k.val % 65)
  ensure ((lowerIndexed sixtyFive).isNone) "65-entry dictionary accepted"
  let mut roundtrips := 0
  for n in [:4096] do
    let f : Fields := {
      kind := BitVec.ofNat 3 (n % 5), levels := BitVec.ofNat 3 n, enabled := BitVec.ofNat 3 (n / 8)
      duration := BitVec.ofNat 8 n, budget := BitVec.ofNat 8 (255 - n % 256)
      check := BitVec.ofNat 4 (n / 3), entry := BitVec.ofNat 6 n, terminal := BitVec.ofNat 6 (n / 2)
      finish := BitVec.ofNat 2 (n % 3), sample := BitVec.ofNat 4 (n / 7)
      yes := BitVec.ofNat 8 (255 - n % 256), no := BitVec.ofNat 8 n }
    let some op := f.instruction | throw (IO.userError "synthetic typed instruction missing")
    ensure (decode (encode op) == some op && validValue (encode op)) "record/canonical checker disagreement"
    roundtrips := roundtrips + 1
  IO.println s!"Emitted decoder and two stores; {roundtrips} typed record roundtrips, five images, V0 lowering, and dictionary boundaries passed."

private def observedWord (f : {w : Nat} → Port w → BitVec w) : BitVec 64 :=
  pack ⟨f .kind, f .levels, f .enabled, f .duration, f .budget, f .check,
    f .entry, f .terminal, f .finish, f .sample, f .yes, f .no⟩

private def checkDecoder : IO Unit := do
  let mut count := 0
  for line in (← IO.FS.lines "build/execution/decoder-vectors.txt") do
    let n ← numbers line
    let word := BitVec.ofNat 64 n[0]!
    let iv : Values WordInput := fun .word => word
    let rv : Values Emit.NoRegister := fun r => nomatch r
    let actual : Values Port := decoderCircuit.observe iv rv
    ensure ((actual .valid).toNat == n[1]! && (observedWord actual).toNat == n[2]!) s!"independent decoder mismatch at {count}"
    ensure ((decode word).isSome == (n[1]! == 1)) s!"typed decoder mismatch at {count}"
    count := count + 1
  IO.println s!"Matched {count} independent raw decoder vectors in Lean."

private def checkStore (indexed : Bool) : IO Unit := do
  let name := if indexed then "indexed" else "direct"
  let mut words : Words := Vector.replicate 256 0
  let mut image : Indexed := ⟨Vector.replicate 64 0, Vector.replicate 256 0⟩
  let mut edge := 0
  let mut checked := 0
  let trace ← IO.FS.Handle.mk s!"build/execution/{name}-lean.csv" .write
  trace.putStrLn "edge,a_valid,a_word,b_valid,b_word"
  for line in (← IO.FS.lines s!"build/execution/{name}-vectors.txt") do
    let v ← numbers line
    let i : Inputs := ⟨v[0]! == 1, v[1]! == 1, v[2]! == 1, BitVec.ofNat 8 v[3]!,
      BitVec.ofNat 64 v[4]!, BitVec.ofNat 8 v[5]!, BitVec.ofNat 8 v[6]!⟩
    if indexed then
      let registers : Values IndexedReg := indexedCircuit.step i.values (indexedValues image)
      image := ⟨Vector.ofFn (fun k => registers (.word (BitVec.ofFin k))),
        Vector.ofFn (fun k => registers (.index (BitVec.ofFin k)))⟩
    else
      let registers : Values DirectReg := directCircuit.step i.values (directValues words)
      words := Vector.ofFn (fun k => registers (.word (BitVec.ofFin k)))
    if v[7]! == 1 then
      let actual : Values Output := if indexed then indexedCircuit.observe i.values (indexedValues image)
        else directCircuit.observe i.values (directValues words)
      let a : Values Port := fun p => actual (.a p)
      let b : Values Port := fun p => actual (.b p)
      let values := #[(a .valid).toNat, (observedWord a).toNat, (b .valid).toNat, (observedWord b).toNat]
      ensure (values == v.extract 8 12) s!"{name} memory/decoder mismatch at edge {edge}"
      trace.putStrLn (toString edge ++ "," ++ String.intercalate "," (values.toList.map toString))
      checked := checked + 1
    edge := edge + 1
  IO.println s!"Matched {name}: {edge} writes/read observations, {checked} checked pairs."

def main (args : List String) : IO Unit := do
  if args == ["check"] then
    checkDecoder
    checkStore false
    checkStore true
  else
    ensure args.isEmpty "usage: Execution.lean [check]"
    emit
