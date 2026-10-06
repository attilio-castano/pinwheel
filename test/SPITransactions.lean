import Pinwheel.Compile.SPITransaction
import Pinwheel.Hardware.Storage.PairedImage
import Lean

open Pinwheel Pinwheel.Hardware
open Lean (toJson)
open Pinwheel.Compile.SPITransaction (program)
open Pinwheel.SPI.Transaction (Config)

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def parameterSlot (fields : Execution.Fields) : BitVec 5 :=
  if fields.entry == 0 then 0 else BitVec.ofNat 5 ((fields.entry.toNat - 1) / 4 + 1)

/-- An untrusted bounded producer: slot zero is the no-capture parameter and
slots one through sixteen hold input-0 captures. PairedImage.check validates it. -/
private def lowered (p : Execution.Image) : Storage.PairedImage.Image := Id.run do
  let token (node : Storage.PairedImage.Node) : BitVec 32 := match node with
    | none => 7
    | some pc =>
      let f := Execution.fields (p.fetch pc.toFin)
      if f.kind == 4 then 4 else
        (0#2) ++ pc ++ parameterSlot f ++ f.duration ++ f.enabled ++ f.levels ++ f.kind
  return {
    parameters := Vector.ofFn fun k => if k.val == 0 then 0
      else if k.val ≤ 16 then BitVec.ofNat 20 (4 * (k.val - 1) + 1) else 0
    rows := Vector.ofFn fun k => if k.val ≤ p.last.val then
      token (Storage.PairedImage.successor p (BitVec.ofFin k) true) ++
        token (Storage.PairedImage.successor p (BitVec.ofFin k) false)
      else (4#32) ++ (4#32)
    boot := token (some 0)
    idle := p.idle.enabled ++ p.idle.levels }

private structure Fixture where
  name : String
  mode : Nat
  count : Nat
  half : Nat
  tx : Nat
  rx : Nat

private def cfg (f : Fixture) : Config :=
  ⟨⟨f.mode ≥ 2, f.mode % 2 = 1⟩,
    ⟨min (f.half - 1) 255, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩,
    ⟨min (f.count - 1) 1, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩

private def metadata (f : Fixture) : Lean.Json := Lean.Json.mkObj [
  ("name", toJson f.name), ("mode", toJson f.mode), ("byte_count", toJson f.count),
  ("half_cycles", toJson f.half), ("tx_payload", toJson f.tx), ("rx_payload", toJson f.rx),
  ("sample_slots", toJson (cfg f).bits), ("transfer_cycles", toJson (cfg f).transferCycles)]

private def validate (f : Fixture) : IO String := do
  ensure (f.mode < 4 && (f.count == 1 || f.count == 2) && 1 ≤ f.half && f.half ≤ 256)
    s!"Invalid SPI fixture: {f.name}"
  let c := cfg f
  let p := program c (BitVec.ofNat 16 f.tx)
  let words := Execution.imageWords p
  let distinct := words.toList.eraseDups.length
  ensure (p.last.val + 1 ≤ 34 && distinct ≤ 32) s!"SPI image capacity: {f.name}"
  let some indexed := Execution.lowerIndexed words | throw (IO.userError s!"Indexed lowering: {f.name}")
  ensure (indexed.val.expand == words) s!"Indexed certificate: {f.name}"
  let paired := lowered p
  ensure (Storage.PairedImage.check p paired (Storage.PairedImage.upload paired))
    s!"Paired certificate: {f.name}"
  let wrong := {paired with parameters := paired.parameters.set 0 (paired.parameters[0] ^^^ 1)}
  ensure (!(Storage.PairedImage.check p wrong (Storage.PairedImage.upload wrong)))
    s!"Wrong capture parameter certified: {f.name}"
  for pc in [:256] do
    ensure (Execution.decode words[pc]! == some (p.fetch (BitVec.ofNat 8 pc).toFin))
      s!"E64 decode: {f.name}/{pc}"
  return f.name ++ " " ++ String.intercalate " " (([p.last.val, p.idle.levels.toNat,
    p.idle.enabled.toNat] ++ words.toList.map BitVec.toNat).map toString)

private def baseline : List Fixture := (List.range 4).flatMap fun mode =>
  [⟨s!"spi-mode{mode}-1byte", mode, 1, 4, 0xa6, 0x96⟩,
   ⟨s!"spi-mode{mode}-2bytes", mode, 2, 4, 0xa653, 0x963c⟩]

private def matrix : List Fixture := (List.range 4).flatMap fun mode =>
  [⟨s!"spi-mode{mode}-2bytes-h3", mode, 2, 3, 0x00ff, 0xff00⟩,
   ⟨s!"spi-mode{mode}-1byte-h6", mode, 1, 6,
     if mode % 2 == 0 then 0x00 else 0xff, if mode % 2 == 0 then 0xff else 0x00⟩,
   ⟨s!"spi-mode{mode}-2bytes-h256", mode, 2, 256, 0xffff, 0x0000⟩]

private def emit (out : System.FilePath) (stem : String) (fixtures : List Fixture) : IO Unit := do
  let lines ← fixtures.mapM validate
  IO.FS.writeFile (out / (stem ++ "images.txt")) (String.intercalate "\n" lines ++ "\n")
  IO.FS.writeFile (out / (stem ++ "metadata.json"))
    ((Lean.Json.arr (fixtures.map metadata).toArray).pretty ++ "\n")

def main (args : List String) : IO Unit := do
  let out : System.FilePath ← match args with
    | [] => pure "build/spi-transactions"
    | [path] => pure path
    | _ => throw (IO.userError "usage: SPITransactions.lean [output-directory]")
  IO.FS.createDirAll out
  emit out "" baseline
  emit out "matrix" matrix
  IO.println "SPI transactions: 20 compiler images, all modes, one/two bytes, H3/4/6/256; E64 decoding, bounded indexed/paired lowering and wrong-capture controls passed."
