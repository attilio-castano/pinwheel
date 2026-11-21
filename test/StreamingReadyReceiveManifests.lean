import Pinwheel.Program.StreamingReadyManifest
import Pinwheel.Program.StreamingReadyReceiveImages

open Lean
open Pinwheel.Program.StreamingReadyManifest
open Pinwheel.Program.StreamingReadyReceiveImages
open Pinwheel.Program.StreamingReadySegments

private def uartProfile : Pinwheel.Program.StreamingUART.Profile := ⟨8, 0⟩

private def manifests : Except String Json := do
  let can ← exportJson can Pinwheel.Program.StreamingCANCore.idlePins []
  let ps2 ← exportJson ps2 Pinwheel.Program.StreamingPS2Core.idlePins []
  let uart ← (uart uartProfile).bind (fun image => exportJson image {} [])
  pure (Json.mkObj [("can", can), ("ps2", ps2), ("uart-rx", uart)])

private def exitFields (image : Json) : Except String (List (String × Nat × Nat × Option Nat × Nat)) := do
  let exits ← (image.getObjVal? "exits").bind Json.getArr?
  exits.toList.mapM fun entry => do
    let kind ← entry.getObjValAs? String "kind"
    let tx ← entry.getObjValAs? Nat "tx"
    let rx ← entry.getObjValAs? Nat "rx"
    let clocks ← entry.getObjValAs? (Option Nat) "core_clocks"
    let external ← entry.getObjValAs? Nat "external_polls"
    pure (kind, tx, rx, clocks, external)

private def receiveFields (name : String) :
    Except String (Nat × List Nat × List (String × Nat × Nat × Option Nat × Nat)) := do
  let image ← (← manifests).getObjVal? name
  let start ← image.getObjValAs? Nat "start_count"
  let words ← image.getObjValAs? (List Nat) "words"
  pure (start, words, ← exitFields image)

example : ((receiveFields "can").toOption ==
    some (0, [1125899906842628, 517, 34359773281, 2], [("complete", 0, 64, none, 1)])) = true := by
  decide +kernel

example : ((receiveFields "ps2").toOption ==
    some (0, [93, 4612811961284345857, 2], [("complete", 0, 11, none, 11)])) = true := by
  decide +kernel

example : ((receiveFields "uart-rx").toOption == some (0, [5629499534213124, 1125899906842628, 18504,
    19140298416324612, 18504, 69, 34359785649, 18504, 23643898043695108, 2],
    [("complete", 0, 8, none, 2)])) = true := by
  decide +kernel

example : ((((compile [.cell .halt] 0).bind (fun image => exportJson image {} [])).bind exitFields).toOption ==
    some [("complete", 0, 0, some 1, 0)]) = true := by
  decide +kernel

example : (exportJson can {} [true]).toOption.isNone = true := by decide +kernel

example : (exportJson registerReadImage {} []).toOption.isNone = true := by decide +kernel

def main : IO Unit := do
  let result ← IO.ofExcept manifests
  IO.println result.compress
