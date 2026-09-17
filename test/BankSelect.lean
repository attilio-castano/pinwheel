import Pinwheel.Hardware.Storage.BankSelect
import Pinwheel.Hardware.Storage.CacheEnable
import Pinwheel.Hardware.Storage.BackendEmit
import Pinwheel.Hardware.Storage.DenseEmit

open Pinwheel.Hardware Pinwheel.Hardware.Loader Pinwheel.Hardware.Storage
open Backend

/-- Reproduce emission order solely to label untrusted read-back hints. -/
private def cutLabels (lateBank : Bool) : Except String (Array (String × String)) := do
  let (labels, _) ← (do
    let rn := fun {w} (r : Backend.Register w) => "%r_" ++ Backend.registerLabel r
    let hn := fun {w} (i : Machine.Input w) => "%" ++ Machine.inputLabel i
    let successor ← Emit.expression hn rn (BankSelect.successor lateBank)
    let extended := fun {w} (i : Backend.SuccessorInput w) =>
      match i with | .input p => hn p | .wire => successor
    let pc ← Emit.expression extended rn BankSelect.nextPC
    let target ← Emit.expression hn rn BankSelect.target
    let selected ← Emit.expression hn rn BankSelect.selected
    let mut labels := #[("address", target), ("selection", selected)]
    if lateBank then
      for b in #[false, true] do
        let index ← Emit.expression hn rn (BankSelect.bankIndex b BankSelect.target)
        let word ← Emit.expression hn rn (BankSelect.bankWord b (BankSelect.bankIndex b BankSelect.target))
        labels := labels ++ #[(s!"index{if b then 1 else 0}", index), (s!"word{if b then 1 else 0}", word)]
    else
      let index ← Emit.expression hn rn (Backend.Readback.indexRead.bind
        (fun p => match p with | .selected => BankSelect.selected | .target => BankSelect.target)
        (fun r => .reg r))
      labels := labels.push ("indexValue", index)
    return labels ++ #[("successorValue", successor), ("pcValue", pc)] : Emit.M _).run {}
  return labels

def main (args : List String) : IO Unit := do
  let out := args.headD "build/bank-select"
  let variant := args[1]?.getD "command-split"
  unless variant == "command-split" || variant == "late-bank" || variant == "enable-split" do
    throw (IO.userError "Expected command-split, late-bank or enable-split")
  let lateBank := variant == "late-bank"
  IO.FS.createDirAll out
  let selected := if variant == "enable-split" then CacheEnable.netlist else BankSelect.netlist lateBank
  let generated := Netlist.moduleText "pinwheel_atomic_small_dense_cached" selected
    Machine.inputs Backend.registers Machine.outputs Machine.inputLabel Backend.registerLabel Machine.outputLabel
  for (name, value) in #[("composed.mlir", generated),
      ("baseline.mlir", Machine.DenseEmit.moduleText true true none true)] do
    match value with
    | .ok text => IO.FS.writeFile (out ++ "/" ++ name) text
    | .error e => throw (IO.userError e)
  match cutLabels lateBank with
  | .ok labels =>
    IO.FS.writeFile (out ++ "/cuts.tsv")
      (String.intercalate "\n" (labels.toList.map fun (role, label) => role ++ "\t" ++ label) ++ "\n")
  | .error e => throw (IO.userError e)
  IO.println s!"Emitted proved bank-selection variant: {variant}"
