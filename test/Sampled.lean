import Pinwheel.Hardware.Storage.SampledBackend

open Pinwheel.Hardware Pinwheel.Hardware.Loader Pinwheel.Hardware.Storage
open Backend

private def texts (n : Netlist Backend.Register Machine.Output Machine.Input) :
    Except String (String × String) := do
  let inner ← Netlist.moduleText "pinwheel_atomic_small_dense_cached" n
    Machine.inputs Backend.registers Machine.outputs Machine.inputLabel Backend.registerLabel Machine.outputLabel
  return (inner, ← Sampled.moduleText n)

/-- Netlists live in a higher universe than IO values, so select the text. -/
private def emitted (variant : String) : Except String (String × String) :=
  match variant with
  | "composed" => texts Backend.netlist
  | "command-split" => texts (BankSelect.netlist false)
  | "late-bank" => texts (BankSelect.netlist true)
  | "enable-split" => texts CacheEnable.netlist
  | _ => .error "Expected composed, command-split, late-bank or enable-split"

/-- Emit one proved backend twice: as it is, and behind the pin pipeline.
The first file lets a checker rebuild the pipeline around the inner RTL. -/
def main (args : List String) : IO Unit := do
  let out := args.headD "build/sampled"
  let variant := args[1]?.getD "command-split"
  IO.FS.createDirAll out
  unless Sampled.registers.size == 609 && (Sampled.registers.foldl (fun n p => n + p.1) 0) == 6237 do
    throw (IO.userError "Changed sampled register layout")
  let labels := Sampled.registers.map fun p => Sampled.registerLabel p.2
  unless labels.toList.eraseDups.length == labels.size do
    throw (IO.userError "Aliased sampled register labels")
  match emitted variant with
  | .ok (inner, sampled) =>
    IO.FS.writeFile (out ++ "/inner.mlir") inner
    IO.FS.writeFile (out ++ "/sampled.mlir") sampled
  | .error e => throw (IO.userError e)
  IO.println s!"Emitted {variant} with and without the two-register pin pipeline."
