import Pinwheel.Hardware.Storage.ChipBackend

open Pinwheel.Hardware Pinwheel.Hardware.Storage.Backend

/-- Emit the whole chip — Tiny Tapeout pins, samplers, serial loader, core — around
the one-port and the two-port backends. -/
def main (args : List String) : IO Unit := do
  let out := args.headD "build/chip"
  IO.FS.createDirAll out
  let onePort := Policy.chipRegisters OnePort.extra
  let twoPort := Policy.chipRegisters TwoPort.extra
  -- core registers, 76 receiver bits, 12 sampler bits
  unless onePort.size == 611 + 5 + 10 && (onePort.foldl (fun n p => n + p.1) 0) == 6426 + 76 + 12 do
    throw (IO.userError "Changed one-port chip register layout")
  unless twoPort.size == 610 + 5 + 10 && (twoPort.foldl (fun n p => n + p.1) 0) == 6425 + 76 + 12 do
    throw (IO.userError "Changed two-port chip register layout")
  for (registers, label) in [(onePort.map fun p => Policy.chipRegisterLabel OnePort.label p.2, "one-port"),
      (twoPort.map fun p => Policy.chipRegisterLabel TwoPort.label p.2, "two-port")] do
    unless registers.toList.eraseDups.length == registers.size do
      throw (IO.userError s!"Aliased {label} chip register labels")
  match OnePort.chipText with
  | .ok text => IO.FS.writeFile (out ++ "/chip-oneport.mlir") text
  | .error e => throw (IO.userError e)
  match TwoPort.chipText with
  | .ok text => IO.FS.writeFile (out ++ "/chip-twoport.mlir") text
  | .error e => throw (IO.userError e)
  IO.println "Emitted the whole chip around the one-port and two-port backends."
