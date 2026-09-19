import Pinwheel.Hardware.Storage.OnePortEmit

open Pinwheel.Hardware Pinwheel.Hardware.Storage.Backend

/-- Emit the one-port backend twice: as it is, and behind the pin pipeline. -/
def main (args : List String) : IO Unit := do
  let out := args.headD "build/oneport"
  IO.FS.createDirAll out
  unless OnePort.registers.size == 611 && (OnePort.registers.foldl (fun n p => n + p.1) 0) == 6426 do
    throw (IO.userError "Changed one-port register layout")
  let labels := OnePort.registers.map fun p => OnePort.registerLabel p.2
  unless labels.toList.eraseDups.length == labels.size do
    throw (IO.userError "Aliased one-port register labels")
  match OnePort.moduleText with
  | .ok text => IO.FS.writeFile (out ++ "/oneport.mlir") text
  | .error e => throw (IO.userError e)
  match OnePort.sampledText with
  | .ok text => IO.FS.writeFile (out ++ "/oneport-sampled.mlir") text
  | .error e => throw (IO.userError e)
  IO.println "Emitted the one-port backend with and without the two-register pin pipeline."
