import Pinwheel.Hardware.Storage.TwoPortEmit

open Pinwheel.Hardware Pinwheel.Hardware.Storage.Backend

/-- Emit the two-port backend twice: as it is, and behind the pin pipeline. -/
def main (args : List String) : IO Unit := do
  let out := args.headD "build/twoport"
  IO.FS.createDirAll out
  unless TwoPort.registers.size == 610 && (TwoPort.registers.foldl (fun n p => n + p.1) 0) == 6425 do
    throw (IO.userError "Changed two-port register layout")
  let labels := TwoPort.registers.map fun p => TwoPort.registerLabel p.2
  unless labels.toList.eraseDups.length == labels.size do
    throw (IO.userError "Aliased two-port register labels")
  match TwoPort.moduleText with
  | .ok text => IO.FS.writeFile (out ++ "/twoport.mlir") text
  | .error e => throw (IO.userError e)
  match TwoPort.sampledText with
  | .ok text => IO.FS.writeFile (out ++ "/twoport-sampled.mlir") text
  | .error e => throw (IO.userError e)
  IO.println "Emitted the two-port backend with and without the two-register pin pipeline."
