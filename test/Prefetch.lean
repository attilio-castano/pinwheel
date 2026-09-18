import Pinwheel.Hardware.Storage.PrefetchEmit

open Pinwheel.Hardware Pinwheel.Hardware.Storage.Backend

/-- Emit the prefetch backend twice: as it is, and behind the pin pipeline. -/
def main (args : List String) : IO Unit := do
  let out := args.headD "build/prefetch"
  IO.FS.createDirAll out
  unless Prefetch.registers.size == 610 && (Prefetch.registers.foldl (fun n p => n + p.1) 0) == 6425 do
    throw (IO.userError "Changed prefetch register layout")
  let labels := Prefetch.registers.map fun p => Prefetch.registerLabel p.2
  unless labels.toList.eraseDups.length == labels.size do
    throw (IO.userError "Aliased prefetch register labels")
  match Prefetch.moduleText with
  | .ok text => IO.FS.writeFile (out ++ "/prefetch.mlir") text
  | .error e => throw (IO.userError e)
  match Prefetch.sampledText with
  | .ok text => IO.FS.writeFile (out ++ "/prefetch-sampled.mlir") text
  | .error e => throw (IO.userError e)
  IO.println "Emitted the prefetch backend with and without the two-register pin pipeline."
