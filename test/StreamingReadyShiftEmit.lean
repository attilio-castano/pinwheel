import Pinwheel.Hardware.StreamingReady.TypedExportShift

open Pinwheel.Hardware.StreamingReady

def main (args : List String) : IO Unit := do
  let [destination] := args
    | throw (IO.userError "expected one destination directory")
  let out := System.FilePath.mk destination
  let artifact ← IO.ofExcept TypedExportShift.core.emit
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "core.mlir") artifact.mlir
  IO.FS.writeFile (out / "core-interface.json") (artifact.descriptor.pretty ++ "\n")
