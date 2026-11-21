import Pinwheel.Hardware.StreamingReady.TypedExport

open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady

private def writeModule (out : System.FilePath) (name : String) (artifact : TypedModule.Export) :
    IO Unit := do
  IO.FS.writeFile (out / (name ++ ".mlir")) artifact.mlir
  IO.FS.writeFile (out / (name ++ "-interface.json")) (artifact.descriptor.pretty ++ "\n")

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD "build/streaming-ready-typed/emitted"
  let some a := (args[1]?.getD "1").toNat?
    | throw (IO.userError "qualified buffer address width must be 1 or 2")
  if supported : a = 1 ∨ a = 2 then
    let core ← IO.ofExcept (TypedExport.core a supported).emit
    let frontend ← IO.ofExcept TypedExport.frontend.emit
    IO.FS.createDirAll out
    writeModule out "core" core
    writeModule out "frontend" frontend
  else
    throw (IO.userError "qualified buffer address width must be 1 or 2")
