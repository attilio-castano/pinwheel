import Pinwheel.Hardware.StreamingReady.RegisteredStorePackage

open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady

private def writeModule (out : System.FilePath) (name : String) (artifact : TypedModule.Export) :
    IO Unit := do
  IO.FS.writeFile (out / (name ++ ".mlir")) artifact.mlir
  IO.FS.writeFile (out / (name ++ "-interface.json")) (artifact.descriptor.pretty ++ "\n")

def main (args : List String) : IO Unit := do
  let [destination, depth] := args
    | throw (IO.userError "expected a destination directory and buffer address width (1 or 2)")
  let some a := depth.toNat?
    | throw (IO.userError "expected buffer address width 1 or 2")
  if supported : a = 1 ∨ a = 2 then
    let out := System.FilePath.mk destination
    let core ← IO.ofExcept (RegisteredStorePackage.core a supported).emit
    let frontend ← IO.ofExcept TypedExport.frontend.emit
    IO.FS.createDirAll out
    writeModule out "core" core
    writeModule out "frontend" frontend
  else
    throw (IO.userError "expected buffer address width 1 or 2")
