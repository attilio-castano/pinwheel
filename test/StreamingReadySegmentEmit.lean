import Pinwheel.Hardware.StreamingReady.SegmentExport

open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady

private def writeModule (out : System.FilePath) (name : String) (artifact : TypedModule.Export) : IO Unit := do
  IO.FS.writeFile (out / (name ++ ".mlir")) artifact.mlir
  IO.FS.writeFile (out / (name ++ "-interface.json")) (artifact.descriptor.pretty ++ "\n")

def main (args : List String) : IO Unit := do
  let [destination, backend] := args
    | throw (IO.userError "expected a destination directory and 0 (combinational) or 1 (registered)")
  unless backend == "0" || backend == "1" do
    throw (IO.userError "expected 0 (combinational) or 1 (registered)")
  let out := System.FilePath.mk destination
  let core ← IO.ofExcept (SegmentExport.core 1 (.inl rfl) (backend == "1")).emit
  let frontend ← IO.ofExcept TypedExport.frontend.emit
  IO.FS.createDirAll out
  writeModule out "core" core
  writeModule out "frontend" frontend
