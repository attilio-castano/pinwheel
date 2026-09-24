import Pinwheel.Hardware.Storage.UploadPipeline

open Pinwheel.Hardware.Storage

def main (args : List String) : IO Unit := do
  let out := args.headD "build/storage/upload-pipeline"
  IO.FS.createDirAll out
  unless UploadPipeline.registers.foldl (fun n p => n + p.1) 0 == 71 do
    throw (IO.userError "Unexpected upload stage register cost")
  for (kind, result) in [("core", UploadPipeline.coreText), ("chip", UploadPipeline.chipText)] do
    match result with
    | .ok text => IO.FS.writeFile (out ++ s!"/{kind}.mlir") text
    | .error e => throw (IO.userError e)
  IO.println "Emitted experimental upload pipeline: 71 added register bits"
