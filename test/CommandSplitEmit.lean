import Pinwheel.Hardware.Storage.DenseEmit

def main : IO Unit := do
  let directory := "build/successor-fetch/command-split"
  IO.FS.createDirAll directory
  match Pinwheel.Hardware.Loader.Machine.DenseEmit.moduleText true true none true with
  | .ok text => IO.FS.writeFile s!"{directory}/candidate.mlir" text
  | .error e => throw (IO.userError e)
