import Pinwheel.Hardware.Storage.Emit

def main : IO Unit := do
  IO.FS.createDirAll "build/storage"
  match Pinwheel.Hardware.Storage.moduleText with
  | .ok text => IO.FS.writeFile "build/storage/small.mlir" text
  | .error e => throw (IO.userError e)
