import Pinwheel.Hardware.Storage.Emit
import Pinwheel.Hardware.Storage.CacheEmit

def main : IO Unit := do
  IO.FS.createDirAll "build/storage"
  match Pinwheel.Hardware.Storage.moduleText with
  | .ok text => IO.FS.writeFile "build/storage/small.mlir" text
  | .error e => throw (IO.userError e)
  match Pinwheel.Hardware.Loader.Machine.CachedEmit.moduleText with
  | .ok text => IO.FS.writeFile "build/storage/cached.mlir" text
  | .error e => throw (IO.userError e)
