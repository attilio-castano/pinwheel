import Pinwheel.Hardware.Storage.Emit
import Pinwheel.Hardware.Storage.CacheEmit
import Pinwheel.Hardware.Storage.DenseEmit

def main : IO Unit := do
  IO.FS.createDirAll "build/storage"
  match Pinwheel.Hardware.Storage.moduleText with
  | .ok text => IO.FS.writeFile "build/storage/small.mlir" text
  | .error e => throw (IO.userError e)
  match Pinwheel.Hardware.Loader.Machine.CachedEmit.moduleText with
  | .ok text => IO.FS.writeFile "build/storage/cached.mlir" text
  | .error e => throw (IO.userError e)
  for (name, small, cached) in [("dense", false, false), ("small-dense", true, false), ("small-dense-cached", true, true)] do
    match Pinwheel.Hardware.Loader.Machine.DenseEmit.moduleText small cached with
    | .ok text => IO.FS.writeFile s!"build/storage/{name}.mlir" text
    | .error e => throw (IO.userError e)
