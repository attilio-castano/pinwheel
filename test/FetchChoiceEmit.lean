import Pinwheel.Hardware.Storage.DenseEmit

def main : IO Unit := do
  for (name, variant) in [("late-index", Pinwheel.Hardware.Storage.FetchChoice.Variant.lateIndex),
      ("late-record", Pinwheel.Hardware.Storage.FetchChoice.Variant.lateRecord)] do
    let directory := s!"build/successor-fetch/{name}"
    IO.FS.createDirAll directory
    match Pinwheel.Hardware.Loader.Machine.DenseEmit.moduleText true true (some variant) with
    | .ok text => IO.FS.writeFile s!"{directory}/candidate.mlir" text
    | .error e => throw (IO.userError e)
