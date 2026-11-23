import Lean.Data.Json
import Pinwheel.Hardware.Processor.Examples.ReadySPI
import Pinwheel.Hardware.Processor.LoadableSystemExport
import Pinwheel.Hardware.Processor.ReadyHost

open Lean Pinwheel.Hardware.Processor

def main (args : List String) : IO Unit := do
  let [out, table, collect] := args | throw (IO.userError "expected output, request table, collect frame")
  let bytes ← IO.FS.readBinFile table
  let some index := collect.toNat? | throw (IO.userError "invalid collection index")
  let frames := bytes.size / 44
  unless frames > index && bytes.size == 44 * frames && bytes.size ≤ 768 &&
      bytes.data.all (· < 16) do throw (IO.userError "invalid request nibble table")
  let image := ReadySPI.rom (bytes.data.map UInt8.toBitVec) frames index
  let _ ← LoadableSystemExport.exportHierarchy ReadySPI.layout image (by decide) (by decide)
    out "processor_loadable_system"
