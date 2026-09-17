import Pinwheel.Hardware.Storage.BackendEmit
import Pinwheel.Hardware.Storage.DenseEmit
import Pinwheel.Hardware.Storage.BackendReadback

/-- Untrusted proof hints for shared values and read stages. Read-back must check their
semantics against the corresponding Lean expressions before using them. -/
private def cutLabels : Except String (Array String) := do
  let (labels, _) ← (do
    let rn := fun {w} (r : Pinwheel.Hardware.Storage.Backend.Register w) =>
      "%r_" ++ Pinwheel.Hardware.Storage.Backend.registerLabel r
    let hn := fun {w} (i : Pinwheel.Hardware.Loader.Machine.Input w) =>
      "%" ++ Pinwheel.Hardware.Loader.Machine.inputLabel i
    let successor ← Pinwheel.Hardware.Emit.expression hn rn Pinwheel.Hardware.Storage.Backend.successor
    let extended := fun {w} (i : Pinwheel.Hardware.Storage.Backend.SuccessorInput w) =>
      match i with | .input p => hn p | .wire => successor
    let pc ← Pinwheel.Hardware.Emit.expression extended rn Pinwheel.Hardware.Storage.Backend.nextPC
    let target ← Pinwheel.Hardware.Emit.expression hn rn
      (Pinwheel.Hardware.Storage.Backend.lift Pinwheel.Hardware.Storage.Cache.target)
    let selected ← Pinwheel.Hardware.Emit.expression hn rn
      (Pinwheel.Hardware.Storage.Backend.lift
        (Pinwheel.Hardware.Storage.Cache.liftExpr Pinwheel.Hardware.Loader.Machine.selectedGate))
    let index ← Pinwheel.Hardware.Emit.expression hn rn
      Pinwheel.Hardware.Storage.Backend.Readback.indexAddress
    return #[successor, pc, target, selected, index] : Pinwheel.Hardware.Emit.M _).run {}
  return labels

def main (args : List String) : IO Unit := do
  let out := args.headD "build/backend"
  IO.FS.createDirAll out
  let registers := Pinwheel.Hardware.Storage.Backend.registers
  unless registers.size == 607 && (registers.foldl (fun n p => n + p.1) 0) == 6233 do
    throw (IO.userError "Changed backend register layout")
  let labels := registers.map fun p => Pinwheel.Hardware.Storage.Backend.registerLabel p.2
  unless labels.toList.eraseDups.length == labels.size do
    throw (IO.userError "Aliased backend register labels")
  match Pinwheel.Hardware.Storage.Backend.moduleText with
  | .ok text => IO.FS.writeFile (out ++ "/composed.mlir") text
  | .error e => throw (IO.userError e)
  match cutLabels with
  | .ok labels =>
    IO.FS.writeFile (out ++ "/cuts.txt") (String.intercalate "\n" labels.toList ++ "\n")
  | .error e => throw (IO.userError e)
  match Pinwheel.Hardware.Loader.Machine.DenseEmit.moduleText true true with
  | .ok text => IO.FS.writeFile (out ++ "/baseline.mlir") text
  | .error e => throw (IO.userError e)
  IO.println "Emitted the proved 32-entry dense cached circuit."
