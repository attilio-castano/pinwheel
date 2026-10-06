import Pinwheel.Hardware.Buffered.Reactive
import Lean

open Pinwheel.Hardware Pinwheel.Hardware.Buffered.Reactive

private def portJson (ps : Array (Sigma P)) (label : {w : Nat} → P w → String) : Lean.Json :=
  Lean.toJson (ps.map fun ⟨w,p⟩ => Lean.Json.mkObj
    [("name",Lean.toJson (label p)),("width",Lean.toJson w)])

private def commandValues (j : Lean.Json) (raw : Nat) : Values Input := fun {w} p =>
  let n := if inputLabel p == "raw_inputs" then raw
    else ((j.getObjVal? (inputLabel p)).bind Lean.Json.getNat?).toOption.getD 0
  BitVec.ofNat w n

private def stateJson (i : Values Input) (before after : Values Register) : Lean.Json :=
  Lean.Json.mkObj (outputs.toList.map fun ⟨_,o⟩ =>
    (outputLabel o, Lean.toJson
      (if outputLabel o == "rejected" then (circuit.observe i before o).toNat
       else (circuit.observe i after o).toNat)))

private def get (j : Lean.Json) (key : String) : IO Lean.Json :=
  match j.getObjVal? key with
  | .ok v => pure v
  | .error e => throw (IO.userError e)

private def array (j : Lean.Json) : IO (Array Lean.Json) :=
  match j.getArr? with
  | .ok v => pure v
  | .error e => throw (IO.userError e)

private def string (j : Lean.Json) : IO String :=
  match j.getStr? with
  | .ok v => pure v
  | .error e => throw (IO.userError e)

private def exportCase (c : Lean.Json) : IO Lean.Json := do
  let name ← string (← get c "name")
  let vectors ← array (← get c "vectors")
  let mut s : Values Register := fun _ => 0
  let mut result : Array Lean.Json := #[]
  for v in vectors do
    let command := (v.getObjVal? "command").toOption.getD (Lean.Json.mkObj [])
    let raw := ((v.getObjVal? "raw_inputs").bind Lean.Json.getNat?).toOption.getD 0
    let i : Values Input := commandValues command raw
    let next : Values Register := circuit.step i s
    -- Materialize every register once; the next edge must not retain a thunk
    -- that recursively reevaluates the complete preceding history.
    let bank : Array Nat := registers.map fun ⟨_,r⟩ => (next r).toNat
    let after : Values Register := fun {w} r => BitVec.ofNat w (bank[registerIndex r]?.getD 0)
    result := result.push (Lean.Json.mkObj
      [("command",command),("raw_inputs",Lean.toJson raw),("state",stateJson i s after)])
    s := after
  return Lean.Json.mkObj [("name",Lean.toJson name),("vectors",Lean.toJson result)]

def main (args : List String) : IO Unit := do
  let input := args.headD "build/buffered-hardware/input.json"
  let out := args[1]?.getD "build/buffered-hardware/linear"
  IO.FS.createDirAll out
  let j ← match Lean.Json.parse (← IO.FS.readFile input) with
    | .ok j => pure j
    | .error e => throw (IO.userError e)
  let schema ← string (← get j "schema")
  unless schema == "pinwheel-buffered-reactive-hardware-input-v1" do
    throw (IO.userError "Wrong hardware input schema")
  let cases ← array (← get j "cases")
  let exported ← cases.mapM exportCase
  let text ← match moduleText with
    | .ok s => pure s
    | .error e => throw (IO.userError e)
  IO.FS.writeFile (out ++ "/core.mlir") text
  let rs := Lean.toJson (registers.map fun ⟨w,r⟩ => Lean.Json.mkObj
    [("name",Lean.toJson ("r_" ++ registerLabel r)),("reference",Lean.toJson ("r_" ++ registerLabel r)),
     ("width",Lean.toJson w)])
  let assembly := Lean.Json.mkObj [("schema",Lean.toJson (1 : Nat)),
    ("module",Lean.toJson "pinwheel_buffered_reactive"),("inputs",portJson inputs inputLabel),
    ("outputs",portJson outputs outputLabel),("registers",rs)]
  IO.FS.writeFile (out ++ "/assembly.json") (assembly.pretty ++ "\n")
  let vectors := Lean.Json.mkObj [("schema",Lean.toJson "pinwheel-buffered-reactive-hardware-vectors-v1"),
    ("cases",Lean.toJson exported)]
  IO.FS.writeFile (out ++ "/vectors.json") (vectors.pretty ++ "\n")
  IO.println s!"Buffered reactive circuit: {cases.size} cases; {registers.size} registers."
