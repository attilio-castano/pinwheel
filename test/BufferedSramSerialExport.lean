import Pinwheel.Hardware.Buffered.Serial
import Lean

open Pinwheel.Hardware Pinwheel.Hardware.Buffered
open Serial

private def portJson (ps : Array (Sigma P)) (label : {w : Nat} → P w → String) : Lean.Json :=
  Lean.toJson (ps.map fun ⟨w,p⟩ => Lean.Json.mkObj
    [("name",Lean.toJson (label p)),("width",Lean.toJson w)])
private def getNat (j : Lean.Json) (key : String) : Nat :=
  ((j.getObjVal? key).bind Lean.Json.getNat?).toOption.getD 0
private def inputValues (v : Lean.Json) : {w : Nat} → Input w → BitVec w := fun {w} p =>
  let pins := (v.getObjVal? "pins").toOption.getD (Lean.Json.mkObj [])
  let status := (v.getObjVal? "status").toOption.getD (Lean.Json.mkObj [])
  BitVec.ofNat w (match p with
    | .status o => getNat status (Reactive.outputLabel o)
    | p => getNat pins (inputLabel p))
private def outputJson (i : Values Input) (s : Values Register) : Lean.Json :=
  Lean.Json.mkObj (outputs.toList.map fun ⟨_,o⟩ =>
    (outputLabel o,Lean.toJson ((circuit.observe i s o).toNat)))
private def registerJson (s : Values Register) : Lean.Json :=
  Lean.Json.mkObj (registers.toList.map fun ⟨_,r⟩ =>
    ("r_" ++ registerLabel r,Lean.toJson ((s r).toNat)))
private def values (a : Array Nat) : Values Register := fun {w} r =>
  BitVec.ofNat w (a[registerIndex r]?.getD 0)
private def snapshot (s : Values Register) : Array Nat :=
  registers.map fun ⟨_,r⟩ => (s r).toNat

private def exportCase (c : Lean.Json) : IO Lean.Json := do
  let name ← IO.ofExcept ((c.getObjVal? "name").bind Lean.Json.getStr?)
  let vectors ← IO.ofExcept ((c.getObjVal? "vectors").bind Lean.Json.getArr?)
  let mut bank : Array Nat := registers.map fun _ => 0
  let mut result : Array Lean.Json := #[]
  for v in vectors do
    let i : Values Input := inputValues v
    let s : Values Register := values bank
    let after := snapshot (circuit.step i s)
    result := result.push (Lean.Json.mkObj
      [("pins",(v.getObjVal? "pins").toOption.getD (Lean.Json.mkObj [])),
       ("status",(v.getObjVal? "status").toOption.getD (Lean.Json.mkObj [])),
       ("pre_outputs",outputJson i s),
       ("post_outputs",outputJson i (values after)),
       ("pre_registers",registerJson s),
       ("post_registers",registerJson (values after))])
    bank := after
  return Lean.Json.mkObj [("name",Lean.toJson name),("vectors",Lean.toJson result)]

def main (args : List String) : IO Unit := do
  let input := args.headD "build/buffered-sram-serial/input.json"
  let out := args[1]?.getD "build/buffered-sram-serial/frontend"
  IO.FS.createDirAll out
  let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile input))
  let schema ← IO.ofExcept ((j.getObjVal? "schema").bind Lean.Json.getStr?)
  unless schema == "pinwheel-buffered-sram-serial-input-v1" do
    throw (IO.userError "Wrong buffered SRAM serial input schema")
  let cases ← IO.ofExcept ((j.getObjVal? "cases").bind Lean.Json.getArr?)
  let exported ← cases.mapM exportCase
  IO.FS.writeFile (out ++ "/frontend.mlir") (← IO.ofExcept moduleText)
  let rs := Lean.toJson (registers.map fun ⟨w,r⟩ => Lean.Json.mkObj
    [("name",Lean.toJson ("r_" ++ registerLabel r)),
     ("reference",Lean.toJson ("r_" ++ registerLabel r)),("width",Lean.toJson w)])
  let assembly := Lean.Json.mkObj [("schema",Lean.toJson (1 : Nat)),
    ("module",Lean.toJson "pinwheel_buffered_sram_serial_frontend"),
    ("inputs",portJson inputs inputLabel),("outputs",portJson outputs outputLabel),
    ("registers",rs)]
  IO.FS.writeFile (out ++ "/assembly.json") (assembly.pretty ++ "\n")
  let vectors := Lean.Json.mkObj
    [("schema",Lean.toJson "pinwheel-buffered-sram-serial-vectors-v1"),
     ("cases",Lean.toJson exported)]
  IO.FS.writeFile (out ++ "/vectors.json") (vectors.pretty ++ "\n")
  IO.println s!"Buffered SRAM serial frontend: {cases.size} cases; {registers.size} registers."
