import Pinwheel.Hardware.StreamingReady.CoreEmit
import Pinwheel.Hardware.Streaming.FrontendEmit
import Lean

/-! Write read-back import descriptors for the Streaming and sampled-ready cores
and the shared frontend.

A descriptor tells the RTL importer everything it needs about one emitted
module: its name, the Lean types and circuit it refines, and for every input,
register and output the RTL name, width and Lean constructor term. All of it
comes from the same enumerations and labels the emitter uses, so the importer
no longer keeps hand-typed copies.

Constructor terms are printed by derived `Repr` instances (with decimal
`BitVec` indices) and shortened to dot notation, e.g. `.word 3#6`.

The importer reads checked-in copies from `scripts/readback_descriptors`;
`test/test_readback_descriptor.py` fails if they differ from a fresh run.
Regenerate them with

    lake env lean -DwarningAsError=true --run test/StreamingReadyReadbackDescriptor.lean scripts/readback_descriptors
-/

open Lean Pinwheel.Hardware

namespace ReadbackTerms
instance (priority := high) decimalBitVec {n : Nat} : Repr (BitVec n) := ⟨fun v _ => s!"{v.toNat}#{n}"⟩
deriving instance Repr for Pinwheel.Hardware.Streaming.Core.Input
deriving instance Repr for Pinwheel.Hardware.Streaming.Core.Output
deriving instance Repr for Pinwheel.Hardware.Streaming.Core.Register
deriving instance Repr for Pinwheel.Hardware.Streaming.Frontend.Input
deriving instance Repr for Pinwheel.Hardware.Streaming.Frontend.Output
deriving instance Repr for Pinwheel.Hardware.Streaming.Frontend.Register
end ReadbackTerms
open ReadbackTerms

/-- `Pinwheel.….Register.word 3#6` becomes `.word 3#6`; a parenthesized nested
constructor `(Pinwheel.….Output.valid)` becomes `.valid`. -/
def dotTerm (text : String) : String :=
  " ".intercalate <| (text.splitOn " ").map fun token =>
    let chars := ((token.toList.dropWhile (· == '(')).reverse.dropWhile (· == ')')).reverse
    let bare := String.ofList chars
    if chars.contains '.' && !chars.contains '#' then
      "." ++ ((bare.splitOn ".").getLast?.getD bare)
    else bare

def port {P : Nat → Type} [∀ w, Repr (P w)] (name : String) (w : Nat) (p : P w) : Json :=
  Json.mkObj [("name", toJson name), ("width", toJson w), ("term", toJson (dotTerm (reprStr p)))]

def descriptor (module inputType registerType outputType circuit : String)
    (inputs registers outputs : Array Json) : Json :=
  Json.mkObj [("schema", toJson "pinwheel.readback-descriptor.v1"), ("module", toJson module),
    ("input_type", toJson inputType), ("register_type", toJson registerType),
    ("output_type", toJson outputType), ("circuit", toJson circuit),
    ("inputs", Json.arr inputs), ("registers", Json.arr registers), ("outputs", Json.arr outputs)]

/-- The Streaming and sampled-ready cores share their ports and registers; only
the module and the circuit differ. -/
def coreDescriptor (module : String) (circuit : Lean.Name) (a : Nat) : Json :=
  descriptor module (toString ``Pinwheel.Hardware.Streaming.Core.Input)
    s!"({``Pinwheel.Hardware.Streaming.Core.Register} {a})" (toString ``Pinwheel.Hardware.Streaming.Core.Output)
    s!"({circuit} {a})"
    (StreamingReady.Core.inputs.map fun ⟨w, p⟩ => port (StreamingReady.Core.inputLabel p) w p)
    ((StreamingReady.Core.registers a).map fun ⟨w, r⟩ => port ("r_" ++ StreamingReady.Core.registerLabel r) w r)
    (StreamingReady.Core.outputs.map fun ⟨w, o⟩ => port (StreamingReady.Core.outputLabel o) w o)

def frontendDescriptor : Json :=
  descriptor Streaming.Frontend.moduleName (toString ``Pinwheel.Hardware.Streaming.Frontend.Input)
    (toString ``Pinwheel.Hardware.Streaming.Frontend.Register) (toString ``Pinwheel.Hardware.Streaming.Frontend.Output)
    (toString ``Pinwheel.Hardware.Streaming.Frontend.circuit)
    (Streaming.Frontend.inputs.map fun ⟨w, p⟩ => port (Streaming.Frontend.inputLabel p) w p)
    (Streaming.Frontend.registers.map fun ⟨w, r⟩ => port ("r_" ++ Streaming.Frontend.registerLabel r) w r)
    (Streaming.Frontend.outputs.map fun ⟨w, o⟩ => port (Streaming.Frontend.outputLabel o) w o)

def main (args : List String) : IO Unit := do
  let out := args.headD "build/readback-descriptors"
  IO.FS.createDirAll out
  let streaming a := coreDescriptor (Streaming.Core.moduleName a) ``Pinwheel.Hardware.Streaming.Core.circuit a
  let ready a := coreDescriptor (StreamingReady.Core.moduleName a) ``Pinwheel.Hardware.StreamingReady.Core.circuit a
  let files := [("streaming-core-d2", streaming 1), ("streaming-core-d4", streaming 2),
    ("ready-core-d2", ready 1), ("ready-core-d4", ready 2), ("frontend", frontendDescriptor)]
  for (name, json) in files do
    IO.FS.writeFile s!"{out}/{name}.json" (json.pretty ++ "\n")
  IO.println s!"wrote {", ".intercalate (files.map (·.1))} descriptors to {out}"
