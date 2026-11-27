import Lean.Data.Json

/-! The JSON shape of a read-back import descriptor, shared by the emitters in
`test/StreamingReadyReadbackDescriptor.lean` and `test/BufferedReadbackDescriptor.lean`.

A descriptor tells the RTL importer everything it needs about one emitted
module: its name, the Lean types and circuit it refines, and for every input,
register and output the RTL name, width and Lean constructor term.

Constructor terms are printed by derived `Repr` instances and shortened to dot
notation, e.g. `.word 3#6` or `.port (.address false)`. An emitter opens this
namespace before deriving them, so `BitVec` indices print in decimal; the
instance is scoped and changes nothing elsewhere.
-/

namespace Pinwheel.Hardware.Readback.Descriptor
open Lean

scoped instance (priority := high) decimalBitVec {n : Nat} : Repr (BitVec n) :=
  ⟨fun v _ => s!"{v.toNat}#{n}"⟩

/-- Shorten one space-separated token: a qualified constructor keeps only its
last component, and parentheses around that one token alone are dropped. -/
def dotToken (token : String) : String :=
  let chars := token.toList
  let opens := chars.takeWhile (· == '(')
  let rest := chars.drop opens.length
  let closes := rest.reverse.takeWhile (· == ')')
  let core := rest.take (rest.length - closes.length)
  let bare := String.ofList core
  let short := if core.contains '.' && !core.contains '#' then "." ++ ((bare.splitOn ".").getLast?.getD bare) else bare
  let paired := min opens.length closes.length
  String.ofList (opens.drop paired) ++ short ++ String.ofList (closes.drop paired)

/-- `Pinwheel.….Register.word 3#6` becomes `.word 3#6`; a nested constructor
`(Pinwheel.….Output.valid)` becomes `.valid`, and one with arguments keeps its
parentheses: `.port (.address false)`. -/
def dotTerm (text : String) : String :=
  " ".intercalate <| (text.splitOn " ").map dotToken

def port {P : Nat → Type} [∀ w, Repr (P w)] (name : String) (w : Nat) (p : P w) : Json :=
  Json.mkObj [("name", toJson name), ("width", toJson w), ("term", toJson (dotTerm (reprStr p)))]

def descriptor (module inputType registerType outputType circuit : String)
    (inputs registers outputs : Array Json) : Json :=
  Json.mkObj [("schema", toJson "pinwheel.readback-descriptor.v1"), ("module", toJson module),
    ("input_type", toJson inputType), ("register_type", toJson registerType),
    ("output_type", toJson outputType), ("circuit", toJson circuit),
    ("inputs", Json.arr inputs), ("registers", Json.arr registers), ("outputs", Json.arr outputs)]

/-- Write each named descriptor to `out/<name>.json`. -/
def write (out : String) (files : List (String × Json)) : IO Unit := do
  IO.FS.createDirAll out
  for (name, json) in files do
    IO.FS.writeFile s!"{out}/{name}.json" (json.pretty ++ "\n")
  IO.println s!"wrote {", ".intercalate (files.map (·.1))} descriptors to {out}"

end Pinwheel.Hardware.Readback.Descriptor
