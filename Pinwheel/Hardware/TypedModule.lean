import Pinwheel.Hardware.Emit
import Pinwheel.Hardware.Interface
import Lean.Data.Json

namespace Pinwheel.Hardware

open Lean

/-- A flat synchronous circuit and the complete interface used for export and readback. -/
structure TypedModule (I R O : Nat → Type) where
  name : String
  circuit : Circuit I R O
  inputs : Interface I
  registers : Interface R
  outputs : Interface O

namespace TypedModule

abbrev Input (_ : TypedModule I R O) := I
abbrev Register (_ : TypedModule I R O) := R
abbrev Output (_ : TypedModule I R O) := O

structure Export where
  mlir : String
  descriptor : Json

private def identifiers (d : Interface P) (name : String → String := id) :
    Array (String × Nat) :=
  d.ports.map fun ⟨width, p⟩ => (name (d.label p), width)

private def asciiLetter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

private def identifier (name : String) : Bool :=
  match name.toList with
  | [] => false
  | head :: rest =>
    (asciiLetter head || head == '_') && rest.all (fun c => asciiLetter c || c == '_' || c.isDigit)

private def reservedNode (name : String) : Bool :=
  match name.toList with
  | head :: digit :: rest => (head == 'n' || head == 'v') && digit.isDigit && rest.all Char.isDigit
  | _ => false

private def portsJson (ports : Array (String × Nat)) (registers : Bool := false) : Json :=
  toJson (ports.mapIdx fun index (name, width) =>
    Json.mkObj ([("index", toJson index), ("width", toJson width), ("name", toJson name)] ++
      (if registers then [("reference", toJson name)] else [])))

/-- Emit RTL source and its readback descriptor together. The current readback
flow uses a single clock, positive widths and simple identifiers. -/
def emit (m : TypedModule I R O) : Except String Export := do
  let inputs := identifiers m.inputs
  let registers := identifiers m.registers Emit.registerSymbol
  let outputs := identifiers m.outputs
  unless identifier m.name do throw s!"Invalid module name: {m.name}"
  if registers.isEmpty then throw "Synchronous module export requires at least one register"
  for (name, width) in inputs ++ registers ++ outputs do
    unless identifier name do throw s!"Invalid signal name: {name}"
    if width == 0 then throw s!"Zero-width signal: {name}"
  let names := "clk" :: (inputs ++ registers ++ outputs).toList.map Prod.fst
  if names.length != names.eraseDups.length then
    throw "Signal names must be distinct across inputs, outputs, registers, and clk"
  for (name, _) in inputs ++ registers do
    if name == "clock" || reservedNode name then throw s!"Reserved signal name: {name}"
  let mlir ← Emit.moduleText m.name m.circuit m.inputs.ports m.registers.ports m.outputs.ports
    m.inputs.label m.registers.label m.outputs.label
  return ⟨mlir, Json.mkObj [("module", toJson m.name), ("clock", toJson "clk"),
    ("inputs", portsJson inputs), ("registers", portsJson registers true),
    ("outputs", portsJson outputs)]⟩

end TypedModule
end Pinwheel.Hardware
