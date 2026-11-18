import Pinwheel.Hardware.TypedModule

namespace Pinwheel.Hardware

open Lean

namespace TypedHierarchy

/-- A source can be a top-level input, an internal net, or an already driven
top-level output that is also consumed inside the hierarchy. -/
inductive Source (I W O : Nat → Type) (b : Nat) where
  | input (port : I b)
  | net (wire : W b)
  | output (port : O b)

/-- A leaf output drives an internal net or one top-level output. -/
inductive Sink (W O : Nat → Type) (b : Nat) where
  | net (wire : W b)
  | output (port : O b)

/-- Connect typed ports and inject each leaf register into the flat state. -/
structure Instance (I R O W : Nat → Type) where
  name : String
  Input : Nat → Type
  Register : Nat → Type
  Output : Nat → Type
  design : TypedModule Input Register Output
  input : ∀ {b}, Input b → Source I W O b
  output : ∀ {b}, Output b → Sink W O b
  state : ∀ {b}, Register b → R b

def Instance.connect (name : String) (design : TypedModule LI LR LO)
    (input : ∀ {b}, LI b → Source I W O b) (output : ∀ {b}, LO b → Sink W O b)
    (state : ∀ {b}, LR b → R b) : Instance I R O W :=
  ⟨name, LI, LR, LO, design, input, output, state⟩

/-- Expose register values as pins for inter-instance wiring. -/
def stateTaps (c : Circuit I R O) : Circuit I R R := ⟨c.next, Expr.reg⟩

end TypedHierarchy

/-- A single-clock assembly with a flat structural reference circuit. Readback
checks the assembled RTL against that reference. -/
structure TypedHierarchy (I R O W : Nat → Type) where
  name : String
  flat : TypedModule I R O
  wires : Interface W
  instances : Array (TypedHierarchy.Instance I R O W)

namespace TypedHierarchy

def stateEntries (h : TypedHierarchy I R O W) : Array (Nat × String) :=
  h.instances.flatMap fun i => i.design.registers.ports.map fun ⟨_, p⟩ =>
    ((h.flat.registers.position (i.state p)).val,
      i.name ++ "." ++ Emit.registerSymbol (i.design.registers.label p))

private def orderedPaths (h : TypedHierarchy I R O W) (entries : Array (Nat × String)) :
    Array String :=
  entries.foldl (fun paths (ordinal, path) => paths.set! ordinal path)
    (Array.replicate h.flat.registers.size "")

/-- Physical path derived from the instance register injection. Emission checks
that the injections cover the complete flat state exactly once. -/
def statePath (h : TypedHierarchy I R O W) (p : R b) : String :=
  (orderedPaths h h.stateEntries)[(h.flat.registers.position p).val]!

private def netName (h : TypedHierarchy I R O W) (p : W b) : String :=
  "net_" ++ Nat.repr (h.wires.position p).val

private def sourceName (h : TypedHierarchy I R O W)
    (wireLabel : {b : Nat} → W b → String) : Source I W O b → String
  | .input p => h.flat.inputs.label p
  | .net p => wireLabel p
  | .output p => h.flat.outputs.label p

private def sinkName (h : TypedHierarchy I R O W)
    (wireLabel : {b : Nat} → W b → String) : Sink W O b → String
  | .net p => wireLabel p
  | .output p => h.flat.outputs.label p

private def vectorDeclaration (direction name : String) (width : Nat) : String :=
  s!"{direction} [{width-1}:0] {name}"

private def instanceText (h : TypedHierarchy I R O W)
    (wireLabel : {b : Nat} → W b → String) (i : Instance I R O W) : String :=
  let inputs := i.design.inputs.ports.map fun ⟨_, p⟩ =>
    s!".{i.design.inputs.label p}({h.sourceName wireLabel (i.input p)})"
  let outputs := i.design.outputs.ports.map fun ⟨_, p⟩ =>
    s!".{i.design.outputs.label p}({h.sinkName wireLabel (i.output p)})"
  s!"{i.design.name} {i.name}(" ++ String.intercalate ", " (#[ ".clk(clk)" ] ++ inputs ++ outputs).toList ++ ");"

structure Layout where
  verilog : String
  registerPaths : Array String

/-- Render the checked typed wrapper without elaborating a flat artifact. Clients
may supply existing net labels when replay or tooling already names those nets. -/
def layout (h : TypedHierarchy I R O W)
    (wireLabel : {b : Nat} → W b → String := h.netName) : Except String Layout := do
  unless TypedModule.identifier h.name && h.name != h.flat.name do
    throw "Invalid or conflicting hierarchy module name"
  let entries := h.stateEntries
  unless entries.size == h.flat.registers.size && (entries.toList.map Prod.fst).eraseDups.length == entries.size do
    throw "Instance register bindings must cover the flat state exactly once"
  let paths := orderedPaths h entries
  let nets := h.wires.ports.map fun p => wireLabel p.2
  let inputNames := h.flat.inputs.ports.map fun p => h.flat.inputs.label p.2
  let outputNames := h.flat.outputs.ports.map fun p => h.flat.outputs.label p.2
  let instanceNames := h.instances.map (·.name)
  let names := (#[ "clk" ] ++ nets ++ inputNames ++ outputNames ++ instanceNames).toList
  unless names.eraseDups.length == names.length && names.all TypedModule.identifier do
    throw "Invalid or conflicting instance or top-level net name"
  if h.wires.ports.any (fun p => p.1 == 0) then throw "Hierarchy net width must be positive"
  let drivers := h.instances.flatMap fun i =>
    i.design.outputs.ports.map fun p => h.sinkName wireLabel (i.output p.2)
  unless drivers.size == nets.size + outputNames.size &&
      (nets ++ outputNames).all (fun name => drivers.contains name) do
    throw "Each internal net and top-level output must have exactly one driver"
  let ports := #[ "input wire clk" ] ++
    h.flat.inputs.ports.map (fun p => vectorDeclaration "input wire" (h.flat.inputs.label p.2) p.1) ++
    h.flat.outputs.ports.map (fun p => vectorDeclaration "output wire" (h.flat.outputs.label p.2) p.1)
  let lines := #[s!"module {h.name}(" ++ String.intercalate ", " ports.toList ++ ");"] ++
    h.wires.ports.map (fun p => vectorDeclaration "wire" (wireLabel p.2) p.1 ++ ";") ++
    h.instances.map (h.instanceText wireLabel) ++ #["endmodule"]
  return ⟨String.intercalate "\n" lines.toList ++ "\n", paths⟩

structure Export where
  verilog : String
  flatMlir : String
  leaves : Array (String × TypedModule.Export)
  descriptor : Json

def emit (h : TypedHierarchy I R O W) : Except String Export := do
  let assembly ← h.layout
  let flat ← h.flat.emit
  let mut leaves : Array (String × TypedModule.Export) := #[]
  for i in h.instances do
    let name := i.design.name
    if name == h.name || name == h.flat.name then throw s!"Conflicting leaf module name: {name}"
    let leaf ← i.design.emit
    match leaves.find? (fun pair => pair.1 == name) with
    | some (_, previous) =>
      unless previous.mlir == leaf.mlir && previous.descriptor == leaf.descriptor do
        throw s!"Different leaf modules share a name: {name}"
    | none => leaves := leaves.push (name, leaf)
  let paths := assembly.registerPaths
  let registers := h.flat.registers.ports.mapIdx fun index p =>
    let label := Emit.registerSymbol (h.flat.registers.label p.2)
    Json.mkObj [("index", toJson index), ("name", toJson label), ("flat_reference", toJson label),
      ("width", toJson p.1), ("reference", toJson paths[index]!)]
  let registerMap := h.flat.registers.ports.mapIdx fun index p =>
    (Emit.registerSymbol (h.flat.registers.label p.2), toJson paths[index]!)
  let descriptor := flat.descriptor.mergeObj (Json.mkObj [
    ("module", toJson h.name), ("flat_module", toJson h.flat.name),
    ("registers", toJson registers), ("register_map", Json.mkObj registerMap.toList),
    ("hierarchical_registers", toJson paths), ("leaves", toJson (leaves.map Prod.fst)),
    ("leaf_interfaces", toJson (leaves.map fun (name, leaf) =>
      leaf.descriptor.setObjVal! "mlir" (toJson (name ++ ".mlir")))),
    ("top_verilog", toJson "hierarchy_top.sv")])
  return ⟨assembly.verilog, flat.mlir, leaves, descriptor⟩

def Export.write (out : Export) (dir : System.FilePath) (metadata : List (String × Json) := []) :
    IO Unit := do
  IO.FS.createDirAll dir
  for (name, leaf) in out.leaves do
    IO.FS.writeFile (dir / (name ++ ".mlir")) leaf.mlir
  IO.FS.writeFile (dir / "hierarchy_top.sv") out.verilog
  IO.FS.writeFile (dir / "flat.mlir") out.flatMlir
  let descriptor := (Json.mkObj metadata).mergeObj out.descriptor
  IO.FS.writeFile (dir / "interface.json") (descriptor.pretty ++ "\n")

end TypedHierarchy
end Pinwheel.Hardware
