import Pinwheel.Hardware.Stream.Normalize
import Lean.Data.Json

namespace Pinwheel.Hardware.Stream
open Lean

inductive Tap (w : Nat) : Nat → Type where
  | normal : Out w b → Tap w b
  | rawReady : Tap w 1
  | rawValid : Tap w 1
  | rawData : Tap w w

def tapCircuit (c : Certified wi wo) : Circuit (In wi) c.Register (Tap wo) where
  next := c.circuit.next
  output := fun p => match p with
    | .normal p => c.circuit.output p
    | .rawReady => (c.circuit.output inReady).bind (probeInput (.input ready)) (.reg)
    | .rawValid => (c.circuit.output outValid).bind (probeInput (.lit 0)) (.reg)
    | .rawData => (c.circuit.output outData).bind (probeInput (.lit 0)) (.reg)

def tapRtl (c : Certified wi wo) (name : String) : Except String String :=
  let ports : Array (Sigma (Tap wo)) :=
    (outputPorts wo).interface.ports.map (fun p => ⟨p.1, .normal p.2⟩) ++
      #[⟨1, .rawReady⟩, ⟨1, .rawValid⟩, ⟨wo, .rawData⟩]
  Emit.moduleText name (tapCircuit c) (inputPorts wi).interface.ports c.registers.ports ports
    (inputPorts wi).interface.label c.registers.label (fun p => match p with
      | .normal p => (outputPorts wo).interface.label p
      | .rawReady => "raw_ready" | .rawValid => "raw_valid" | .rawData => "raw_data")

def vectorPort (direction name : String) (width : Nat) : String :=
  s!"{direction} wire [{width - 1}:0] {name}"

def streamPorts (wi wo : Nat) (taps : Bool) : String :=
  let base := #["input wire clk"] ++
    (inputPorts wi).interface.ports.map (fun p => vectorPort "input" ((inputPorts wi).interface.label p.2) p.1) ++
    (outputPorts wo).interface.ports.map (fun p => vectorPort "output" ((outputPorts wo).interface.label p.2) p.1)
  String.intercalate ", " (base ++ (if taps then
    #["output wire raw_ready", "output wire raw_valid", vectorPort "output" "raw_data" wo] else #[])).toList

/-- Hierarchical HDL wiring implements the same typed probe/serial construction
as `serialCircuit`. Fresh artifact correspondence independently checks it. -/
def serialVerilog (wi wm wo : Nat) (name left right : String) : String :=
  s!"module {name}({streamPorts wi wo true});\n" ++
  s!"wire left_valid, right_ready; wire [{wm - 1}:0] left_data;\n" ++
  s!"{left} left(.clk(clk), .reset(reset), .in_valid(in_valid), .in_data(in_data),\n" ++
  "  .out_ready(right_ready), .in_ready(in_ready), .out_valid(), .out_data(),\n" ++
  "  .raw_ready(raw_ready), .raw_valid(left_valid), .raw_data(left_data));\n" ++
  s!"{right} right(.clk(clk), .reset(reset), .in_valid(left_valid), .in_data(left_data),\n" ++
  "  .out_ready(out_ready), .in_ready(), .out_valid(out_valid), .out_data(out_data),\n" ++
  "  .raw_ready(right_ready), .raw_valid(raw_valid), .raw_data(raw_data));\nendmodule\n"

def wrapperVerilog (wi wo : Nat) (child : String) : String :=
  s!"module pinwheel_stream({streamPorts wi wo false});\n" ++
  s!"{child} core(.clk(clk), .reset(reset), .in_valid(in_valid), .in_data(in_valid ? in_data : {wi}'d0),\n" ++
  "  .out_ready(out_ready), .in_ready(in_ready), .out_valid(out_valid), .out_data(out_data),\n" ++
  "  .raw_ready(), .raw_valid(), .raw_data());\nendmodule\n"

def parallelVerilog (wi wa wb : Nat) (name left right : String) : String :=
  s!"module {name}({streamPorts wi (wa + wb) true});\n" ++
  s!"wire lv, rv, lr, rr; wire [{wa - 1}:0] ld; wire [{wb - 1}:0] rd;\n" ++
  s!"{left} left(.clk(clk), .reset(reset), .in_valid(in_valid & rr),\n" ++
  s!"  .in_data(rr ? in_data : {wi}'d0), .out_ready(out_ready & rv),\n" ++
  "  .in_ready(), .out_valid(), .out_data(), .raw_ready(lr), .raw_valid(lv), .raw_data(ld));\n" ++
  s!"{right} right(.clk(clk), .reset(reset), .in_valid(in_valid & lr),\n" ++
  s!"  .in_data(lr ? in_data : {wi}'d0), .out_ready(out_ready & lv),\n" ++
  "  .in_ready(), .out_valid(), .out_data(), .raw_ready(rr), .raw_valid(rv), .raw_data(rd));\n" ++
  "assign raw_ready = lr & rr; assign raw_valid = lv & rv;\n" ++
  "assign raw_data = raw_valid ? {ld, rd} : " ++ s!"{wa + wb}'d0;\n" ++
  "assign in_ready = ~reset & raw_ready; assign out_valid = ~reset & raw_valid;\n" ++
  s!"assign out_data = reset ? {wa + wb}'d0 : raw_data;\nendmodule\n"

def Design.hierarchicalRegisters (d : Design wi wo) (path : String) : Array String :=
  match d with
  | .leaf _ c => c.registers.ports.map fun p => path ++ ".r_" ++ c.registers.label p.2
  | .serial a b => a.hierarchicalRegisters (path ++ ".left") ++ b.hierarchicalRegisters (path ++ ".right")
  | .parallel a b => a.hierarchicalRegisters (path ++ ".left") ++ b.hierarchicalRegisters (path ++ ".right")

def Design.outputWidth (_ : Design wi wo) : Nat := wo

def Design.exportHierarchy (d : Design wi wo) (dir : System.FilePath) (name : String) : IO (Array String) :=
  match d with
  | .leaf _ c => do
    let text ← IO.ofExcept (tapRtl c name)
    IO.FS.writeFile (dir / s!"{name}.mlir") text
    return #[name]
  | .serial a b => do
    let al ← a.exportHierarchy dir (name ++ "_left")
    let bl ← b.exportHierarchy dir (name ++ "_right")
    IO.FS.writeFile (dir / s!"{name}.sv") (serialVerilog wi a.outputWidth wo name (name ++ "_left") (name ++ "_right"))
    return al ++ bl
  | .parallel a b => do
    let al ← a.exportHierarchy dir (name ++ "_left")
    let bl ← b.exportHierarchy dir (name ++ "_right")
    IO.FS.writeFile (dir / s!"{name}.sv") (parallelVerilog wi a.outputWidth b.outputWidth name (name ++ "_left") (name ++ "_right"))
    return al ++ bl

def interfaceJson (d : Interface P) : Json := toJson (d.ports.mapIdx fun k p =>
  Json.mkObj [("name", toJson (d.label p.2)), ("width", toJson p.1), ("index", toJson k)])

def exportDesign (d : Design wi wo) (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "flat.mlir") (← IO.ofExcept (d.flatten.normalized.rtl "pinwheel_stream"))
  let leaves ← d.exportHierarchy dir "stream_core"
  IO.FS.writeFile (dir / "hierarchy_top.sv") (wrapperVerilog wi wo "stream_core")
  let descriptor := Json.mkObj [
    ("inputs", interfaceJson (inputPorts wi).interface),
    ("outputs", interfaceJson (outputPorts wo).interface),
    ("registers", interfaceJson d.flatten.registers),
    ("hierarchical_registers", toJson (d.hierarchicalRegisters "core")),
    ("leaves", toJson leaves)]
  IO.FS.writeFile (dir / "interface.json") descriptor.pretty

end Pinwheel.Hardware.Stream
