import Pinwheel.Hardware.Processor.LoadableSystemStaged

/-! Four-leaf export of the loader-owned system. The bus reuses `SystemWiring`
with effective reset, while the RAM loader receives external reset. The top is
typed wiring only. No memory image or raw-state initialization is emitted. -/
namespace Pinwheel.Hardware.Processor.LoadableSystemExport

open Lean
open SystemExport (Snapshot snapshot snapshot_values tapped tapInterface portsJson leafJson writeLeaf
  connections declaration instanceText stateWire hierarchyReference coreInputWire mmioInputWire)

/-- `Joint` uses ordinal labels for both directions, so the exported input
descriptor adds a typed prefix to keep the top module's port names disjoint. -/
def inputs (aw : Nat) : Interface (LoadableSystem.Input aw) :=
  let d := LoadableSystem.inputs aw
  d.rename (fun p => "in_" ++ d.label p) (by
    intro a b h
    apply d.unique a b
    simpa only [String.append_right_inj] using h)

abbrev BusInput (aw : Nat) := Stream.Joint (LoadableSystem.Input aw)
  (Stream.Joint CoreInterface.Output (Stream.Joint Memory.ByteAdapterLoader.Output MmioInterface.Output))
abbrev BusOutput (aw : Nat) := Stream.Joint CoreInterface.Input
  (Stream.Joint (Memory.ByteAdapterLoader.Input aw) (Stream.Joint MmioInterface.Input LoadableSystem.statusPorts.Signal))

def busInputs (aw : Nat) : Interface (BusInput aw) := Stream.Joint.interface (LoadableSystem.inputs aw)
  (Stream.Joint.interface CoreInterface.outputs
    (Stream.Joint.interface Memory.ByteAdapterLoader.outputs MmioInterface.outputs))
def busOutputs (aw : Nat) : Interface (BusOutput aw) := Stream.Joint.interface CoreInterface.inputs
  (Stream.Joint.interface (Memory.ByteAdapterLoader.inputs aw)
    (Stream.Joint.interface MmioInterface.inputs LoadableSystem.statusPorts.interface))

def busSystemInput : {b : Nat} → SystemInterface.Input b → Expr (BusInput aw) SystemInterface.Fetch b
  | _, .at ⟨0,_⟩ => WordOps.wordOr (.input (.left LoadableSystem.reset)) (.input (.left LoadableSystem.mode))
  | _, .at ⟨k+1,h⟩ => .input (.left (.left (.at ⟨k+1,h⟩)))

def busNetwork : SystemWiring.Network (BusInput aw) SystemInterface.Fetch where
  pins := busSystemInput
  coreOutputs p := .input (.right (.left p))
  ramOutputs p := .input (.right (.right (.left (.left p))))
  mmioOutputs p := .input (.right (.right (.right p)))
  fetchValues p := .reg p

def busLoaderInput (layout : AddressMap.Layout rw aw) (ramFits : aw ≤ 30) :
    {b : Nat} → Memory.ByteAdapterLoader.Input aw b → Expr (BusInput aw) SystemInterface.Fetch b
  | _, .left (.at ⟨0,_⟩) => .input (.left LoadableSystem.reset)
  | _, .left (.at ⟨k+1,h⟩) => SystemWiring.ramInput busNetwork layout ramFits (.at ⟨k+1,h⟩)
  | _, .right p => .input (.left (.right p))

def status : {b : Nat} → LoadableSystem.statusPorts.Signal b → Expr (BusInput aw) SystemInterface.Fetch b
  | _, .at ⟨0,_⟩ => .band (.input (.left LoadableSystem.mode)) (.inv (.input (.left LoadableSystem.reset)))
  | _, .at ⟨1,_⟩ => .band (.inv (.input (.left LoadableSystem.mode))) (.inv (.input (.left LoadableSystem.reset)))
  | _, .at ⟨k+2,h⟩ => False.elim (by change k+2 < 2 at h; omega)

def busCircuit (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
    (romFits : rw ≤ 30) (ramFits : aw ≤ 30) : Circuit (BusInput aw) SystemInterface.Fetch (BusOutput aw) where
  next := SystemWiring.fetchNext busNetwork layout rom romFits
  output o := match o with
    | .left o => SystemWiring.coreInput busNetwork layout rom romFits o
    | .right (.left o) => busLoaderInput layout ramFits o
    | .right (.right (.left o)) => SystemWiring.mmioInput busNetwork layout o
    | .right (.right (.right o)) => status o

def ramInputWire (p : Memory.ByteAdapterLoader.Input aw b) : String :=
  "ram_input_" ++ (Memory.ByteAdapterLoader.inputs aw).label p
def ramOutputWire (p : Memory.ByteAdapterLoader.Output b) : String :=
  "ram_output_" ++ Memory.ByteAdapterLoader.outputs.label p

def busInputWire : BusInput aw b → String
  | .left p => (inputs aw).label p
  | .right (.left p) => LoadableSystem.outputs.label (.left (.left p))
  | .right (.right (.left p)) => ramOutputWire p
  | .right (.right (.right p)) => LoadableSystem.outputs.label (.left (.right p))

def busOutputWire : BusOutput aw b → String
  | .left p => coreInputWire p
  | .right (.left p) => ramInputWire p
  | .right (.right (.left p)) => mmioInputWire p
  | .right (.right (.right p)) => LoadableSystem.outputs.label (.right p)

def hierarchyVerilog (aw : Nat) (name : String) : String := Id.run do
  let ii := inputs aw
  let oi := LoadableSystem.outputs
  let ri := LoadableSystem.registers aw
  let ci := CoreInterface.inputs
  let co := tapInterface CoreInterface.outputs CoreCircuit.registers
  let mi := Memory.ByteAdapterLoader.inputs aw
  let mo := tapInterface Memory.ByteAdapterLoader.outputs (Memory.ByteAdapterLoader.registers aw)
  let pi := MmioInterface.inputs
  let po := tapInterface MmioInterface.outputs MmioCircuit.registers
  let bo := tapInterface (busOutputs aw) SystemInterface.fetchPorts.interface
  let ports := #["input wire clk"] ++
    ii.ports.map (fun ⟨b,p⟩ => declaration "input wire" (ii.label p) b) ++
    oi.ports.map (fun ⟨b,p⟩ => declaration "output wire" (oi.label p) b)
  let mut lines := #[s!"module {name}(" ++ String.intercalate ", " ports.toList ++ ");"]
  lines := lines ++ ci.ports.map (fun ⟨b,p⟩ => declaration "wire" (coreInputWire p) b ++ ";")
  lines := lines ++ mi.ports.map (fun ⟨b,p⟩ => declaration "wire" (ramInputWire p) b ++ ";")
  lines := lines ++ pi.ports.map (fun ⟨b,p⟩ => declaration "wire" (mmioInputWire p) b ++ ";")
  lines := lines ++ Memory.ByteAdapterLoader.outputs.ports.map
    (fun ⟨b,p⟩ => declaration "wire" (ramOutputWire p) b ++ ";")
  lines := lines ++ ri.ports.map (fun ⟨b,r⟩ => declaration "wire" (stateWire r) b ++ ";")
  lines := lines.push (instanceText (name ++ "_core") "core" (connections ci coreInputWire ++
    connections co (fun o => match o with
      | .left o => oi.label (.left (.left o)) | .right r => stateWire (SystemCircuit.core (aw := aw) r))))
  lines := lines.push (instanceText (name ++ "_ram") "ram" (connections mi ramInputWire ++
    connections mo (fun o => match o with
      | .left o => ramOutputWire o | .right r => stateWire (SystemCircuit.ram r))))
  lines := lines.push (instanceText (name ++ "_mmio") "mmio" (connections pi mmioInputWire ++
    connections po (fun o => match o with
      | .left o => oi.label (.left (.right o)) | .right r => stateWire (SystemCircuit.mmio (aw := aw) r))))
  lines := lines.push (instanceText (name ++ "_bus") "bus" (connections (busInputs aw) busInputWire ++
    connections bo (fun o => match o with
      | .left o => busOutputWire o | .right r => stateWire (SystemCircuit.fetch (aw := aw) r))))
  return String.intercalate "\n" (lines.push "endmodule").toList ++ "\n"

def interfaceJson (aw : Nat) (name : String) : Json :=
  let ii := inputs aw
  let oi := LoadableSystem.outputs
  let ri := LoadableSystem.registers aw
  let systemRoles := SystemInterface.inputs.ports.map fun ⟨_,p⟩ =>
    (SystemInterface.inputs.label p,toJson (ii.label (.left p)))
  let loaderRoles := (Memory.ByteAdapterLoader.loaderPorts aw).interface.ports.map fun ⟨_,p⟩ =>
    ((Memory.ByteAdapterLoader.loaderPorts aw).interface.label p,toJson (ii.label (.right p)))
  let coreRoles := CoreInterface.outputs.ports.map fun ⟨_,p⟩ =>
    ("core_"++CoreInterface.outputs.label p,toJson (oi.label (.left (.left p))))
  let mmioRoles := MmioInterface.outputs.ports.map fun ⟨_,p⟩ =>
    ("mmio_"++MmioInterface.outputs.label p,toJson (oi.label (.left (.right p))))
  let statusRoles := LoadableSystem.statusPorts.interface.ports.map fun ⟨_,p⟩ =>
    (LoadableSystem.statusPorts.interface.label p,toJson (oi.label (.right p)))
  let roles := systemRoles ++ loaderRoles ++ coreRoles ++ mmioRoles ++ statusRoles
  let regRows := ri.ports.map fun ⟨b,r⟩ => Json.mkObj
    [("index",toJson (ri.position r).val),("name",toJson (stateWire r)),
     ("reference",toJson (hierarchyReference r)),("flat_reference",toJson (stateWire r)),
     ("tap",toJson (stateWire r)),("width",toJson b)]
  Json.mkObj [("schema",toJson (1 : Nat)),("module",toJson name),("clock",toJson "clk"),
    ("inputs",portsJson ii),("outputs",portsJson oi),("registers",toJson regRows),
    ("roles",Json.mkObj roles.toList),("top_verilog",toJson "top.sv"),
    ("register_map",Json.mkObj (ri.ports.map (fun ⟨_,r⟩ => (stateWire r,toJson (hierarchyReference r)))).toList),
    ("hierarchical_registers",toJson (ri.ports.map fun ⟨_,r⟩ => hierarchyReference r)),
    ("leaf_interfaces",toJson #[
      leafJson (name++"_core") "core.mlir" CoreInterface.inputs CoreCircuit.registers CoreInterface.outputs,
      leafJson (name++"_ram") "ram.mlir" (Memory.ByteAdapterLoader.inputs aw)
        (Memory.ByteAdapterLoader.registers aw) Memory.ByteAdapterLoader.outputs,
      leafJson (name++"_mmio") "mmio.mlir" MmioInterface.inputs MmioCircuit.registers MmioInterface.outputs,
      leafJson (name++"_bus") "bus.mlir" (busInputs aw) SystemInterface.fetchPorts.interface (busOutputs aw)]),
    ("reset_synchronous",toJson true),("latency_added",toJson (0 : Nat)),
    ("startup",toJson "No raw initialization. Loader writes establish RAM words; Q and inactive metadata remain arbitrary until captured"),
    ("state_contract",toJson "complete one-to-one register mapping to LoadableSystem; no state is hidden by hierarchy"),
    ("loader_contract",toJson "mode holds core/fetch/MMIO reset; external reset blocks loader writes; host supplies every RAM word before run"),
    ("serial_boundary",toJson "byte arrival/completion/error pins are supplied by an external frontend")]

def exportHierarchy (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
    (romFits : rw ≤ 30) (ramFits : aw ≤ 30) (dir : System.FilePath) (name : String) : IO Json := do
  unless aw > 0 do throw (IO.userError "The physical RAM address port requires positive width")
  IO.FS.createDirAll dir
  writeLeaf dir "core.mlir" (name++"_core") CoreCircuit.circuit CoreInterface.inputs CoreCircuit.registers CoreInterface.outputs
  writeLeaf dir "ram.mlir" (name++"_ram") (Memory.ByteAdapterLoader.circuit aw)
    (Memory.ByteAdapterLoader.inputs aw) (Memory.ByteAdapterLoader.registers aw) Memory.ByteAdapterLoader.outputs
  writeLeaf dir "mmio.mlir" (name++"_mmio") MmioCircuit.circuit MmioInterface.inputs MmioCircuit.registers MmioInterface.outputs
  writeLeaf dir "bus.mlir" (name++"_bus") (busCircuit layout rom romFits ramFits)
    (busInputs aw) SystemInterface.fetchPorts.interface (busOutputs aw)
  IO.FS.writeFile (dir / "top.sv") (hierarchyVerilog aw name)
  let descriptor := interfaceJson aw name
  IO.FS.writeFile (dir / "interface.json") (descriptor.pretty++"\n")
  return descriptor

end Pinwheel.Hardware.Processor.LoadableSystemExport
