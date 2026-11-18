import Pinwheel.Hardware.Processor.LoadableSystemStaged
import Pinwheel.Hardware.TypedHierarchy

/-! Four-leaf export of the loader-owned system. The bus reuses `SystemWiring`
with effective reset, while the RAM loader receives external reset. The top is
typed wiring only. No memory image or raw-state initialization is emitted. -/
namespace Pinwheel.Hardware.Processor.LoadableSystemExport

open Lean
open SystemExport (tapped tapInterface portsJson leafJson stateWire coreInputWire mmioInputWire)

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

abbrev Net (aw : Nat) := Stream.Joint CoreInterface.Input
  (Stream.Joint (Memory.ByteAdapterLoader.Input aw) (Stream.Joint MmioInterface.Input
    (Stream.Joint Memory.ByteAdapterLoader.Output (LoadableSystem.Register aw))))

private def nets (aw : Nat) : Interface (Net aw) :=
  Stream.Joint.interface CoreInterface.inputs
    (Stream.Joint.interface (Memory.ByteAdapterLoader.inputs aw)
      (Stream.Joint.interface MmioInterface.inputs
        (Stream.Joint.interface Memory.ByteAdapterLoader.outputs (LoadableSystem.registers aw))))

private def netLabel : Net aw b → String
  | .left p => coreInputWire p
  | .right (.left p) => ramInputWire p
  | .right (.right (.left p)) => mmioInputWire p
  | .right (.right (.right (.left p))) => ramOutputWire p
  | .right (.right (.right (.right r))) => stateWire r

private def stateNet (r : LoadableSystem.Register aw b) : Net aw b :=
  .right (.right (.right (.right r)))

private def tappedModule (name : String) (c : Circuit I R O) (ii : Interface I)
    (ri : Interface R) (oi : Interface O) : TypedModule I R (Stream.Joint O R) :=
  ⟨name, tapped c, ii, ri, tapInterface oi ri⟩

/-- Preserve the original leaf boundaries, direct state taps and observable
ports. Only the bus/fetch instance selects providers and distributes reset. -/
def hierarchy (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
    (romFits : rw ≤ 30) (ramFits : aw ≤ 30) (name : String) :
    TypedHierarchy (LoadableSystem.Input aw) (LoadableSystem.Register aw)
      LoadableSystem.Output (Net aw) :=
  let core := TypedHierarchy.Instance.connect "core"
    (tappedModule (name ++ "_core") CoreCircuit.circuit CoreInterface.inputs
      CoreCircuit.registers CoreInterface.outputs)
    (fun p => .net (.left p))
    (fun p => match p with
      | .left p => .output (.left (.left p))
      | .right r => .net (stateNet (SystemCircuit.core r))) SystemCircuit.core
  let ram := TypedHierarchy.Instance.connect "ram"
    (tappedModule (name ++ "_ram") (Memory.ByteAdapterLoader.circuit aw)
      (Memory.ByteAdapterLoader.inputs aw) (Memory.ByteAdapterLoader.registers aw)
      Memory.ByteAdapterLoader.outputs)
    (fun p => .net (.right (.left p)))
    (fun p => match p with
      | .left p => .net (.right (.right (.right (.left p))))
      | .right r => .net (stateNet (SystemCircuit.ram r))) SystemCircuit.ram
  let mmio := TypedHierarchy.Instance.connect "mmio"
    (tappedModule (name ++ "_mmio") MmioCircuit.circuit MmioInterface.inputs
      MmioCircuit.registers MmioInterface.outputs)
    (fun p => .net (.right (.right (.left p))))
    (fun p => match p with
      | .left p => .output (.left (.right p))
      | .right r => .net (stateNet (SystemCircuit.mmio r))) SystemCircuit.mmio
  let bus := TypedHierarchy.Instance.connect "bus"
    (tappedModule (name ++ "_bus") (busCircuit layout rom romFits ramFits)
      (busInputs aw) SystemInterface.fetchPorts.interface (busOutputs aw))
    (fun p => match p with
      | .left p => .input p
      | .right (.left p) => .output (.left (.left p))
      | .right (.right (.left p)) => .net (.right (.right (.right (.left p))))
      | .right (.right (.right p)) => .output (.left (.right p)))
    (fun p => match p with
      | .left (.left p) => .net (.left p)
      | .left (.right (.left p)) => .net (.right (.left p))
      | .left (.right (.right (.left p))) => .net (.right (.right (.left p)))
      | .left (.right (.right (.right p))) => .output (.right p)
      | .right r => .net (stateNet (SystemCircuit.fetch r))) SystemCircuit.fetch
  ⟨name, ⟨name ++ "_flat", LoadableSystem.circuit layout rom romFits ramFits, inputs aw,
    LoadableSystem.registers aw, LoadableSystem.outputs⟩, nets aw, #[core, ram, mmio, bus]⟩

private def interfaceJson (aw : Nat) (name : String) (paths : Array String) : Json :=
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
  let regRows := ri.ports.mapIdx fun index ⟨b,r⟩ => Json.mkObj
    [("index",toJson (ri.position r).val),("name",toJson (stateWire r)),
     ("reference",toJson paths[index]!),("flat_reference",toJson (stateWire r)),
     ("tap",toJson (stateWire r)),("width",toJson b)]
  Json.mkObj [("schema",toJson (1 : Nat)),("module",toJson name),("clock",toJson "clk"),
    ("inputs",portsJson ii),("outputs",portsJson oi),("registers",toJson regRows),
    ("roles",Json.mkObj roles.toList),("top_verilog",toJson "top.sv"),
    ("register_map",Json.mkObj (ri.ports.mapIdx (fun index ⟨_,r⟩ => (stateWire r,toJson paths[index]!))).toList),
    ("hierarchical_registers",toJson paths),
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
  let design := hierarchy layout rom romFits ramFits name
  let assembly ← IO.ofExcept (design.layout netLabel)
  IO.FS.createDirAll dir
  for child in design.instances do
    let leaf := child.design
    let mlir ← IO.ofExcept (FastEmit.moduleText leaf.name leaf.circuit
      leaf.inputs.ports leaf.registers.ports leaf.outputs.ports
      leaf.inputs.label leaf.registers.label leaf.outputs.label)
    IO.FS.writeFile (dir / (child.name ++ ".mlir")) mlir
  IO.FS.writeFile (dir / "top.sv") assembly.verilog
  let descriptor := interfaceJson aw name assembly.registerPaths
  IO.FS.writeFile (dir / "interface.json") (descriptor.pretty++"\n")
  return descriptor

end Pinwheel.Hardware.Processor.LoadableSystemExport
