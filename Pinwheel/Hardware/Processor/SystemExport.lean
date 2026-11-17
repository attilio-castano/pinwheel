import Pinwheel.Hardware.Processor.SystemCircuit
import Pinwheel.Hardware.Processor.CoreCircuitRequests
import Pinwheel.Hardware.FastEmit
import Lean.Data.Json

/-! Component-preserving processor export and finite staged evaluation.
The bus reuses SystemWiring directly. Leaf next-state functions are unchanged;
raw taps expose every register. The Verilog assembly contains wiring only and
remains an unproved export boundary until checked by artifact readback.
-/
namespace Pinwheel.Hardware.Processor.SystemExport

open Lean

abbrev BusInput := Stream.Joint SystemInterface.Input
  (Stream.Joint CoreInterface.Output (Stream.Joint Memory.ByteAdapterInterface.Output MmioInterface.Output))
abbrev BusOutput (aw : Nat) := Stream.Joint CoreInterface.Input
  (Stream.Joint (Memory.ByteAdapterInterface.Input aw) MmioInterface.Input)

def busInputs : Interface BusInput := Stream.Joint.interface SystemInterface.inputs
  (Stream.Joint.interface CoreInterface.outputs
    (Stream.Joint.interface Memory.ByteAdapterInterface.outputs MmioInterface.outputs))
def busOutputs (aw : Nat) : Interface (BusOutput aw) := Stream.Joint.interface CoreInterface.inputs
  (Stream.Joint.interface (Memory.ByteAdapterInterface.inputs aw) MmioInterface.inputs)

def busNetwork : SystemWiring.Network BusInput SystemInterface.Fetch where
  pins p := .input (.left p)
  coreOutputs p := .input (.right (.left p))
  ramOutputs p := .input (.right (.right (.left p)))
  mmioOutputs p := .input (.right (.right (.right p)))
  fetchValues p := .reg p

def busCircuit (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30) : Circuit BusInput SystemInterface.Fetch (BusOutput aw) where
  next := SystemWiring.fetchNext busNetwork layout rom romFits
  output o := match o with
    | .left o => SystemWiring.coreInput busNetwork layout rom romFits o
    | .right (.left o) => SystemWiring.ramInput busNetwork layout ramFits o
    | .right (.right o) => SystemWiring.mmioInput busNetwork layout o

/-- A materialized finite valuation. The wrapper ensures its array is built
before the width-polymorphic lookup function is returned. -/
structure Snapshot (P : Nat → Type) where
  descriptor : Interface P
  cache : Vector Nat descriptor.size

def Snapshot.values (s : Snapshot P) : Values P :=
  fun p => BitVec.ofNat _ s.cache[(s.descriptor.position p).val]

def snapshot (d : Interface P) (v : Values P) : Snapshot P :=
  ⟨d, Vector.ofFn (fun k : Fin d.size => (v (d.signal k).2).toNat)⟩

@[simp] theorem snapshot_values (d : Interface P) (v : Values P) (p : P b) :
    (snapshot d v).values p = v p := by
  simp only [snapshot, Snapshot.values, Vector.getElem_ofFn]
  have h := congrArg (fun q : Sigma P => (v q.2).toNat) (d.signal_position p)
  rw [h]
  simp

def requestPins (i : Values SystemInterface.Input) : Values CoreInterface.Input
  | _, .at ⟨0,_⟩ => i SystemInterface.reset
  | _, .at _ => 0

/-- Only reset and request/readiness endpoints 0..10 feed the bus. Other core
outputs are computed from the actual service/response inputs in `staged`. -/
def requestValues (i : Values SystemInterface.Input) (s : Values CoreCircuit.Register) :
    Snapshot CoreInterface.Output :=
  snapshot CoreInterface.outputs (fun o =>
    if (CoreInterface.outputs.position o).val < 11 then CoreCircuit.circuit.observe (requestPins i) s o else 0)

def busValues (i : Values SystemInterface.Input) (c : Values CoreInterface.Output)
    (r : Values Memory.ByteAdapterInterface.Output) (m : Values MmioInterface.Output) : Values BusInput :=
  Stream.Joint.values i (Stream.Joint.values c (Stream.Joint.values r m))

structure Stage (aw : Nat) where
  coreInput : Snapshot CoreInterface.Input
  ramInput : Snapshot (Memory.ByteAdapterInterface.Input aw)
  mmioInput : Snapshot MmioInterface.Input
  mmioOutput : Snapshot MmioInterface.Output
  fetchNext : Snapshot SystemInterface.Fetch

def stages (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30) (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw)) : Stage aw :=
  let co := requestValues i (fun r => s (SystemCircuit.core r))
  let first : Values BusInput := busValues i co.values (fun _ => 0) (fun _ => 0)
  let fs : Values SystemInterface.Fetch := fun r => s (SystemCircuit.fetch r)
  let ri := snapshot (Memory.ByteAdapterInterface.inputs aw)
    (fun p => (SystemWiring.ramInput busNetwork layout ramFits p).eval first fs)
  let mi := snapshot MmioInterface.inputs (fun p => (SystemWiring.mmioInput busNetwork layout p).eval first fs)
  let ro := snapshot Memory.ByteAdapterInterface.outputs
    ((Memory.ByteAdapterCircuit.circuit aw).observe ri.values (fun r => s (SystemCircuit.ram r)))
  let mo := snapshot MmioInterface.outputs (MmioCircuit.circuit.observe mi.values (fun r => s (SystemCircuit.mmio r)))
  let connected : Values BusInput := busValues i co.values ro.values mo.values
  { coreInput := snapshot CoreInterface.inputs
      (fun p => (SystemWiring.coreInput busNetwork layout rom romFits p).eval connected fs)
    ramInput := ri, mmioInput := mi, mmioOutput := mo
    fetchNext := snapshot SystemInterface.fetchPorts.interface
      (fun p => (SystemWiring.fetchNext busNetwork layout rom romFits p).eval first fs) }

def nextSnapshot (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30) (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw)) :
    Snapshot (SystemCircuit.Register aw) :=
  let stage := stages layout rom romFits ramFits i s
  snapshot (SystemCircuit.registers aw) (fun r => match r with
    | .left r => CoreCircuit.circuit.step stage.coreInput.values (fun p => s (SystemCircuit.core p)) r
    | .right (.left r) => (Memory.ByteAdapterCircuit.circuit aw).step stage.ramInput.values (fun p => s (SystemCircuit.ram p)) r
    | .right (.right (.left r)) => MmioCircuit.circuit.step stage.mmioInput.values (fun p => s (SystemCircuit.mmio p)) r
    | .right (.right (.right r)) => stage.fetchNext.values r)

def outputSnapshot (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30) (i : Values SystemInterface.Input) (s : Values (SystemCircuit.Register aw)) :
    Snapshot SystemCircuit.Output :=
  let stage := stages layout rom romFits ramFits i s
  snapshot SystemCircuit.outputs (Stream.Joint.values
    (CoreCircuit.circuit.observe stage.coreInput.values (fun r => s (SystemCircuit.core r))) stage.mmioOutput.values)

def staged (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30) : Timed.Component (Values SystemInterface.Input) (Values (SystemCircuit.Register aw))
    (Values SystemCircuit.Output) where
  step i s := @Snapshot.values _ (nextSnapshot layout rom romFits ramFits i s)
  observe i s := @Snapshot.values _ (outputSnapshot layout rom romFits ramFits i s)

/-- Original outputs plus raw state taps, without modifying next-state logic. -/
def tapped (c : Circuit I R O) : Circuit I R (Stream.Joint O R) where
  next := c.next
  output o := match o with | .left o => c.output o | .right r => .reg r

def tapInterface (o : Interface O) (r : Interface R) : Interface (Stream.Joint O R) :=
  let d := Stream.Joint.interface o r
  d.rename (fun p => "out_" ++ d.label p) (by
    intro a b h
    apply d.unique a b
    simpa only [String.append_right_inj] using h)

theorem tapped_step (c : Circuit I R O) (i : Values I) (s : Values R) (r : R b) :
    (tapped c).step i s r = c.step i s r := rfl
theorem tapped_output (c : Circuit I R O) (i : Values I) (s : Values R) (o : O b) :
    (tapped c).observe i s (.left o) = c.observe i s o := rfl
theorem tapped_state (c : Circuit I R O) (i : Values I) (s : Values R) (r : R b) :
    (tapped c).observe i s (.right r) = s r := rfl

def stateWire (r : SystemCircuit.Register aw b) : String :=
  "r_" ++ (SystemCircuit.registers aw).label r

def hierarchyReference : SystemCircuit.Register aw b → String
  | .left r => "core.r_" ++ CoreCircuit.registers.label r
  | .right (.left r) => "ram.r_" ++ (Memory.ByteAdapterCircuit.registers aw).label r
  | .right (.right (.left r)) => "mmio.r_" ++ MmioCircuit.registers.label r
  | .right (.right (.right r)) => "bus.r_" ++ SystemInterface.fetchPorts.interface.label r

def coreInputWire (p : CoreInterface.Input b) : String := "core_input_" ++ CoreInterface.inputs.label p
def ramInputWire (p : Memory.ByteAdapterInterface.Input aw b) : String :=
  "ram_input_" ++ (Memory.ByteAdapterInterface.inputs aw).label p
def mmioInputWire (p : MmioInterface.Input b) : String := "mmio_input_" ++ MmioInterface.inputs.label p
def ramOutputWire (p : Memory.ByteAdapterInterface.Output b) : String :=
  "ram_output_" ++ Memory.ByteAdapterInterface.outputs.label p

def busInputWire : BusInput b → String
  | .left p => SystemInterface.inputs.label p
  | .right (.left p) => SystemCircuit.outputs.label (.left p)
  | .right (.right (.left p)) => ramOutputWire p
  | .right (.right (.right p)) => SystemCircuit.outputs.label (.right p)

def busOutputWire : BusOutput aw b → String
  | .left p => coreInputWire p
  | .right (.left p) => ramInputWire p
  | .right (.right p) => mmioInputWire p

def connections (d : Interface P) (wire : {b : Nat} → P b → String) : Array String :=
  d.ports.map fun ⟨_,p⟩ => s!".{d.label p}({wire p})"

def declaration (direction name : String) (bits : Nat) : String := s!"{direction} [{bits-1}:0] {name}"

def instanceText (moduleName instanceName : String) (ports : Array String) : String :=
  s!"{moduleName} {instanceName}(" ++ String.intercalate ", " (#[".clk(clk)"] ++ ports).toList ++ ");"

/-- The hierarchy assembly declares wires and instances only. Canonical bus
expressions and every leaf transition are still emitted by `Emit.moduleText`. -/
def hierarchyVerilog (aw : Nat) (name : String) : String := Id.run do
  let ii := SystemInterface.inputs
  let oi := SystemCircuit.outputs
  let ri := SystemCircuit.registers aw
  let ci := CoreInterface.inputs
  let co := tapInterface CoreInterface.outputs CoreCircuit.registers
  let mi := Memory.ByteAdapterInterface.inputs aw
  let mo := tapInterface Memory.ByteAdapterInterface.outputs (Memory.ByteAdapterCircuit.registers aw)
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
  lines := lines ++ Memory.ByteAdapterInterface.outputs.ports.map
    (fun ⟨b,p⟩ => declaration "wire" (ramOutputWire p) b ++ ";")
  lines := lines ++ ri.ports.map (fun ⟨b,r⟩ => declaration "wire" (stateWire r) b ++ ";")
  lines := lines.push (instanceText (name ++ "_core") "core" (connections ci coreInputWire ++
    connections co (fun o => match o with
      | .left o => oi.label (.left o) | .right r => stateWire (SystemCircuit.core (aw := aw) r))))
  lines := lines.push (instanceText (name ++ "_ram") "ram" (connections mi ramInputWire ++
    connections mo (fun o => match o with
      | .left o => ramOutputWire o | .right r => stateWire (SystemCircuit.ram r))))
  lines := lines.push (instanceText (name ++ "_mmio") "mmio" (connections pi mmioInputWire ++
    connections po (fun o => match o with
      | .left o => oi.label (.right o) | .right r => stateWire (SystemCircuit.mmio (aw := aw) r))))
  lines := lines.push (instanceText (name ++ "_bus") "bus" (connections busInputs busInputWire ++
    connections bo (fun o => match o with
      | .left o => busOutputWire o | .right r => stateWire (SystemCircuit.fetch (aw := aw) r))))
  return String.intercalate "\n" (lines.push "endmodule").toList ++ "\n"

def portsJson (d : Interface P) : Json := toJson (d.ports.map fun ⟨b,p⟩ => Json.mkObj
  [("index", toJson (d.position p).val), ("name", toJson (d.label p)), ("width", toJson b)])

def leafJson (name file : String) (i : Interface I) (r : Interface R) (o : Interface O) : Json :=
  Json.mkObj [("module",toJson name),("mlir",toJson file),("clock",toJson "clk"),
    ("inputs",portsJson i),("outputs",portsJson (tapInterface o r)),
    ("state_taps",Json.mkObj (r.ports.map (fun ⟨_,p⟩ =>
      ("r_"++r.label p,toJson ((tapInterface o r).label (.right p))))).toList),
    ("registers",toJson (r.ports.map fun ⟨b,p⟩ => Json.mkObj
      [("index",toJson (r.position p).val),("name",toJson ("r_"++r.label p)),
       ("reference",toJson ("r_"++r.label p)),("width",toJson b)]))]

def interfaceJson (aw : Nat) (name : String) : Json :=
  let ii := SystemInterface.inputs
  let oi := SystemCircuit.outputs
  let ri := SystemCircuit.registers aw
  let coreRoles := CoreInterface.outputs.ports.map fun ⟨_,p⟩ =>
    ("core_"++CoreInterface.outputs.label p,toJson (oi.label (.left p)))
  let mmioRoles := MmioInterface.outputs.ports.map fun ⟨_,p⟩ =>
    ("mmio_"++MmioInterface.outputs.label p,toJson (oi.label (.right p)))
  let roles := (ii.ports.map fun ⟨_,p⟩ => (ii.label p,toJson (ii.label p))) ++ coreRoles ++ mmioRoles
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
      leafJson (name++"_ram") "ram.mlir" (Memory.ByteAdapterInterface.inputs aw)
        (Memory.ByteAdapterCircuit.registers aw)
        Memory.ByteAdapterInterface.outputs,
      leafJson (name++"_mmio") "mmio.mlir" MmioInterface.inputs MmioCircuit.registers MmioInterface.outputs,
      leafJson (name++"_bus") "bus.mlir" busInputs SystemInterface.fetchPorts.interface (busOutputs aw)]),
    ("reset_synchronous",toJson true),("latency_added",toJson (0 : Nat)),
    ("startup",toJson "RAM words/Q and inactive metadata are arbitrary; reset cancels pending work but does not initialize RAM"),
    ("state_contract",toJson "complete one-to-one register mapping to SystemCircuit; no state is hidden by the hierarchy"),
    ("serial_boundary",toJson "byte arrival/completion/error pins are supplied by an external frontend")]

def writeLeaf (dir : System.FilePath) (file moduleName : String) (c : Circuit I R O)
    (ii : Interface I) (ri : Interface R) (oi : Interface O) : IO Unit := do
  IO.FS.writeFile (dir / file) (← IO.ofExcept
    (FastEmit.moduleText moduleName (tapped c) ii.ports ri.ports (tapInterface oi ri).ports
      ii.label ri.label (tapInterface oi ri).label))

/-- Emit four component modules and their typed wiring. The returned descriptor
can be extended with a particular ROM image and checked address-map metadata. -/
def exportHierarchy (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
    (romFits : rw ≤ 30) (ramFits : aw ≤ 30) (dir : System.FilePath) (name : String) : IO Json := do
  unless aw > 0 do throw (IO.userError "The physical RAM address port requires positive width")
  IO.FS.createDirAll dir
  writeLeaf dir "core.mlir" (name++"_core") CoreCircuit.circuit CoreInterface.inputs CoreCircuit.registers CoreInterface.outputs
  writeLeaf dir "ram.mlir" (name++"_ram") (Memory.ByteAdapterCircuit.circuit aw)
    (Memory.ByteAdapterInterface.inputs aw) (Memory.ByteAdapterCircuit.registers aw) Memory.ByteAdapterInterface.outputs
  writeLeaf dir "mmio.mlir" (name++"_mmio") MmioCircuit.circuit MmioInterface.inputs MmioCircuit.registers MmioInterface.outputs
  writeLeaf dir "bus.mlir" (name++"_bus") (busCircuit layout rom romFits ramFits)
    busInputs SystemInterface.fetchPorts.interface (busOutputs aw)
  IO.FS.writeFile (dir / "top.sv") (hierarchyVerilog aw name)
  let descriptor := interfaceJson aw name
  IO.FS.writeFile (dir / "interface.json") (descriptor.pretty++"\n")
  return descriptor

end Pinwheel.Hardware.Processor.SystemExport
