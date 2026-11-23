import Pinwheel.Hardware.Processor.SystemWiring
import Pinwheel.Hardware.Processor.CoreCircuit
import Pinwheel.Hardware.Processor.AddressDecode
import Pinwheel.Hardware.Processor.MmioCircuit
import Pinwheel.Hardware.Memory.ByteAdapterCircuit

/-! Structural ROM/RAM/MMIO composition for a serialized core. ROM words are
explicit elaboration-time constants. RAM uses the existing one-outstanding byte
adapter, with a distinct owned response edge. Devices use the atomic MMIO port.
Serial frontend events are external input pins. SystemCircuitProofs supplies
correspondence to the connected system model. -/
namespace Pinwheel.Hardware.Processor.SystemCircuit

abbrev inputPorts := SystemInterface.inputPorts
abbrev Input := SystemInterface.Input
abbrev fetchPorts := SystemInterface.fetchPorts
abbrev Fetch := SystemInterface.Fetch
export SystemInterface (inputs reset gpioInput txComplete rxValid rxData framingError)

abbrev Register (aw : Nat) := Stream.Joint CoreCircuit.Register
  (Stream.Joint (Memory.ByteAdapterCircuit.Register aw) (Stream.Joint MmioCircuit.Register Fetch))
abbrev Output := Stream.Joint CoreInterface.Output MmioInterface.Output
def registers (aw : Nat) : Interface (Register aw) :=
  Stream.Joint.interface CoreCircuit.registers
    (Stream.Joint.interface (Memory.ByteAdapterCircuit.registers aw)
      (Stream.Joint.interface MmioCircuit.registers fetchPorts.interface))
def outputs : Interface Output := Stream.Joint.interface CoreInterface.outputs MmioInterface.outputs
def core (r : CoreCircuit.Register b) : Register aw b := .left r
def ram (r : Memory.ByteAdapterCircuit.Register aw b) : Register aw b := .right (.left r)
def mmio (r : MmioCircuit.Register b) : Register aw b := .right (.right (.left r))
def fetch (r : Fetch b) : Register aw b := .right (.right (.right r))
def fetchValid : Register aw 1 := fetch (.at ⟨0,by decide⟩)
def fetchFault : Register aw 1 := fetch (.at ⟨1,by decide⟩)
def fetchData : Register aw 32 := fetch (.at ⟨2,by decide⟩)
abbrev E (aw b : Nat) := Expr Input (Register aw) b
def both (a b : E aw 1) : E aw 1 := .band a b
def either (a b : E aw 1) : E aw 1 := WordOps.wordOr a b
def gate (enabled : E aw 1) (value : E aw b) : E aw b := .mux enabled value (.lit 0)

/-- Request-only outputs depend on reset and the held core state. Response pins
are filled with zero for this acyclic construction of the request network. -/
def requestInput : {b : Nat} → CoreInterface.Input b → E aw b
  | _, .at ⟨0,_⟩ => .input reset
  | _, .at _ => .lit 0
def offer (o : CoreInterface.Output b) : E aw b :=
  (CoreCircuit.circuit.output o).bind requestInput (fun r => .reg (core r))

def requestNetwork : SystemWiring.Network Input (Register aw) where
  pins := fun p => .input p
  coreOutputs := offer
  ramOutputs := fun _ => .lit 0
  mmioOutputs := fun _ => .lit 0
  fetchValues := fun p => .reg (fetch p)

variable (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

def route : E aw 3 := SystemWiring.route requestNetwork layout
def region (code : BitVec 3) : E aw 1 := SystemWiring.region requestNetwork layout code
def ramInput : {b : Nat} → Memory.ByteAdapterInterface.Input aw b → E aw b :=
  SystemWiring.ramInput requestNetwork layout ramFits
def ramOutput (o : Memory.ByteAdapterInterface.Output b) : E aw b :=
  ((Memory.ByteAdapterCircuit.circuit aw).output o).bind (ramInput layout ramFits) (fun r => .reg (ram r))
def mmioInput : {b : Nat} → MmioInterface.Input b → E aw b := SystemWiring.mmioInput requestNetwork layout
def mmioOutput (o : MmioInterface.Output b) : E aw b :=
  (MmioCircuit.circuit.output o).bind (mmioInput layout) (fun r => .reg (mmio r))
def network : SystemWiring.Network Input (Register aw) :=
  { requestNetwork with ramOutputs := ramOutput layout ramFits, mmioOutputs := mmioOutput layout }
def coreInput : {b : Nat} → CoreInterface.Input b → E aw b :=
  SystemWiring.coreInput (network layout ramFits) layout rom romFits
def fetchNext : {b : Nat} → Fetch b → E aw b := SystemWiring.fetchNext requestNetwork layout rom romFits

def circuit : Circuit Input (Register aw) Output where
  next r := match r with
    | .left r => (CoreCircuit.circuit.next r).bind (coreInput layout rom romFits ramFits) (fun r => .reg (core r))
    | .right (.left r) => ((Memory.ByteAdapterCircuit.circuit aw).next r).bind (ramInput layout ramFits) (fun r => .reg (ram r))
    | .right (.right (.left r)) => (MmioCircuit.circuit.next r).bind (mmioInput layout) (fun r => .reg (mmio r))
    | .right (.right (.right r)) => fetchNext layout rom romFits r
  output o := match o with
    | .left o => (CoreCircuit.circuit.output o).bind (coreInput layout rom romFits ramFits) (fun r => .reg (core r))
    | .right o => mmioOutput layout o

end Pinwheel.Hardware.Processor.SystemCircuit
