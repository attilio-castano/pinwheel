import Pinwheel.Hardware.Processor.SystemCircuit
import Pinwheel.Hardware.Memory.ByteAdapterLoader

/-! Explicit loader ownership for the processor system. Loader mode holds core,
devices and fetch control in reset while the existing RAM loader accepts full
words. External reset blocks loader writes. The host establishes complete image
coverage before deasserting loader mode. No physical register is initialized by
the exporter or by an implicit memory image. -/
namespace Pinwheel.Hardware.Processor.LoadableSystem

abbrev Input (aw : Nat) := Stream.Joint SystemInterface.Input (Memory.ByteAdapterLoader.Loader aw)
abbrev Register (aw : Nat) := SystemCircuit.Register aw
abbrev statusPorts : Stream.Ports where
  size := 2
  widths := fun _ => 1
  names := fun k => #["loader_ready","running"][k]
  distinct := by decide +kernel
abbrev Output := Stream.Joint SystemCircuit.Output statusPorts.Signal
def inputs (aw : Nat) : Interface (Input aw) :=
  Stream.Joint.interface SystemInterface.inputs (Memory.ByteAdapterLoader.loaderPorts aw).interface
def outputs : Interface Output := Stream.Joint.interface SystemCircuit.outputs statusPorts.interface
def registers (aw : Nat) : Interface (Register aw) := SystemCircuit.registers aw

def reset : Input aw 1 := .left SystemInterface.reset
def mode : Input aw 1 := .right (.at ⟨0,by change 0 < 4; decide⟩)
def valid : Input aw 1 := .right (.at ⟨1,by change 1 < 4; decide⟩)
def address : Input aw aw := .right (.at ⟨2,by change 2 < 4; decide⟩)
def data : Input aw 32 := .right (.at ⟨3,by change 3 < 4; decide⟩)

/-- Actual host admission: loader ownership, no external reset, and a valid offer. -/
def Accepted (i : Values (Input aw)) : Prop := i mode = 1 ∧ i reset = 0 ∧ i valid = 1
instance (i : Values (Input aw)) : Decidable (Accepted i) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

abbrev E (aw b : Nat) := Expr (Input aw) (Register aw) b
def effectiveReset : E aw 1 := WordOps.wordOr (.input reset) (.input mode)
def systemInput : {b : Nat} → SystemInterface.Input b → E aw b
  | _, .at ⟨0,_⟩ => effectiveReset
  | _, .at k => .input (.left (.at k))

variable (layout : AddressMap.Layout rw aw) (rom : BitVec rw → BitVec 32)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

def loaderInput : {b : Nat} → Memory.ByteAdapterLoader.Input aw b → E aw b
  | _, .left (.at ⟨0,_⟩) => .input reset
  | _, .left (.at ⟨1,h⟩) => (SystemCircuit.ramInput layout ramFits (.at ⟨1,h⟩)).bind systemInput Expr.reg
  | _, .left (.at ⟨2,h⟩) => (SystemCircuit.ramInput layout ramFits (.at ⟨2,h⟩)).bind systemInput Expr.reg
  | _, .left (.at ⟨3,h⟩) => (SystemCircuit.ramInput layout ramFits (.at ⟨3,h⟩)).bind systemInput Expr.reg
  | _, .left (.at ⟨4,h⟩) => (SystemCircuit.ramInput layout ramFits (.at ⟨4,h⟩)).bind systemInput Expr.reg
  | _, .left (.at ⟨5,h⟩) => (SystemCircuit.ramInput layout ramFits (.at ⟨5,h⟩)).bind systemInput Expr.reg
  | _, .left (.at ⟨6,h⟩) => (SystemCircuit.ramInput layout ramFits (.at ⟨6,h⟩)).bind systemInput Expr.reg
  | _, .left (.at ⟨7,h⟩) => (SystemCircuit.ramInput layout ramFits (.at ⟨7,h⟩)).bind systemInput Expr.reg
  | _, .left (.at ⟨8,h⟩) => (SystemCircuit.ramInput layout ramFits (.at ⟨8,h⟩)).bind systemInput Expr.reg
  | _, .left (.at ⟨k+9,h⟩) => False.elim (by change k+9 < 9 at h; omega)
  | _, .right p => .input (.right p)

def next : {b : Nat} → Register aw b → E aw b
  | _, .left p => ((SystemCircuit.circuit layout rom romFits ramFits).next (.left p)).bind systemInput Expr.reg
  | _, .right (.left p) => ((Memory.ByteAdapterLoader.circuit aw).next p).bind (loaderInput layout ramFits)
      (fun r => .reg (SystemCircuit.ram r))
  | _, .right (.right p) => ((SystemCircuit.circuit layout rom romFits ramFits).next (.right (.right p))).bind systemInput Expr.reg

def circuit : Circuit (Input aw) (Register aw) Output where
  next := next layout rom romFits ramFits
  output := fun {b} o => match b,o with
    | _, .left o => ((SystemCircuit.circuit layout rom romFits ramFits).output o).bind systemInput Expr.reg
    | _, .right (.at ⟨0,_⟩) => .band (.input mode) (.inv (.input reset))
    | _, .right (.at ⟨1,_⟩) => .band (.inv (.input mode)) (.inv (.input reset))
    | _, .right (.at ⟨k+2,h⟩) => False.elim (by change k+2 < 2 at h; omega)

end Pinwheel.Hardware.Processor.LoadableSystem
