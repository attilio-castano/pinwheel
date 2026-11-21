import Pinwheel.Hardware.Memory.TransferHostCircuit
import Pinwheel.Hardware.TypedHierarchy

/-! The host accelerator's controller owns its original registers and the
two memory instances own theirs. Control consumes raw memory taps, so command
selection and next-state logic have no combinational feedback through a memory
request port. The flat circuit remains the correspondence reference. -/
namespace Pinwheel.Hardware.Memory.TransferHostExport

open TransferHostInterface
open Hardware.Stream (Joint)

abbrev MemoryState (a wi wo : Nat) := Joint (StreamFlops.Register a wi) (StreamFlops.Register a wo)
abbrev MemoryPins (a wi wo : Nat) := Joint (StreamInterface.Input a wi) (StreamInterface.Input a wo)
abbrev ControlInput (a wi wo : Nat) := Joint (Input a wi wo) (MemoryState a wi wo)
abbrev ControlOutput (a wi wo : Nat) := Joint (Output wi wo) (MemoryPins a wi wo)
abbrev Net (a wi wo : Nat) := Joint (MemoryPins a wi wo) (MemoryState a wi wo)

private def memoryState (a wi wo : Nat) : Interface (MemoryState a wi wo) :=
  Joint.interface (StreamFlops.registers a wi) (StreamFlops.registers a wo)

private def memoryPins (a wi wo : Nat) : Interface (MemoryPins a wi wo) :=
  Joint.interface (StreamInterface.inputs a wi) (StreamInterface.inputs a wo)

private def controlExpr (e : Expr (Input a wi wo) (TransferHostCircuit.Register a wi wo) b) :
    Expr (ControlInput a wi wo) (TransferCircuit.Register a) b :=
  e.bind (fun p => .input (.left p)) (fun r => match r with
    | .left p => .reg p
    | .right p => .input (.right p))

private def control (m : Hardware.Stream.Map wi wo) :
    Circuit (ControlInput a wi wo) (TransferCircuit.Register a) (ControlOutput a wi wo) where
  next := fun r => controlExpr ((TransferHostCircuit.circuit m).next (.left r))
  output := fun p => controlExpr (match p with
    | .left p => (TransferHostCircuit.circuit m).output p
    | .right (.left p) => TransferHostCircuit.sourceInput m p
    | .right (.right p) => TransferHostCircuit.destinationInput m p)

private def controlOutputs (a wi wo : Nat) : Interface (ControlOutput a wi wo) :=
  let ports := Joint.interface (outputs wi wo) (memoryPins a wi wo)
  ports.rename (fun p => "out_" ++ ports.label p)
    (fun i j h => ports.unique i j (by simpa only [String.append_right_inj] using h))

private def memory (a width : Nat) (name : String) :
    TypedModule (StreamInterface.Input a width) (StreamFlops.Register a width) (StreamFlops.Register a width) :=
  let regs := StreamFlops.registers a width
  ⟨s!"{name}_memory_w{width}", TypedHierarchy.stateTaps (StreamFlops.circuit a width),
    StreamInterface.inputs a width, regs, regs⟩

def hierarchy (m : Hardware.Stream.Map wi wo) (a : Nat) (name : String) :
    TypedHierarchy (Input a wi wo) (TransferHostCircuit.Register a wi wo) (Output wi wo) (Net a wi wo) :=
  let ii := inputs a wi wo
  let oi := outputs wi wo
  let ctl : TypedModule _ _ _ := ⟨name ++ "_control", control m,
    Joint.interface ii (memoryState a wi wo), TransferCircuit.registers a, controlOutputs a wi wo⟩
  let controller := TypedHierarchy.Instance.connect "control" ctl
    (fun p => match p with | .left p => .input p | .right p => .net (.right p))
    (fun p => match p with | .left p => .output p | .right p => .net (.left p)) Joint.left
  let source := TypedHierarchy.Instance.connect "source" (memory a wi name)
    (fun p => .net (.left (.left p))) (fun p => .net (.right (.left p))) (fun r => .right (.left r))
  let destination := TypedHierarchy.Instance.connect "destination" (memory a wo name)
    (fun p => .net (.left (.right p))) (fun p => .net (.right (.right p))) (fun r => .right (.right r))
  ⟨name, ⟨name ++ "_flat", TransferHostCircuit.circuit m, ii, TransferHostCircuit.registers a wi wo, oi⟩,
    Joint.interface (memoryPins a wi wo) (memoryState a wi wo), #[controller, source, destination]⟩

end Pinwheel.Hardware.Memory.TransferHostExport
