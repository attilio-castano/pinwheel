import Pinwheel.Hardware.Memory.TransferHostInterface
import Pinwheel.Hardware.Memory.TransferCircuit

/-! Host ownership muxes around the existing transfer controller and two stream
memories. There are no extra registers. Every subcircuit reads the same pre-edge
state. Controller feedback is a finite expression: destination ready is reset
gated true, and source ready depends only on pending and response readiness.
-/
namespace Pinwheel.Hardware.Memory.TransferHostCircuit

open TransferHostInterface

abbrev Register (a wi wo : Nat) := Hardware.Stream.Joint (TransferCircuit.Register a)
  (Hardware.Stream.Joint (StreamFlops.Register a wi) (StreamFlops.Register a wo))

def registers (a wi wo : Nat) : Interface (Register a wi wo) :=
  Hardware.Stream.Joint.interface (TransferCircuit.registers a)
    (Hardware.Stream.Joint.interface (StreamFlops.registers a wi) (StreamFlops.registers a wo))

theorem register_count (a wi wo : Nat) : (registers a wi wo).size = 7 + (2^a+2) + (2^a+2) := by
  change 7 + ((2^a+2) + (2^a+2)) = _
  omega

def controlValues (s : Values (Register a wi wo)) : Values (TransferCircuit.Register a) := fun r => s (.left r)
def sourceValues (s : Values (Register a wi wo)) : Values (StreamFlops.Register a wi) := fun r => s (.right (.left r))
def destinationValues (s : Values (Register a wi wo)) : Values (StreamFlops.Register a wo) := fun r => s (.right (.right r))

def encode (s : TransferModel.State a wi wo) : Values (Register a wi wo)
  | _, .left r => TransferCircuit.encode s.control r
  | _, .right (.left r) => StreamFlops.encode s.source r
  | _, .right (.right r) => StreamFlops.encode s.destination r

def phase (value : BitVec 2) : Expr (Input a wi wo) (Register a wi wo) 1 :=
  .equal (.reg (.left .phase)) (.lit value)

def memoryReset : Expr (Input a wi wo) (Register a wi wo) 1 := (Expr.input reset).bor (phase 3)
def sourcePending : Expr (Input a wi wo) (Register a wi wo) 1 := .reg (.right (.left StreamFlops.pending))
def destinationPending : Expr (Input a wi wo) (Register a wi wo) 1 := .reg (.right (.right StreamFlops.pending))

def canStart : Expr (Input a wi wo) (Register a wi wo) 1 :=
  .band (.inv (.input reset)) (.band (phase 0) (.band (.inv sourcePending) (.inv destinationPending)))

def acceptedStart : Expr (Input a wi wo) (Register a wi wo) 1 := .band canStart (.input startValid)
def hostMode : Expr (Input a wi wo) (Register a wi wo) 1 := .band (phase 0) (.inv acceptedStart)
def controllerResponseReady : Expr (Input a wi wo) (Register a wi wo) 1 := .band (phase 2) (.inv memoryReset)
def controllerResponseValid : Expr (Input a wi wo) (Register a wi wo) 1 := .band (.inv memoryReset) sourcePending

def controllerInput : {b : Nat} → TransferInterface.Input a wi b → Expr (Input a wi wo) (Register a wi wo) b
  | _, .at ⟨0, _⟩ => .input reset
  | _, .at ⟨1, _⟩ => acceptedStart
  | _, .at ⟨2, _⟩ => .input sourceBase
  | _, .at ⟨3, _⟩ => .input destinationBase
  | _, .at ⟨4, _⟩ => .input length
  | _, .at ⟨5, _⟩ => .band (.inv memoryReset) ((Expr.inv sourcePending).bor controllerResponseReady)
  | _, .at ⟨6, _⟩ => controllerResponseValid
  | _, .at ⟨7, _⟩ => .mux controllerResponseValid (.reg (.right (.left (.left CommandFlops.q)))) (.lit 0)
  | _, .at ⟨8, _⟩ => .inv memoryReset
  | _, .at ⟨k+9, h⟩ => False.elim (by change k+9 < 9 at h; omega)

def controllerPins (i : Values (Input a wi wo)) (s : Values (Register a wi wo)) :
    Values (TransferInterface.Input a wi) := fun p => (controllerInput p).eval i s

def controllerOutput (m : Hardware.Stream.Map wi wo) (p : TransferInterface.Output a wo b) :
    Expr (Input a wi wo) (Register a wi wo) b :=
  ((TransferCircuit.circuit m).output p).bind controllerInput (fun r => .reg (.left r))

def sourceHostInput : {b : Nat} → StreamInterface.Input a wi b → Expr (Input a wi wo) (Register a wi wo) b
  | _, .at ⟨0, _⟩ => .input reset
  | _, .at ⟨1, _⟩ => .band (.input sourceValid) (.inv (.input startValid))
  | _, .at ⟨2, _⟩ => .input sourceWrite
  | _, .at ⟨3, _⟩ => .input sourceAddress
  | _, .at ⟨4, _⟩ => .input sourceData
  | _, .at ⟨5, _⟩ => .input sourceReady
  | _, .at ⟨k+6, h⟩ => False.elim (by change k+6 < 6 at h; omega)

def destinationHostInput : {b : Nat} → StreamInterface.Input a wo b → Expr (Input a wi wo) (Register a wi wo) b
  | _, .at ⟨0, _⟩ => .input reset
  | _, .at ⟨1, _⟩ => .band (.input destinationValid) (.inv (.input startValid))
  | _, .at ⟨2, _⟩ => .input destinationWrite
  | _, .at ⟨3, _⟩ => .input destinationAddress
  | _, .at ⟨4, _⟩ => .input destinationData
  | _, .at ⟨5, _⟩ => .input destinationReady
  | _, .at ⟨k+6, h⟩ => False.elim (by change k+6 < 6 at h; omega)

def sourceHostValues (i : Values (Input a wi wo)) (s : Values (Register a wi wo)) :
    Values (StreamInterface.Input a wi) := fun p => (sourceHostInput p).eval i s

def destinationHostValues (i : Values (Input a wi wo)) (s : Values (Register a wi wo)) :
    Values (StreamInterface.Input a wo) := fun p => (destinationHostInput p).eval i s

def sourceControllerInput (m : Hardware.Stream.Map wi wo) :
    {b : Nat} → StreamInterface.Input a wi b → Expr (Input a wi wo) (Register a wi wo) b
  | _, .at ⟨0, _⟩ => controllerOutput m TransferInterface.memoryReset
  | _, .at ⟨1, _⟩ => controllerOutput m TransferInterface.sourceRequestValid
  | _, .at ⟨2, _⟩ => .lit 0
  | _, .at ⟨3, _⟩ => controllerOutput m TransferInterface.sourceRequestAddress
  | _, .at ⟨4, _⟩ => .lit 0
  | _, .at ⟨5, _⟩ => controllerOutput m TransferInterface.sourceResponseReady
  | _, .at ⟨k+6, h⟩ => False.elim (by change k+6 < 6 at h; omega)

def destinationControllerInput (m : Hardware.Stream.Map wi wo) :
    {b : Nat} → StreamInterface.Input a wo b → Expr (Input a wi wo) (Register a wi wo) b
  | _, .at ⟨0, _⟩ => controllerOutput m TransferInterface.memoryReset
  | _, .at ⟨1, _⟩ => controllerOutput m TransferInterface.destinationRequestValid
  | _, .at ⟨2, _⟩ => .lit 1
  | _, .at ⟨3, _⟩ => controllerOutput m TransferInterface.destinationRequestAddress
  | _, .at ⟨4, _⟩ => controllerOutput m TransferInterface.destinationRequestData
  | _, .at ⟨5, _⟩ => .lit 1
  | _, .at ⟨k+6, h⟩ => False.elim (by change k+6 < 6 at h; omega)

def sourceInput (m : Hardware.Stream.Map wi wo) (p : StreamInterface.Input a wi b) :
    Expr (Input a wi wo) (Register a wi wo) b := .mux hostMode (sourceHostInput p) (sourceControllerInput m p)

def destinationInput (m : Hardware.Stream.Map wi wo) (p : StreamInterface.Input a wo b) :
    Expr (Input a wi wo) (Register a wi wo) b := .mux hostMode (destinationHostInput p) (destinationControllerInput m p)

def sourcePins (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo)) (s : Values (Register a wi wo)) :
    Values (StreamInterface.Input a wi) := fun p => (sourceInput m p).eval i s

def destinationPins (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi wo)) (s : Values (Register a wi wo)) :
    Values (StreamInterface.Input a wo) := fun p => (destinationInput m p).eval i s

def sourceHostOutput (p : StreamInterface.Output wi b) : Expr (Input a wi wo) (Register a wi wo) b :=
  ((StreamFlops.circuit a wi).output p).bind sourceHostInput (fun r => .reg (.right (.left r)))

def destinationHostOutput (p : StreamInterface.Output wo b) : Expr (Input a wi wo) (Register a wi wo) b :=
  ((StreamFlops.circuit a wo).output p).bind destinationHostInput (fun r => .reg (.right (.right r)))

def circuit (m : Hardware.Stream.Map wi wo) : Circuit (Input a wi wo) (Register a wi wo) (Output wi wo) where
  next := fun {b} r => match b, r with
    | _, .left r => ((TransferCircuit.circuit m).next r).bind controllerInput (fun r => .reg (.left r))
    | _, .right (.left r) => ((StreamFlops.circuit a wi).next r).bind (sourceInput m) (fun r => .reg (.right (.left r)))
    | _, .right (.right r) => ((StreamFlops.circuit a wo).next r).bind (destinationInput m) (fun r => .reg (.right (.right r)))
  output := fun o => match o with
    | .at ⟨0, _⟩ => canStart
    | .at ⟨1, _⟩ => controllerOutput m TransferInterface.busy
    | .at ⟨2, _⟩ => controllerOutput m TransferInterface.done
    | .at ⟨3, _⟩ => controllerOutput m TransferInterface.error
    | .at ⟨4, _⟩ => .mux (phase 0) (.band (.inv (.input startValid)) (sourceHostOutput StreamInterface.inReady)) (.lit 0)
    | .at ⟨5, _⟩ => .mux (phase 0) (sourceHostOutput StreamInterface.outValid) (.lit 0)
    | .at ⟨6, _⟩ => .mux (phase 0) (sourceHostOutput StreamInterface.outData) (.lit 0)
    | .at ⟨7, _⟩ => .mux (phase 0) (.band (.inv (.input startValid)) (destinationHostOutput StreamInterface.inReady)) (.lit 0)
    | .at ⟨8, _⟩ => .mux (phase 0) (destinationHostOutput StreamInterface.outValid) (.lit 0)
    | .at ⟨9, _⟩ => .mux (phase 0) (destinationHostOutput StreamInterface.outData) (.lit 0)
    | .at ⟨k+10, h⟩ => False.elim (by change k+10 < 10 at h; omega)

end Pinwheel.Hardware.Memory.TransferHostCircuit
