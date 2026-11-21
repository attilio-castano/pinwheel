import Pinwheel.Hardware.Memory.TransferInterface
import Pinwheel.Hardware.Memory.StreamFlops
import Std.Data.String.ToNat

/-! Seven-register open transfer controller. Length and completed index retain
the capacity bit; no response payload is stored here. Phase 3 suppresses all
transactions, resets the attached adapters through `memory_reset`, and recovers
to empty control with an error pulse. External reset takes priority.
-/
namespace Pinwheel.Hardware.Memory.TransferCircuit

open TransferInterface

inductive Register (a : Nat) : Nat → Type where
  | phase : Register a 2
  | sourceBase : Register a a
  | destinationBase : Register a a
  | length : Register a (a+1)
  | index : Register a (a+1)
  | done : Register a 1
  | error : Register a 1

def registerPosition : Register a b → Fin 7
  | .phase => 0
  | .sourceBase => 1
  | .destinationBase => 2
  | .length => 3
  | .index => 4
  | .done => 5
  | .error => 6

def registerSignal (a : Nat) : Fin 7 → Sigma (Register a)
  | ⟨0, _⟩ => ⟨2, .phase⟩
  | ⟨1, _⟩ => ⟨a, .sourceBase⟩
  | ⟨2, _⟩ => ⟨a, .destinationBase⟩
  | ⟨3, _⟩ => ⟨a+1, .length⟩
  | ⟨4, _⟩ => ⟨a+1, .index⟩
  | ⟨5, _⟩ => ⟨1, .done⟩
  | ⟨6, _⟩ => ⟨1, .error⟩
  | ⟨k+7, h⟩ => False.elim (by omega)

theorem register_signal_position (r : Register a b) : registerSignal a (registerPosition r) = ⟨b, r⟩ := by
  cases r <;> rfl

theorem register_position_signal (k : Fin 7) : registerPosition (registerSignal a k).2 = k := by
  match k with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ => rfl
  | ⟨k+7, h⟩ => omega

def registerName (k : Fin 7) : String :=
  #["phase", "source_base", "destination_base", "length", "index", "done", "error"][k]

def registers (a : Nat) : Interface (Register a) where
  size := 7
  signal := registerSignal a
  position := registerPosition
  signal_position := register_signal_position
  label := fun r => registerName (registerPosition r)
  unique := by
    intro i j h
    have unique : ∀ i j : Fin 7, registerName i = registerName j → i = j := by decide +kernel
    exact unique i j (by simpa only [register_position_signal] using h)

def phaseBits : TransferModel.Phase → BitVec 2
  | .idle => 0
  | .issueRead => 1
  | .transfer => 2

def encode (s : TransferModel.Control a) : Values (Register a)
  | _, .phase => phaseBits s.phase
  | _, .sourceBase => s.config.sourceBase
  | _, .destinationBase => s.config.destinationBase
  | _, .length => BitVec.ofNat (a+1) s.config.length
  | _, .index => BitVec.ofNat (a+1) s.index
  | _, .done => BitVec.ofBool s.done
  | _, .error => BitVec.ofBool s.error

def widen (e : Expr I R a) : Expr I R (a+1) :=
  cast (congrArg (Expr I R) (Nat.add_comm 1 a)) (.concat (.lit (0 : BitVec 1)) e)

def isPhase (value : BitVec 2) : Expr (Input a wi) (Register a) 1 :=
  .equal (.reg .phase) (.lit value)

def invalidPhase : Expr (Input a wi) (Register a) 1 := isPhase 3

def memoryResetExpr : Expr (Input a wi) (Register a) 1 := (Expr.input reset).bor invalidPhase

def remaining (base : Expr (Input a wi) (Register a) a) : Expr (Input a wi) (Register a) (a+1) :=
  .sub (.lit (BitVec.ofNat (a+1) (2^a))) (widen base)

def commandFits : Expr (Input a wi) (Register a) 1 :=
  .band (.inv (.ult (remaining (.input sourceBase)) (.input length)))
    (.inv (.ult (remaining (.input destinationBase)) (.input length)))

def start : Expr (Input a wi) (Register a) 1 := .band (isPhase 0) (.input startValid)
def zeroLength : Expr (Input a wi) (Register a) 1 := .equal (.input length) (.lit 0)
def fire : Expr (Input a wi) (Register a) 1 :=
  .band (.input sourceResponseValid) (.input destinationRequestReady)
def nextIndex : Expr (Input a wi) (Register a) (a+1) := (Expr.reg .index).plus (.lit 1)
def more : Expr (Input a wi) (Register a) 1 := .ult nextIndex (.reg .length)

def indexedAddress (base : Expr (Input a wi) (Register a) a) : Expr (Input a wi) (Register a) a :=
  .slice 0 a (by omega) ((widen base).plus (.reg .index))

def normalNext : {b : Nat} → Register a b → Expr (Input a wi) (Register a) b
  | _, .phase => .mux (isPhase 0)
      (.mux (.input startValid) (.mux commandFits (.mux zeroLength (.lit 0) (.lit 1)) (.lit 0)) (.lit 0))
      (.mux (isPhase 1) (.mux (.input sourceRequestReady) (.lit 2) (.lit 1))
        (.mux fire (.mux more (.lit 1) (.lit 0)) (.lit 2)))
  | _, .sourceBase => .mux start (.mux commandFits (.input sourceBase) (.lit 0)) (.reg .sourceBase)
  | _, .destinationBase => .mux start (.mux commandFits (.input destinationBase) (.lit 0)) (.reg .destinationBase)
  | _, .length => .mux start (.mux commandFits (.input length) (.lit 0)) (.reg .length)
  | _, .index => .mux start (.lit 0) (.mux (.band (isPhase 2) fire) nextIndex (.reg .index))
  | _, .done => .mux (isPhase 0) (.band (.input startValid) (.band commandFits zeroLength))
      (.band (isPhase 2) (.band fire (.inv more)))
  | _, .error => .band (isPhase 0) (.band (.input startValid) (.inv commandFits))

def recoveryValue : {b : Nat} → Register a b → BitVec b
  | _, .error => 1
  | _, _ => 0

def gated (e : Expr (Input a wi) (Register a) b) : Expr (Input a wi) (Register a) b :=
  .mux memoryResetExpr (.lit 0) e

def destinationValid : Expr (Input a wi) (Register a) 1 := .band (isPhase 2) (.input sourceResponseValid)

def circuit (m : Hardware.Stream.Map wi wo) : Circuit (Input a wi) (Register a) (Output a wo) where
  next := fun r => .mux (.input reset) (.lit 0) (.mux invalidPhase (.lit (recoveryValue r)) (normalNext r))
  output := fun o => match o with
    | .at ⟨0, _⟩ => gated (isPhase 0)
    | .at ⟨1, _⟩ => gated (.inv (isPhase 0))
    | .at ⟨2, _⟩ => gated (.reg .done)
    | .at ⟨3, _⟩ => gated (.reg .error)
    | .at ⟨4, _⟩ => gated (isPhase 1)
    | .at ⟨5, _⟩ => gated (.mux (isPhase 1) (indexedAddress (.reg .sourceBase)) (.lit 0))
    | .at ⟨6, _⟩ => gated (.band (isPhase 2) (.input destinationRequestReady))
    | .at ⟨7, _⟩ => gated destinationValid
    | .at ⟨8, _⟩ => gated (.mux destinationValid (indexedAddress (.reg .destinationBase)) (.lit 0))
    | .at ⟨9, _⟩ => gated (.mux destinationValid (m.apply (.input sourceResponseData)) (.lit 0))
    | .at ⟨10, _⟩ => memoryResetExpr
    | .at ⟨k+11, h⟩ => False.elim (by change k+11 < 11 at h; omega)

/-- Canonical bindings from controller outputs to the existing read/write
adapters. Source requests are reads; destination requests are writes. -/
def sourceMemoryPins (o : Values (Output a wo)) : Values (StreamInterface.Input a wi) :=
  StreamInterface.Pins.values ⟨o memoryReset, o sourceRequestValid, 0, o sourceRequestAddress, 0,
    o sourceResponseReady⟩

def destinationMemoryPins (o : Values (Output a wo)) : Values (StreamInterface.Input a wo) :=
  StreamInterface.Pins.values ⟨o memoryReset, o destinationRequestValid, 1,
    o destinationRequestAddress, o destinationRequestData, 1⟩

end Pinwheel.Hardware.Memory.TransferCircuit
