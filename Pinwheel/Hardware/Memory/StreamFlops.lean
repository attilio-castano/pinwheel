import Pinwheel.Hardware.Memory.StreamInterface
import Pinwheel.Hardware.Memory.CommandFlops

/-! Structural stream adapter: the existing command memory plus one pending
bit. Q itself holds the response, so an accepted read has one-edge latency
without a second data register. Reset never changes any memory register.
-/
namespace Pinwheel.Hardware.Memory.StreamFlops

open StreamInterface

inductive Pending : Nat → Type where
  | valid : Pending 1

def pendingInterface : Interface Pending where
  size := 1
  signal := fun _ => ⟨1, .valid⟩
  position := fun _ => 0
  signal_position := by intro b p; cases p; rfl
  label := fun _ => "pending"
  unique := by intro a b _; exact Subsingleton.elim a b

abbrev Register (a w : Nat) := Hardware.Stream.Joint (CommandFlops.Register a w) Pending

def pending : Register a w 1 := .right .valid

/-- Command memory words and Q, followed by exactly one pending bit. -/
def registers (a w : Nat) : Interface (Register a w) :=
  Hardware.Stream.Joint.interface (CommandFlops.registers a w) pendingInterface

theorem register_count (a w : Nat) : (registers a w).size = 2^a + 2 := rfl

def memoryValues (s : Values (Register a w)) : Values (CommandFlops.Register a w) :=
  fun r => s (.left r)

def view (s : Values (Register a w)) : StreamModel.State a w :=
  ⟨CommandFlops.view (memoryValues s), s pending == 1⟩

def encode (s : StreamModel.State a w) : Values (Register a w)
  | _, .left r => CommandFlops.encode s.memory r
  | _, .right .valid => BitVec.ofBool s.pending

def canLoad : Expr (Input a w) (Register a w) 1 :=
  (Expr.inv (.reg pending)).bor (.input ready)

def accept : Expr (Input a w) (Register a w) 1 :=
  .band (.inv (.input reset)) (.band (.input valid) canLoad)

def memoryInput : {b : Nat} → CommandInterface.Input a w b → Expr (Input a w) (Register a w) b
  | _, .enable => accept
  | _, .write => .input write
  | _, .address => .input address
  | _, .data => .input data

def memoryPins (i : Values (Input a w)) (s : Values (Register a w)) :
    Values (CommandInterface.Input a w) :=
  fun p => (memoryInput p).eval i s

def responseValid : Expr (Input a w) (Register a w) 1 :=
  .band (.inv (.input reset)) (.reg pending)

def circuit (a w : Nat) : Circuit (Input a w) (Register a w) (Output w) where
  next := fun {b} r => match b, r with
    | _, .left r => ((CommandFlops.circuit a w).next r).bind memoryInput (fun p => .reg (.left p))
    | _, .right .valid => .mux (.input reset) (.lit 0)
        (.mux canLoad (.band (.input valid) (.inv (.input write))) (.reg pending))
  output := fun o => match o with
    | .at ⟨0, _⟩ => .band (.inv (.input reset)) canLoad
    | .at ⟨1, _⟩ => responseValid
    | .at ⟨2, _⟩ => .mux responseValid (.reg (.left CommandFlops.q)) (.lit 0)
    | .at ⟨k+3, h⟩ => False.elim (by change k+3 < 3 at h; omega)

end Pinwheel.Hardware.Memory.StreamFlops
