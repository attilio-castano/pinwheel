import Pinwheel.Hardware.Memory.CommandInterface
import Pinwheel.Hardware.Memory.Flops
import Pinwheel.Hardware.Stream.Compose

/-! A structural implementation of the exclusive single-port command contract.
Word updates reuse the existing decoded flip-flop memory. The Q register loads
only on an enabled read and holds during writes and idle cycles. Array contents
and Q are arbitrary until established by commands; no reset is invented.
-/
namespace Pinwheel.Hardware.Memory.CommandFlops

open CommandInterface

abbrev Register (a w : Nat) := Stream.Joint (Flops.Register a w) (Output w)

def word (address : BitVec a) : Register a w w := .left (.word address)
def q : Register a w w := .right .q

def wordPosition : Flops.Register a w b → Fin (2^a)
  | .word address => address.toFin

def wordSignal (a w : Nat) (k : Fin (2^a)) : Sigma (Flops.Register a w) :=
  ⟨w, .word (BitVec.ofFin k)⟩

theorem word_signal_position (r : Flops.Register a w b) : wordSignal a w (wordPosition r) = ⟨b, r⟩ := by
  cases r <;> rfl

theorem word_position_signal (k : Fin (2^a)) : wordPosition (wordSignal a w k).2 = k := rfl

def wordInterface (a w : Nat) : Interface (Flops.Register a w) where
  size := 2^a
  signal := wordSignal a w
  position := wordPosition
  signal_position := word_signal_position
  label := fun r => "word_" ++ Nat.repr (wordPosition r).val
  unique := by
    intro a b h
    simpa only [word_position_signal, String.append_right_inj, Nat.repr_inj, Fin.val_inj] using h

/-- Every word in ascending address order, followed by Q. -/
def registers (a w : Nat) : Interface (Register a w) :=
  Stream.Joint.interface (wordInterface a w) (outputs w)

def view (s : Values (Register a w)) : Sram.State a w :=
  ⟨fun address => s (word address), s q⟩

def encode (s : Sram.State a w) : Values (Register a w)
  | _, .left (.word address) => s.contents address
  | _, .right .q => s.q

def writeInput : {b : Nat} → Flops.Input a w 0 b → Expr (Input a w) (Register a w) b
  | _, .enable => .band (.input .enable) (.input .write)
  | _, .address => .input .address
  | _, .data => .input .data
  | _, .read port => port.elim0

def readEnable : Expr (Input a w) (Register a w) 1 :=
  .band (.input .enable) (.inv (.input .write))

def readData : Expr (Input a w) (Register a w) w :=
  Execution.readTree a (fun address => .reg (word address)) (.input .address)

def circuit (a w : Nat) : Circuit (Input a w) (Register a w) (Output w) where
  next := fun {b} r => match b, r with
    | _, .left r => ((Flops.circuit a w 0).next r).bind writeInput (fun r => .reg (.left r))
    | _, .right .q => .mux readEnable readData (.reg q)
  output := fun {b} p => match b, p with
    | _, .q => .reg q

end Pinwheel.Hardware.Memory.CommandFlops
