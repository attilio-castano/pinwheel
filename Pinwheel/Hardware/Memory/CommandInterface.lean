import Pinwheel.Hardware.Memory.SinglePort
import Pinwheel.Hardware.Interface
import Std.Data.String.ToNat

/-! Physical single-port command interface. Disabled is idle; an enabled edge
is either a read or a full-word write. There is no reset, response-valid bit,
or initialization promise. Every a-bit address names one of 2^a words.
The semantics include zero widths; HDL exporters may require positive widths.
-/
namespace Pinwheel.Hardware.Memory.CommandInterface

inductive Input (a w : Nat) : Nat → Type where
  | enable : Input a w 1
  | write : Input a w 1
  | address : Input a w a
  | data : Input a w w

inductive Output (w : Nat) : Nat → Type where
  | q : Output w w

def inputPosition : Input a w b → Fin 4
  | .enable => 0
  | .write => 1
  | .address => 2
  | .data => 3

def inputSignal (a w : Nat) : Fin 4 → Sigma (Input a w)
  | ⟨0, _⟩ => ⟨1, .enable⟩
  | ⟨1, _⟩ => ⟨1, .write⟩
  | ⟨2, _⟩ => ⟨a, .address⟩
  | ⟨3, _⟩ => ⟨w, .data⟩
  | ⟨k+4, h⟩ => False.elim (by omega)

theorem input_signal_position (p : Input a w b) : inputSignal a w (inputPosition p) = ⟨b, p⟩ := by
  cases p <;> rfl

theorem input_position_signal (k : Fin 4) : inputPosition (inputSignal a w k).2 = k := by
  match k with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl
  | ⟨k+4, h⟩ => omega

def inputs (a w : Nat) : Interface (Input a w) where
  size := 4
  signal := inputSignal a w
  position := inputPosition
  signal_position := input_signal_position
  label := fun p => "mem_in_" ++ Nat.repr (inputPosition p).val
  unique := by
    intro a b h
    simpa only [input_position_signal, String.append_right_inj, Nat.repr_inj, Fin.val_inj] using h

def outputs (w : Nat) : Interface (Output w) where
  size := 1
  signal := fun _ => ⟨w, .q⟩
  position := fun _ => 0
  signal_position := by intro b p; cases p; rfl
  label := fun _ => "q"
  unique := by intro a b _; exact Subsingleton.elim a b

/-- The write mode is ignored while enable is low. -/
def decode (i : Values (Input a w)) : SinglePort.Command a w :=
  if i .enable = 1 then
    if i .write = 1 then .write (i .address) (i .data) else .read (i .address)
  else .idle

def encode : SinglePort.Command a w → Values (Input a w)
  | .idle => fun p => match p with
    | .enable | .write => 0
    | .address | .data => 0
  | .read address => fun p => match p with
    | .enable => 1
    | .write => 0
    | .address => address
    | .data => 0
  | .write address data => fun p => match p with
    | .enable | .write => 1
    | .address => address
    | .data => data

theorem decode_encode (command : SinglePort.Command a w) : decode (encode command) = command := by
  cases command <;> simp [decode, encode]

def outputValues (s : Sram.State a w) : Values (Output w)
  | _, .q => s.q

def spec (a w : Nat) : Timed.Component (Values (Input a w)) (Sram.State a w) (Values (Output w)) where
  step := fun i s => SinglePort.step s (decode i)
  observe := fun _ s => outputValues s

end Pinwheel.Hardware.Memory.CommandInterface
