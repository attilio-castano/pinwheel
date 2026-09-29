import Pinwheel.Hardware.Memory.Sram

/-! Restricted single-port SRAM contract with an explicit idle mode. The macro
has arbitrary power-up contents and Q; a write holds Q, an enabled read updates
Q on the edge, and idle holds both. Simultaneous read/write is outside this
contract. Physical qualification is an external obligation, not a Lean axiom. -/
namespace Pinwheel.Hardware.Memory.SinglePort

inductive Command (a w : Nat) where
  | idle
  | read (address : BitVec a)
  | write (address : BitVec a) (data : BitVec w)

def step (s : Sram.State a w) : Command a w → Sram.State a w
  | .idle => s
  | .read address => s.step ⟨false, address, 0⟩ address
  | .write address data => s.step ⟨true, address, data⟩ address

/-- A caller supplies this law for its exact memory implementation. The view
includes all contents and Q; no initial state restriction is imposed. -/
structure Contract (S : Type) (a w : Nat) where
  view : S → Sram.State a w
  advance : Command a w → S → S
  correct : ∀ command s, view (advance command s) = step (view s) command

def modelStep (s : Sram.Model a w 1) : Command a w → Sram.Model a w 1
  | .idle => s
  | .read address => s.step ⟨⟨false, address, 0⟩, fun _ => address⟩
  | .write address data => s.step ⟨⟨true, address, data⟩, fun _ => address⟩

abbrev Related (s : Sram.State a w) (model : Sram.Model a w 1) : Prop :=
  Sram.Related (fun _ => s) model

theorem related_step (s : Sram.State a w) (model : Sram.Model a w 1)
    (h : Related s model) (command : Command a w) : Related (step s command) (modelStep model command) := by
  cases command with
  | idle => exact h
  | read address => exact Sram.related_step ⟨⟨false, address, 0⟩, fun _ => address⟩ (fun _ => s) model h
  | write address data => exact Sram.related_step ⟨⟨true, address, data⟩, fun _ => address⟩ (fun _ => s) model h

theorem related_initial (s : Sram.State a w) : Related s Sram.Model.initial :=
  Sram.related_initial (fun _ => s)

theorem write_initializes (s : Sram.Model a w 1) (address : BitVec a) (data : BitVec w) :
    (modelStep s (.write address data)).Defined address :=
  Sram.Model.write_defined s ⟨⟨true, address, data⟩, fun _ => address⟩ rfl

/-- Only a previously defined word yields a promised response. This theorem
does not assume that the controller has established that coverage. -/
theorem initialized_read (s : Sram.State a w) (model : Sram.Model a w 1)
    (h : Related s model) (address : BitVec a) (v : BitVec w)
    (hv : model.contents address = some v) : (step s (.read address)).q = v :=
  Sram.read_defined ⟨⟨false, address, 0⟩, fun _ => address⟩ (fun _ => s) model h rfl 0 v hv

theorem idle_holds (s : Sram.State a w) : step s .idle = s := rfl
theorem write_holds_q (s : Sram.State a w) (address : BitVec a) (data : BitVec w) :
    (step s (.write address data)).q = s.q := rfl

theorem related_run (commands : List (Command a w)) (s : Sram.State a w)
    (model : Sram.Model a w 1) (h : Related s model) :
    Related (commands.foldl step s) (commands.foldl modelStep model) := by
  induction commands generalizing s model with
  | nil => exact h
  | cons command rest ih => exact ih _ _ (related_step s model h command)

end Pinwheel.Hardware.Memory.SinglePort
