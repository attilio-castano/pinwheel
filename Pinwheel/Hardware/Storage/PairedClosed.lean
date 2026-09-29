import Pinwheel.Hardware.Storage.PairedComposition
import Pinwheel.Hardware.Memory.SinglePort

/-! Conditional package traces with the single SRAM fed back into the exact
controller. A contract is supplied as a parameter, never as a global axiom.
This interprets the paired graph; correspondence to E64 timed execution and
loader-established read coverage are separate obligations. -/
namespace Pinwheel.Hardware.Storage.PairedClosed
open PairedComposition
open SramController (Reads Out)

def feedback (i : Values I) (q : BitVec 64) : Values (Reads I)
  | _, .base p => i p
  | _, .q _ => q

def command (o : Values (Out O)) : Memory.SinglePort.Command 9 64 :=
  if o (.port .write) = 1 then .write (o (.port (.address false))) (o (.port .data))
  else if o (.port .read) = 1 then .read (o (.port (.address false))) else .idle

def Exclusive (c : Component (Reads I) R (Out O)) : Prop :=
  ∀ i s, c.observe i s (.port .read) = 1 → c.observe i s (.port .write) = 0

def enables : Memory.SinglePort.Command a w → BitVec 1 × BitVec 1
  | .idle => (0, 0)
  | .read _ => (0, 1)
  | .write _ _ => (1, 0)

/-- Selecting a contract command preserves both actual enable pins. In
particular, the write-first case in `command` cannot conceal an illegal mode. -/
theorem command_enables (o : Values (Out O))
    (h : o (.port .read) = 1 → o (.port .write) = 0) :
    enables (command o) = (o (.port .write), o (.port .read)) := by
  by_cases hw : o (.port .write) = 1 <;> by_cases hr : o (.port .read) = 1 <;>
    simp_all [command, enables] <;> bv_omega

theorem fed_exclusive (f : Feeder (Reads J) X (Reads I)) (c : Component (Reads I) R (Out O))
    (h : Exclusive c) : Exclusive (fed f c) :=
  fun i s => h (f.feed i (Extended.extraValues s)) (Extended.innerValues s)

theorem observed_exclusive (c : Component (Reads Chip.Pin) R (Out Loader.Machine.Output))
    (h : Exclusive c) : Exclusive (observed SramAssembly.observer c) :=
  fun i s => h i (Extended.innerValues s)

theorem graph_exclusive : Exclusive graph :=
  fun i s => PairedSemantics.request_exclusive (PairedSemantics.inputs PairedController.bindings i s) s

theorem packaged_exclusive : Exclusive (packaged graph) :=
  observed_exclusive _ (fed_exclusive _ _ (fed_exclusive _ _ (fed_exclusive _ _ graph_exclusive)))

theorem retained_package_exclusive
    (n : Netlist PairedController.Register (Out Loader.Machine.Output) PairedController.Input)
    (h : PairedValidation.core = .ok n) : Exclusive (package n).component := by
  rw [retained_package_correct n h]
  exact packaged_exclusive

/-- Registers and memory advance from the same pre-edge snapshot. Post-edge
observation uses the updated Q and updated package registers. -/
def closed (c : Component (Reads I) R (Out O))
    (advance : Memory.SinglePort.Command 9 64 → S → S) (q : S → BitVec 64) :
    Timed.Component (Values I) (Values R × S) (Values O) where
  step := fun i s =>
    let j : Values (Reads I) := feedback i (q s.2)
    (c.step j s.1, advance (command (c.observe j s.1)) s.2)
  observe := fun i s {_} o => c.observe (feedback i (q s.2)) s.1 (.base o)

def implementation (c : Component (Reads I) R (Out O)) (memory : Memory.SinglePort.Contract S 9 64) :=
  closed c memory.advance (fun s => (memory.view s).q)

def model (c : Component (Reads I) R (Out O)) :=
  closed c (fun request s => Memory.SinglePort.step s request) Memory.Sram.State.q

def contract_refinement (c : Component (Reads I) R (Out O)) (memory : Memory.SinglePort.Contract S 9 64) :
    Timed.Refinement (implementation c memory) (model c) where
  Rel := fun s t => (s.1 : Values R) = (t.1 : Values R) ∧ memory.view s.2 = t.2
  step := by
    rintro i ⟨rs, ms⟩ ⟨rt, mt⟩ ⟨hc, hm⟩
    change @rs = @rt at hc
    subst rt
    change memory.view ms = mt at hm
    subst mt
    exact ⟨rfl, memory.correct _ ms⟩
  observe := fun i s t h => congrArg ((model c).observe i)
    (show ((s.1 : Values R), memory.view s.2) = t from Prod.ext h.1 h.2)

/-- Equality before and after every edge for arbitrary package histories,
including reset, incomplete uploads and rejected commands. SRAM contents and Q
start at the caller's arbitrary state. This is graph interpretation, not yet
the E64 program-execution refinement. -/
theorem retained_package_trace
    (n : Netlist PairedController.Register (Out Loader.Machine.Output) PairedController.Input)
    (h : PairedValidation.core = .ok n) (memory : Memory.SinglePort.Contract S 9 64)
    (registers : Values PairedController.FullRegister) (initial : S) (history : List (Values Chip.Pin)) :
    (implementation (package n).component memory).trace (registers, initial) history =
      (model (packaged graph)).trace (registers, memory.view initial) history := by
  rw [retained_package_correct n h]
  exact (contract_refinement (packaged graph) memory).trace_eq _ _ ⟨rfl, rfl⟩ history

/-- Every controller write targets the other bank. This protects all words of
the previously active image, even across partial or interrupted uploads. -/
theorem active_words_preserved (i : Values Loader.Machine.Input)
    (registers : Values PairedController.Register) (memory : Memory.Sram.State 9 64) (row : BitVec 8) :
    ((model graph).step i (registers, memory)).2.contents (registers .active ++ row) =
      memory.contents (registers .active ++ row) := by
  change (Memory.SinglePort.step memory (command (graph.observe (feedback i memory.q) registers))).contents
    (registers .active ++ row) = memory.contents (registers .active ++ row)
  by_cases hw : graph.observe (feedback i memory.q) registers (.port .write) = 1
  · have hb := PairedSemantics.write_address_bank (feedback i memory.q) registers hw
    change (graph.observe (feedback i memory.q) registers (.port (.address false))).extractLsb' 8 1 =
      ~~~registers .active at hb
    have hn : graph.observe (feedback i memory.q) registers (.port (.address false)) ≠
        registers .active ++ row := by
      intro he
      rw [he, BitVec.extractLsb'_append_eq_left] at hb
      bv_omega
    simp only [command, hw, if_true, Memory.SinglePort.step, Memory.Sram.State.step]
    exact Memory.write_other _ _ _ hn
  · simp only [command, hw, if_false]
    split <;> simp [Memory.SinglePort.step, Memory.Sram.State.step]

end Pinwheel.Hardware.Storage.PairedClosed
