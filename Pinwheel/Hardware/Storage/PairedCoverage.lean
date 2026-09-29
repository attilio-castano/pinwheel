import Pinwheel.Hardware.Storage.PairedUpload

/-! Accepted-transcript coverage of the actual closed paired controller.
The ledger is ghost state: erasing it recovers the existing graph/SRAM model.
Initialization invalidates ownership, without clearing any physical contents. -/
namespace Pinwheel.Hardware.Storage.PairedCoverage
open Pinwheel.Hardware PairedController PairedUpload

structure Tracked where
  registers : Values Register
  memory : Memory.Sram.State 9 64
  ledger : PairedLoader.Ledger

def Tracked.physical (s : Tracked) : Values Register × Memory.Sram.State 9 64 :=
  (s.registers, s.memory)

def graphInputs (i : Values Loader.Machine.Input) (s : Tracked) : Values GraphInput :=
  PairedSemantics.inputs bindings (PairedClosed.feedback i s.memory.q) s.registers

theorem graph_equations (i : Values Loader.Machine.Input) (s : Tracked) :
    PairedSemantics.Equations bindings (graphInputs i s) s.registers :=
  PairedSemantics.inputs_equations bindings PairedSemantics.bindings_ordered
    (PairedClosed.feedback i s.memory.q) s.registers

def advance (s : Tracked) (i : Values Loader.Machine.Input) : Tracked :=
  let g : Values GraphInput := graphInputs i s
  ⟨body.step g s.registers, memoryNext g s.registers s.memory,
    PairedLoader.record (inputs g s.registers) (admitted g s.registers) (control s.registers) s.ledger⟩

def Invariant (s : Tracked) : Prop :=
  PairedLoader.Invariant (control s.registers) (banks s.registers s.memory) s.ledger

theorem physical_advance (s : Tracked) (i : Values Loader.Machine.Input) :
    (advance s i).physical = (PairedClosed.model PairedComposition.graph).step i s.physical := by
  rfl

theorem invariant_next (s : Tracked) (i : Values Loader.Machine.Input) (h : Invariant s) :
    Invariant (advance s i) := by
  change PairedLoader.Invariant (control (body.step (graphInputs i s) s.registers))
    (banks (body.step (graphInputs i s) s.registers) (memoryNext (graphInputs i s) s.registers s.memory))
    (PairedLoader.record (inputs (graphInputs i s) s.registers) (admitted (graphInputs i s) s.registers)
      (control s.registers) s.ledger)
  rw [control_next _ _ (graph_equations i s), banks_next _ _ _ (graph_equations i s)]
  exact PairedLoader.invariant_next _ _ _ _ _ h
  done

theorem input_init (i : Values Loader.Machine.Input) (s : Tracked) :
    (inputs (graphInputs i s) s.registers).init = (i .init == 1) := by
  simpa only [PairedUpload.inputs, graphInputs, PairedSemantics.inputs, PairedSemantics.graphValues,
    PairedClosed.feedback] using
    congrArg (fun v : BitVec 1 => v == 1) (init_value _ _ (graph_equations i s))

/-- The recorded word is the actual delivered data, not an unconstrained graph input. -/
theorem input_data (i : Values Loader.Machine.Input) (s : Tracked) :
    (inputs (graphInputs i s) s.registers).data = i .data := by
  simpa only [PairedUpload.inputs, graphInputs, PairedSemantics.inputs, PairedSemantics.graphValues,
    PairedClosed.feedback] using data_value _ _ (graph_equations i s)

theorem invariant_initialize (s : Tracked) (i : Values Loader.Machine.Input) (hi : i .init = 1) :
    Invariant (advance s i) := by
  change PairedLoader.Invariant (control (body.step (graphInputs i s) s.registers))
    (banks (body.step (graphInputs i s) s.registers) (memoryNext (graphInputs i s) s.registers s.memory))
    (PairedLoader.record (inputs (graphInputs i s) s.registers) (admitted (graphInputs i s) s.registers)
      (control s.registers) s.ledger)
  rw [control_next _ _ (graph_equations i s), banks_next _ _ _ (graph_equations i s)]
  exact PairedLoader.invariant_initialize _ _ _ _ _ (by simp only [input_init, hi, beq_self_eq_true])
  done

theorem invariant_run (history : List (Values Loader.Machine.Input)) (s : Tracked)
    (h : Invariant s) : Invariant (history.foldl advance s) := by
  induction history generalizing s with
  | nil => exact h
  | cons i rest ih => exact ih (advance s i) (invariant_next s i h)

/-- Erasing the ledger gives exactly the existing closed controller history. -/
theorem physical_run (history : List (Values Loader.Machine.Input)) (s : Tracked) :
    (history.foldl advance s).physical =
      history.foldl (fun t i => (PairedClosed.model PairedComposition.graph).step i t) s.physical := by
  induction history generalizing s with
  | nil => rfl
  | cons i rest ih => simpa only [List.foldl_cons, physical_advance] using ih (advance s i)

/-- All raw command histories after an initialization edge are covered, from
arbitrary register values, memory contents, Q and ghost ledger. -/
theorem initialized_run (history : List (Values Loader.Machine.Input)) (s : Tracked)
    (i : Values Loader.Machine.Input) (hi : i .init = 1) :
    Invariant (history.foldl advance (advance s i)) :=
  invariant_run history (advance s i) (invariant_initialize s i hi)

theorem active_complete (s : Tracked) (h : Invariant s) (hv : s.registers .valid = 1) :
    s.ledger.active.length = 290 ∧
      PairedLoader.Matches (banks s.registers s.memory (control s.registers).active) s.ledger.active :=
  h.active (by simp only [PairedUpload.control, hv, beq_self_eq_true])

/-- A certificate for the accepted transcript is now a certificate for the
complete image resident in the actual active storage bank. -/
theorem certified_image (s : Tracked) (h : Invariant s) (hv : s.registers .valid = 1)
    (p : Execution.Image) (image : PairedImage.Image)
    (hc : PairedImage.check p image s.ledger.active = true) :
    (banks s.registers s.memory (control s.registers).active : Values PairedLoader.Slot) =
        (PairedLoader.imageValues image : Values PairedLoader.Slot) ∧ PairedImage.Corresponds p image := by
  obtain ⟨hw, hp⟩ := PairedImage.check_sound p image s.ledger.active hc
  exact ⟨PairedLoader.image_agreement _ image (hw ▸ (active_complete s h hv).2), hp⟩
  done

theorem active_row (s : Tracked) (h : Invariant s) (hv : s.registers .valid = 1) (k : BitVec 8) :
    s.memory.contents (s.registers .active ++ k) = s.ledger.active.getD (32 + k.toNat) 0 := by
  simpa only [banks, Memory.Sram.bankAddress, PairedUpload.control, bit_value,
    PairedLoader.offset, BitVec.extractLsb'_eq_self] using
    (active_complete s h hv).2 (PairedLoader.Slot.row k)

/-- An enabled read returns the loaded row for the token installed on that
edge. Idle and write edges make no claim that Q changes or is usable. -/
theorem read_response (s : Tracked) (i : Values Loader.Machine.Input) (h : Invariant s)
    (hv : s.registers .valid = 1)
    (hr : (request .read).eval (graphInputs i s) s.registers = 1) :
    (advance s i).memory.q = s.ledger.active.getD
      (32 + (((advance s i).registers .current).extractLsb' 22 8).toNat) 0 := by
  have hw := PairedSemantics.request_exclusive (graphInputs i s) s.registers hr
  have hw' : writing.eval (graphInputs i s) s.registers = 0 := hw
  simp only [advance, memoryNext, PairedClosed.command, Circuit.observe, Circuit.step, body,
    PairedController.next, hw, hr, BitVec.reduceEq, Bool.false_eq_true, if_false, if_true, Memory.SinglePort.step,
    Memory.Sram.State.step]
  simpa only [request, row, Expr.eval, hw', BitVec.reduceEq, if_false] using
    active_row s h hv ((nextWord.eval (graphInputs i s) s.registers).extractLsb' 22 8)
  done

def view (memory : Memory.SinglePort.Contract S 9 64) (s : Values Register × S) :
    Values Register × Memory.Sram.State 9 64 := (s.1, memory.view s.2)

theorem view_step (memory : Memory.SinglePort.Contract S 9 64)
    (i : Values Loader.Machine.Input) (s : Values Register × S) :
    view memory ((PairedClosed.implementation PairedComposition.graph memory).step i s) =
      (PairedClosed.model PairedComposition.graph).step i (view memory s) := by
  exact Prod.ext rfl (memory.correct _ s.2)

theorem view_run (memory : Memory.SinglePort.Contract S 9 64)
    (history : List (Values Loader.Machine.Input)) (s : Values Register × S) :
    view memory (history.foldl
        (fun t i => (PairedClosed.implementation PairedComposition.graph memory).step i t) s) =
      history.foldl (fun t i => (PairedClosed.model PairedComposition.graph).step i t) (view memory s) := by
  induction history generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simpa only [List.foldl_cons, view_step] using
      ih ((PairedClosed.implementation PairedComposition.graph memory).step i s)

/-- The retained typed controller with any implementation of the stated SRAM
contract acquires the same upload invariant after initialization. This theorem
is at the decoded command boundary; host delivery and timed E64 execution are
separate obligations. No initial register, contents or Q value is assumed. -/
theorem retained_initialized_history
    (n : Netlist Register (SramController.Out Loader.Machine.Output) Input)
    (hn : PairedValidation.core = .ok n) (memory : Memory.SinglePort.Contract S 9 64)
    (registers : Values Register) (initial : S) (i : Values Loader.Machine.Input)
    (hi : i .init = 1) (history : List (Values Loader.Machine.Input)) :
    let actual := ((i : Values Loader.Machine.Input) :: history).foldl
      (fun t j => (PairedClosed.implementation n.component memory).step j t) (registers, initial)
    ∃ ledger, PairedLoader.Invariant (control actual.1) (banks actual.1 (memory.view actual.2)) ledger := by
  rw [PairedComposition.retained_correct n hn]
  let t : Tracked := ⟨registers, memory.view initial, {}⟩
  have he := (physical_run ((i : Values Loader.Machine.Input) :: history) t).trans
    (view_run memory ((i : Values Loader.Machine.Input) :: history) (registers, initial)).symm
  refine ⟨(history.foldl advance (advance t i)).ledger, ?_⟩
  exact Eq.mp (congrArg (fun p : Values Register × Memory.Sram.State 9 64 =>
    PairedLoader.Invariant (control p.1) (banks p.1 p.2)
      (history.foldl advance (advance t i)).ledger) he) (initialized_run history t i hi)
  done

end Pinwheel.Hardware.Storage.PairedCoverage
