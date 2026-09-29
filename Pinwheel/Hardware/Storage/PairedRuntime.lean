import Pinwheel.Hardware.Storage.PairedRunning

/-! Initialized running histories and their connection to a certified image.
The actual memory response feeds the graph. This establishes instruction,
parameter and response ownership; exact E64 capture/dispatch timing is separate. -/
namespace Pinwheel.Hardware.Storage.PairedRuntime
open Pinwheel.Hardware PairedController PairedUpload PairedRunning
open PairedCoverage (Tracked graphInputs advance)

def Invariant (s : Tracked) : Prop :=
  PairedCoverage.Invariant s ∧ Ready s.registers s.memory

theorem invariant_next (s : Tracked) (i : Values Loader.Machine.Input) (h : Invariant s) :
    Invariant (advance s i) := by
  exact ⟨PairedCoverage.invariant_next s i h.1,
    ready_next (graphInputs i s) s.registers s.memory (PairedCoverage.graph_equations i s) rfl h.2⟩

theorem invariant_initialize (s : Tracked) (i : Values Loader.Machine.Input) (hi : i .init = 1) :
    Invariant (advance s i) := by
  refine ⟨PairedCoverage.invariant_initialize s i hi,
    ready_initialize (graphInputs i s) s.registers s.memory (PairedCoverage.graph_equations i s) ?_⟩
  exact (init_value (graphInputs i s) s.registers (PairedCoverage.graph_equations i s)).trans hi
  done

theorem invariant_run (history : List (Values Loader.Machine.Input)) (s : Tracked)
    (h : Invariant s) : Invariant (history.foldl advance s) := by
  induction history generalizing s with
  | nil => exact h
  | cons i rest ih => exact ih (advance s i) (invariant_next s i h)

/-- Every initialized command history preserves upload coverage and running
instruction/parameter/response ownership, with arbitrary power-up state. -/
theorem initialized_run (history : List (Values Loader.Machine.Input)) (s : Tracked)
    (i : Values Loader.Machine.Input) (hi : i .init = 1) :
    Invariant (history.foldl advance (advance s i)) :=
  invariant_run history (advance s i) (invariant_initialize s i hi)

/-- Transfer to the actual retained controller, with the memory behavior law
supplied explicitly. No graph-wire or initial-memory premise is left free. -/
theorem retained_initialized_history
    (n : Netlist Register (SramController.Out Loader.Machine.Output) Input)
    (hn : PairedValidation.core = .ok n) (memory : Memory.SinglePort.Contract S 9 64)
    (registers : Values Register) (initial : S) (i : Values Loader.Machine.Input)
    (hi : i .init = 1) (history : List (Values Loader.Machine.Input)) :
    let actual := ((i : Values Loader.Machine.Input) :: history).foldl
      (fun t j => (PairedClosed.implementation n.component memory).step j t) (registers, initial)
    ∃ ledger, Invariant ⟨actual.1, memory.view actual.2, ledger⟩ := by
  rw [PairedComposition.retained_correct n hn]
  let t : Tracked := ⟨registers, memory.view initial, {}⟩
  have he := (PairedCoverage.physical_run ((i : Values Loader.Machine.Input) :: history) t).trans
    (PairedCoverage.view_run memory ((i : Values Loader.Machine.Input) :: history) (registers, initial)).symm
  refine ⟨(history.foldl advance (advance t i)).ledger, ?_⟩
  exact Eq.mp (congrArg (fun p : Values Register × Memory.Sram.State 9 64 =>
    Invariant ⟨p.1, p.2, (history.foldl advance (advance t i)).ledger⟩) he)
    (initialized_run history t i hi)
  done

/-- The current parameter and response come from the certified image; the
current token is its boot token or one of its stored successor tokens. -/
theorem certified_values (s : Tracked) (h : Invariant s) (hb : Running s.registers)
    (p : Execution.Image) (image : PairedImage.Image)
    (hc : PairedImage.check p image s.ledger.active = true) :
    s.registers .cached = image.parameters[(PairedImage.index (s.registers .current)).toNat] ∧
    s.memory.q = image.rows[(PairedImage.row (s.registers .current)).toNat] ∧
    (s.registers .current = image.boot ∨
      ∃ (row : BitVec 8) (choice : Bool),
        s.registers .current = PairedImage.select image.rows[row.toNat] choice) := by
  have ha := (PairedCoverage.certified_image s h.1 (h.2 hb).1 p image hc).1
  have rows (row : BitVec 8) : s.memory.contents (s.registers .active ++ row) = image.rows[row.toNat] := by
    simpa only [banks, PairedUpload.control, Memory.Sram.bankAddress, bit_value,
      PairedLoader.imageValues] using
      congrArg (fun bank : Values PairedLoader.Slot => bank (.row row)) ha
  refine ⟨(h.2 hb).2.1.trans ?_, (h.2 hb).2.2.1.trans ?_, ?_⟩
  case refine_3 =>
    rcases (h.2 hb).2.2.2.2 with hw | ⟨row, choice, hw⟩
    case inr => exact Or.inr ⟨row, choice,
      hw.trans (congrArg (fun pair => PairedImage.select pair choice) (rows row))⟩
    exact Or.inl (hw.trans (congrArg (fun bank : Values PairedLoader.Slot => bank .boot) ha))
  case refine_1 => exact congrArg (fun bank : Values PairedLoader.Slot =>
    bank (.parameter (PairedImage.index (s.registers .current)))) ha
  exact rows (PairedImage.row (s.registers .current))
  done

private theorem matches_row (p : Execution.Image) (image : PairedImage.Image)
    (node : PairedImage.Node) (word : BitVec 32) (h : PairedImage.Matches p image node word)
    (ht : PairedImage.terminal word = false) :
    PairedImage.Matches p image (some (PairedImage.row word)) word := by
  cases node with
  | none => simp_all [PairedImage.terminal]
  | some pc =>
    by_cases hk : (PairedImage.fields p pc).kind = 4
    · simp_all [PairedImage.Matches, PairedImage.terminal]
    · simp only [PairedImage.Matches, hk, if_false] at h
      simpa only [h.2.2.1, PairedImage.Matches, hk, if_false] using h
      done

/-- While running, the current token denotes the actual source instruction
at its row address, including its canonical fields and parameter value. -/
theorem certified_current (s : Tracked) (h : Invariant s) (hb : Running s.registers)
    (p : Execution.Image) (image : PairedImage.Image)
    (hc : PairedImage.check p image s.ledger.active = true) :
    PairedImage.Matches p image (some (PairedImage.row (s.registers .current))) (s.registers .current) := by
  have cert := (PairedImage.check_sound p image s.ledger.active hc).2
  rcases (certified_values s h hb p image hc).2.2 with hw | ⟨row, choice, hw⟩
  case inr =>
    have hm := cert.2.2 row choice
    split at hm
    next => exact matches_row p image _ _ (hw.symm ▸ hm) (h.2 hb).2.2.2.1
    next => exact False.elim (by simpa [hw, hm, PairedImage.terminal] using (h.2 hb).2.2.2.1)
  exact matches_row p image _ _ (hw.symm ▸ cert.1) (h.2 hb).2.2.2.1
  done

/-- On an actual entry edge from a running state, the new token is the
certified image's successor for the actual branch wire. This does not yet prove
that the edge or branch bit agrees with the timed E64 reference. -/
theorem dispatch_token (s : Tracked) (i : Values Loader.Machine.Input)
    (h : Invariant s) (hb : Running s.registers) (p : Execution.Image) (image : PairedImage.Image)
    (hc : PairedImage.check p image s.ledger.active = true)
    (he : entering.eval (graphInputs i s) s.registers = 1) :
    (advance s i).registers .current =
      PairedImage.step image (s.registers .current) (branch.eval (graphInputs i s) s.registers == 1) := by
  refine (dispatch_current (graphInputs i s) s.registers (PairedCoverage.graph_equations i s) hb he).trans ?_
  simpa only [PairedImage.step, (h.2 hb).2.2.2.1, Bool.false_eq_true, if_false,
    (show graphInputs i s (.q false) = s.memory.q from rfl)] using
    congrArg (fun pair => PairedImage.select pair (branch.eval (graphInputs i s) s.registers == 1))
      (certified_values s h hb p image hc).2.1
  done

theorem dispatch_matches (s : Tracked) (i : Values Loader.Machine.Input)
    (h : Invariant s) (hb : Running s.registers) (p : Execution.Image) (image : PairedImage.Image)
    (hc : PairedImage.check p image s.ledger.active = true)
    (he : entering.eval (graphInputs i s) s.registers = 1) :
    PairedImage.Matches p image
      (PairedImage.referenceStep p (some (PairedImage.row (s.registers .current)))
        (branch.eval (graphInputs i s) s.registers == 1))
      ((advance s i).registers .current) := by
  exact (dispatch_token s i h hb p image hc he).symm ▸
    PairedImage.step_matches p image _ _ _ (PairedImage.check_sound p image s.ledger.active hc).2
      (certified_current s h hb p image hc)

end Pinwheel.Hardware.Storage.PairedRuntime
