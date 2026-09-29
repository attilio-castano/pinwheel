import Pinwheel.Hardware.Storage.PairedReference

/-! A certified active program, connected to the actual closed graph. -/
namespace Pinwheel.Hardware.Storage.PairedCertified
open Pinwheel.Hardware PairedController PairedRunning PairedBits PairedControl PairedE64
open PairedCoverage (Tracked graphInputs advance graph_equations)
set_option backward.isDefEq.respectTransparency false

structure Context (p : Execution.Image) (image : PairedImage.Image) (s : Tracked) : Prop where
  invariant : PairedRuntime.Invariant s
  valid : s.registers .valid = 1
  certificate : PairedImage.check p image s.ledger.active = true

/-- Execution of one resident program: initialization and replacement commit
begin a new certified segment. All other commands and pin samples are allowed. -/
def Rule (i : Values Loader.Machine.Input) : Prop := i .init = 0 ∧ i .command ≠ 3

theorem init_zero (s : Tracked) (i : Values Loader.Machine.Input) (hi : Rule i) :
    init.eval (graphInputs i s) s.registers = 0 :=
  (PairedUpload.init_value _ _ (graph_equations i s)).trans hi.1

theorem commit_zero (s : Tracked) (i : Values Loader.Machine.Input) (hi : Rule i) :
    commit.eval (graphInputs i s) s.registers = 0 := by
  simp only [PairedUpload.commit_value _ _ (graph_equations i s), PairedLoader.commit,
    PairedUpload.inputs, show graphInputs i s (.base .command) = i .command from rfl,
    Bool.beq_eq_decide_eq, hi.2, decide_false, Bool.and_false, Bool.false_and, BitVec.ofBool_false]

theorem context_next (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (i : Values Loader.Machine.Input) (h : Context p image s) (hi : Rule i) :
    Context p image (advance s i) := by
  refine ⟨PairedRuntime.invariant_next s i h.invariant, ?_, ?_⟩
  case refine_1 =>
    simp [advance, Circuit.step, body, PairedController.next, init_zero s i hi,
      commit_zero s i hi, h.valid, Expr.eval, either]
  simp only [advance, PairedLoader.record, PairedLoader.commit, PairedUpload.inputs,
    init_zero s i hi, show graphInputs i s (.base .command) = i .command from rfl,
    hi.2, Bool.beq_eq_decide_eq, decide_false, Bool.and_false, Bool.false_and,
    BitVec.reduceEq, Bool.false_eq_true, if_false]
  repeat first | exact h.certificate | split
  done

theorem idle_value (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (i : Values Loader.Machine.Input) (h : Context p image s) (hi : Rule i) :
    idleWord.eval (graphInputs i s) s.registers = p.idle.enabled ++ p.idle.levels := by
  have ha := PairedCoverage.certified_image s h.invariant.1 h.valid p image h.certificate
  have hs := congrArg (fun b : Values PairedLoader.Slot => b .idle) ha.1
  simp only [idleWord_wire _ _ (graph_equations i s), idleWordExpr,
    selected_wire _ _ (graph_equations i s), selectedExpr, both, either, Expr.eval,
    init_zero s i hi, commit_zero s i hi, h.valid]
  rcases PairedUpload.bit_cases (s.registers .active) with hb | hb <;>
    simpa [PairedUpload.banks, PairedUpload.control, PairedLoader.imageValues, hb] using hs.trans ha.2.2.1
  done

theorem entry_parameter_value (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (i : Values Loader.Machine.Input) (h : Context p image s)
    (he : entering.eval (graphInputs i s) s.registers = 1) :
    parameter0.eval (graphInputs i s) s.registers =
      image.parameters[(PairedImage.index (entered.eval (graphInputs i s) s.registers)).toNat] := by
  have source := (entering_source _ _ (graph_equations i s) he).2
  have hv := (no_upload _ _ (graph_equations i s) (source.elim
    (fun hs => Or.inr ((start_conditions _ _ (graph_equations i s)).mp hs).2.1) Or.inl)).1
  exact (entry_parameter _ _ (graph_equations i s) hv).trans
    (congrArg (fun b : Values PairedLoader.Slot =>
      b (.parameter (PairedImage.index (entered.eval (graphInputs i s) s.registers))))
      (PairedCoverage.certified_image s h.invariant.1 h.valid p image h.certificate).1)
  done

theorem install (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (i : Values Loader.Machine.Input) (h : Context p image s) (hi : Rule i)
    (hr : resetting.eval (graphInputs i s) s.registers = 0)
    (hd : ending.eval (graphInputs i s) s.registers = 0)
    (he : entering.eval (graphInputs i s) s.registers = 1)
    (node : PairedImage.Node)
    (hm : PairedImage.Matches p image node (entered.eval (graphInputs i s) s.registers)) :
    PairedEntry.view (advance s i).registers = Reactive.embed
      (enterNode p node (samples (entrySamples.eval (graphInputs i s) s.registers)) (i .incoming)) := by
  have hv := PairedEntry.graph_value _ _ (graph_equations i s) hr (commit_zero s i hi) hd he
    (PairedEntry.matches_kind p image node _ hm)
  simp only [idle_value p image s i h hi, BitVec.extractLsb'_append_eq_right,
    BitVec.extractLsb'_append_eq_left] at hv
  exact hv.trans (PairedEntry.value_matches p image node _ _ hm
    (entry_parameter_value p image s i h he) _ _)
  done

theorem current_fields (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (h : Context p image s) (hb : Running s.registers) (pc : Fin 256)
    (hpc : PairedImage.row (s.registers .current) = BitVec.ofFin pc) :
    s.registers .cached = PairedImage.parameter (Execution.fields (p.fetch pc)) ∧
    (s.registers .current).extractLsb' 9 8 = (Execution.fields (p.fetch pc)).duration := by
  have parts := running_parts p image _ _
    (PairedRuntime.certified_current s h.invariant hb p image h.certificate) (h.invariant.2 hb).2.2.2.1
  simpa only [PairedImage.fields, hpc] using
    And.intro ((PairedRuntime.certified_values s h.invariant hb p image h.certificate).1.trans parts.2)
      (token_fields _ _ parts.1).2.2.2
  done

theorem dispatch_entry (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (i : Values Loader.Machine.Input) (h : Context p image s) (hb : Running s.registers)
    (he : entering.eval (graphInputs i s) s.registers = 1) :
    PairedImage.Matches p image
      (PairedImage.successor p (PairedImage.row (s.registers .current))
        (branch.eval (graphInputs i s) s.registers == 1))
      (entered.eval (graphInputs i s) s.registers) := by
  have hm := PairedRuntime.certified_current s h.invariant hb p image h.certificate
  have hn : (PairedImage.fields p (PairedImage.row (s.registers .current))).kind ≠ 4 := by
    intro hk
    have hw : s.registers .current = 4 := by simpa only [PairedImage.Matches, hk, if_true] using hm.2
    simpa [hw, PairedImage.terminal] using (h.invariant.2 hb).2.2.2.1
    done
  have hd := PairedRuntime.dispatch_matches s i h.invariant hb p image h.certificate he
  simpa only [PairedImage.referenceStep, hn, if_false, advance,
    current_next _ _ (graph_equations i s), he, if_true] using hd
  done

theorem boot_entry (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (i : Values Loader.Machine.Input) (h : Context p image s)
    (hb : busy.eval (graphInputs i s) s.registers = 0) :
    PairedImage.Matches p image (some 0) (entered.eval (graphInputs i s) s.registers) := by
  have ha := PairedCoverage.certified_image s h.invariant.1 h.valid p image h.certificate
  have hw := congrArg (fun b : Values PairedLoader.Slot => b .boot) ha.1
  simp only [entered_wire _ _ (graph_equations i s), enteredExpr, Expr.eval,
    hb, BitVec.reduceEq, if_false, bootWord_value _ _ (graph_equations i s)]
  exact (show s.registers (.boot (s.registers .active == 1)) = image.boot from hw).symm ▸ ha.2.1
  done

end Pinwheel.Hardware.Storage.PairedCertified
