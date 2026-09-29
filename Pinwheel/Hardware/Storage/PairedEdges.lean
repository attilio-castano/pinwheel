import Pinwheel.Hardware.Storage.PairedCertified

/-! Clock-edge control and observations for certified execution. -/
namespace Pinwheel.Hardware.Storage.PairedEdges
open Pinwheel.Hardware PairedController PairedRunning PairedBits PairedControl PairedE64 PairedCertified
open PairedCoverage (Tracked graphInputs advance graph_equations)
set_option backward.isDefEq.respectTransparency false

theorem running_start (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hb : busy.eval g s = 1) : start.eval g s = 0 := by
  simp [start_wire g s h, startExpr, PairedUpload.accepting_value g s h,
    Loader.enabled, PairedUpload.inputs, hb, both, Expr.eval]

theorem running_edges (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hr : resetting.eval g s = 0)
    (hb : busy.eval g s = 1) :
    ending.eval g s = ~~~(~~~(timeout.eval g s) &&& ~~~(fault.eval g s)) ∧
    entering.eval g s = dispatch.eval g s := by
  simp only [ending_wire g s h, endingExpr, entering_wire g s h, enteringExpr,
    both, either, Expr.eval, hr, hb, running_start g s h hb]
  bv_normalize
  done

theorem checked_dispatch (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (i : Values Loader.Machine.Input) (h : Context p image s) (hi : Rule i)
    (hr : resetting.eval (graphInputs i s) s.registers = 0)
    (hd : ending.eval (graphInputs i s) s.registers = 0)
    (he : entering.eval (graphInputs i s) s.registers = 1)
    (hm : s.registers .mode = 3) (pc : Fin 256) (a : Engine.Reactive.Checked 255 15)
    (hpc : PairedImage.row (s.registers .current) = BitVec.ofFin pc) (ha : p.fetch pc = .checked a) :
    PairedEntry.view (advance s i).registers = Reactive.embed
      (Engine.Reactive.dispatch p pc a.finish
        (Engine.Reactive.capture (samples (s.registers .samples)) a.terminalCapture (i .incoming)) (i .incoming)) := by
  have hb : Running s.registers := by simp [Running, hm]
  have hp := (current_fields p image s h hb pc hpc).1
  simp only [ha] at hp
  have hv := install p image s i h hi hr hd he _ (dispatch_entry p image s i h hb he)
  simp only [entrySamples_wire _ _ (graph_equations i s), entrySamplesExpr, Expr.eval,
    running_start _ _ (graph_equations i s) ((busy_iff _ _ (graph_equations i s)).mpr hb),
    BitVec.reduceEq, if_false, terminal_samples _ _ (graph_equations i s) hm,
    hp, (parameter_checked a).1, Execution.capture_roundtrip, hpc,
    checked_branch a _ _ (graph_equations i s) hm hp] at hv
  simpa [Bool.beq_eq_decide_eq, Reactive.bool_one,
    checked_successor p (BitVec.ofFin pc) a ha,
    show graphInputs i s (.base .incoming) = i .incoming from rfl] using hv
  done

theorem sequential_dispatch (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (i : Values Loader.Machine.Input) (h : Context p image s) (hi : Rule i)
    (hr : resetting.eval (graphInputs i s) s.registers = 0)
    (hd : ending.eval (graphInputs i s) s.registers = 0)
    (he : entering.eval (graphInputs i s) s.registers = 1)
    (hb : Running s.registers) (hm : s.registers .mode ≠ 3) (pc : Fin 256)
    (hpc : PairedImage.row (s.registers .current) = BitVec.ofFin pc)
    (hk : (Execution.fields (p.fetch pc)).kind ≠ 2) :
    PairedEntry.view (advance s i).registers = Reactive.embed
      (Engine.Reactive.next p pc (samples (s.registers .samples)) (i .incoming)) := by
  have hv := install p image s i h hi hr hd he _ (dispatch_entry p image s i h hb he)
  simp only [entrySamples_wire _ _ (graph_equations i s), entrySamplesExpr, Expr.eval,
    running_start _ _ (graph_equations i s) ((busy_iff _ _ (graph_equations i s)).mpr hb),
    BitVec.reduceEq, if_false, exited_wire _ _ (graph_equations i s), exitedExpr, isMode,
    Expr.eval, hm, decide_false, hpc, PairedImage.successor, PairedImage.fields, hk,
    false_and, if_false] at hv
  simpa only [BitVec.ofBool_false, BitVec.reduceEq, if_false, sequential_node] using hv
  done

theorem stop_result (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (i : Values Loader.Machine.Input) (h : Context p image s) (hi : Rule i)
    (hr : resetting.eval (graphInputs i s) s.registers = 0)
    (hd : ending.eval (graphInputs i s) s.registers = 1)
    (he : entering.eval (graphInputs i s) s.registers = 0) :
    PairedEntry.view (advance s i).registers = Reactive.embed
      (Engine.Reactive.stop p
        (if fault.eval (graphInputs i s) s.registers = 1 then .fault else .timeout)
        (samples (s.registers .samples))) := by
  have hv := PairedEntry.ending_graph _ _ (graph_equations i s) hr (commit_zero s i hi) hd he
  simp only [idle_value p image s i h hi, BitVec.extractLsb'_append_eq_right,
    BitVec.extractLsb'_append_eq_left] at hv
  rcases PairedUpload.bit_cases (fault.eval (graphInputs i s) s.registers) with hf | hf <;>
    simpa [advance, hf, Reactive.embed, Engine.Reactive.stop, Reactive.stopMode] using hv
  done

theorem reset_result (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (i : Values Loader.Machine.Input) (h : Context p image s) (hi : Rule i)
    (hr : resetting.eval (graphInputs i s) s.registers = 1) :
    PairedEntry.view (advance s i).registers = Reactive.embed (Engine.Reactive.reset p) := by
  have hv := PairedEntry.reset_graph _ _ (graph_equations i s) hr
  simp only [idle_value p image s i h hi, BitVec.extractLsb'_append_eq_right,
    BitVec.extractLsb'_append_eq_left] at hv
  exact hv

theorem reset_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : reset.eval g s = resetExpr.eval g s := by
  simpa only [reset, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .reset (.concat (.lit (0 : BitVec 63)) resetExpr) (by simp [bindings]))

def resetRequested (i : Values Loader.Machine.Input) : Bool := i .reset == 1 || i .command == 7

theorem resetting_value (s : Tracked) (i : Values Loader.Machine.Input) (hi : Rule i) :
    resetting.eval (graphInputs i s) s.registers = BitVec.ofBool (resetRequested i) := by
  simp only [resetting_wire _ _ (graph_equations i s), resettingExpr, reset_wire _ _ (graph_equations i s),
    resetExpr, either, cmd, Expr.eval, init_zero s i hi,
    show graphInputs i s (.base .reset) = i .reset from rfl,
    show graphInputs i s (.base .command) = i .command from rfl, resetRequested]
  rcases PairedUpload.bit_cases (i .reset) with hr | hr <;>
    by_cases hc : i .command = 7 <;> simp_all [Bool.beq_eq_decide_eq]
  done

theorem stopped_edges (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hr : resetting.eval g s = 0)
    (hb : busy.eval g s = 0) (hv : s .valid = 1) :
    ending.eval g s = 0 ∧ entering.eval g s = BitVec.ofBool (g (.base .command) == 5) ∧
      start.eval g s = BitVec.ofBool (g (.base .command) == 5) := by
  have rr := (resetting_zero g s h).mp hr
  have hs : start.eval g s = BitVec.ofBool (g (.base .command) == 5) := by
    simp [start_wire g s h, startExpr, PairedUpload.accepting_value g s h,
      Loader.enabled, PairedUpload.inputs, rr.1, rr.2, hb, hv, both, cmd, Expr.eval, Bool.beq_eq_decide_eq]
    bv_normalize
  simp only [ending_wire g s h, endingExpr, entering_wire g s h, enteringExpr,
    dispatch_wire g s h, dispatchExpr, both, either, Expr.eval, hr, hb, hs]
  bv_normalize
  done

end Pinwheel.Hardware.Storage.PairedEdges
