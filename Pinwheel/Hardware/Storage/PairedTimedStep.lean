import Pinwheel.Hardware.Storage.PairedEdges

/-! One actual paired-controller edge refines the timed E64 execution state. -/
namespace Pinwheel.Hardware.Storage.PairedTimedStep
open Pinwheel.Hardware PairedController PairedRunning PairedBits PairedControl PairedE64 PairedCertified PairedEdges
open PairedCoverage (Tracked graphInputs advance graph_equations)
set_option backward.isDefEq.respectTransparency false

theorem busy_model (g : Values GraphInput) (s : Values Register) (m : Reactive.Model)
    (h : PairedSemantics.Equations bindings g s) (hv : PairedEntry.view s = Reactive.embed m) :
    busy.eval g s = BitVec.ofBool (Engine.Reactive.busy m) := by
  have hm := congrArg Reactive.State.mode hv
  rcases m with ⟨control, pins, slots⟩
  cases control <;> simp only [Reactive.embed, PairedEntry.view] at hm
  case stopped reason => cases reason <;> simp [busy_value g s h, hm, Reactive.stopMode, Engine.Reactive.busy]
  all_goals simp [busy_value g s h, hm, Engine.Reactive.busy]
  done

theorem running (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (i : Values Loader.Machine.Input) (m : Reactive.Model)
    (h : Context p image s) (hi : Rule i) (hc : PairedReference.Coherent p m)
    (hv : PairedEntry.view s.registers = Reactive.embed m)
    (hr : resetting.eval (graphInputs i s) s.registers = 0) (hb : Engine.Reactive.busy m = true) :
    PairedEntry.view (advance s i).registers = Reactive.embed (Engine.Reactive.advance p m (i .incoming)) := by
  rcases m with ⟨control, pins, slots⟩
  cases control with
  | stopped reason => simp [Engine.Reactive.busy] at hb
  | checked pc rem =>
    obtain ⟨a, ha⟩ := hc
    have hm : s.registers .mode = 3 := congrArg Reactive.State.mode hv
    have hrem : s.registers .remaining = BitVec.ofFin rem := congrArg Reactive.State.remaining hv
    have hs : samples (s.registers .samples) = slots := congrArg Reactive.State.samples hv
    have hpc : PairedImage.row (s.registers .current) = BitVec.ofFin pc := by
      simpa [PairedEntry.view, Reactive.embed, hm] using congrArg Reactive.State.pc hv
    have run : Running s.registers := by simp [Running, hm]
    have hp := (current_fields p image s h run pc hpc).1
    simp only [ha] at hp
    have hd := checked_decisions a _ _ (graph_equations i s) hm hp
    have he := running_edges _ _ (graph_equations i s) hr ((busy_iff _ _ (graph_equations i s)).mpr run)
    cases hg : a.guard.ready (i .incoming) <;>
      simp only [show graphInputs i s (.base .incoming) = i .incoming from rfl, hg,
        Bool.not_false, Bool.not_true, Bool.false_and, Bool.true_and,
        BitVec.ofBool_false, BitVec.ofBool_true] at hd
    case false =>
      simpa [Engine.Reactive.advance, ha, hg, hd.1, hs] using
        stop_result p image s i h hi hr (by simpa [hd.1, hd.2.1] using he.1) (he.2.trans hd.2.2)
    have hend : ending.eval (graphInputs i s) s.registers = 0 := by simpa [hd.1, hd.2.1] using he.1
    by_cases hz : 0 < rem.val
    case pos =>
      have hen : entering.eval (graphInputs i s) s.registers = 0 := by
        simpa [hrem, Bool.beq_eq_decide_eq, ← BitVec.toNat_inj, Nat.ne_of_gt hz] using he.2.trans hd.2.2
      simpa [advance, hv, hrem, Engine.Reactive.advance, ha, hg, hz, Reactive.embed,
        Reactive.predecessor_counter rem hz] using
        PairedEntry.decrement_graph _ _ (graph_equations i s) hr (commit_zero s i hi) hend hen (Or.inr (Or.inr hm))
      done
    have hen : entering.eval (graphInputs i s) s.registers = 1 := by
      simpa [hrem, Bool.beq_eq_decide_eq, ← BitVec.toNat_inj, Nat.eq_zero_of_not_pos hz] using he.2.trans hd.2.2
    simpa [Engine.Reactive.advance, ha, hg, hz, hs] using
      checked_dispatch p image s i h hi hr hend hen hm pc a hpc ha
    done
  | active pc rem =>
    obtain ⟨a, ha⟩ := hc
    have hm : s.registers .mode = 1 := congrArg Reactive.State.mode hv
    have hrem : s.registers .remaining = BitVec.ofFin rem := congrArg Reactive.State.remaining hv
    have hs : samples (s.registers .samples) = slots := congrArg Reactive.State.samples hv
    have hpc : PairedImage.row (s.registers .current) = BitVec.ofFin pc := by
      simpa [PairedEntry.view, Reactive.embed, hm] using congrArg Reactive.State.pc hv
    have run : Running s.registers := by simp [Running, hm]
    have hd := active_decisions _ _ (graph_equations i s) hm
    have he := running_edges _ _ (graph_equations i s) hr ((busy_iff _ _ (graph_equations i s)).mpr run)
    have hend : ending.eval (graphInputs i s) s.registers = 0 := by simpa [hd.1, hd.2.1] using he.1
    by_cases hz : 0 < rem.val
    case pos =>
      have hen : entering.eval (graphInputs i s) s.registers = 0 := by
        simpa [hrem, Bool.beq_eq_decide_eq, ← BitVec.toNat_inj, Nat.ne_of_gt hz] using he.2.trans hd.2.2
      simpa [advance, hv, hrem, Engine.Reactive.advance, hz, Reactive.embed,
        Reactive.predecessor_counter rem hz] using
        PairedEntry.decrement_graph _ _ (graph_equations i s) hr (commit_zero s i hi) hend hen (Or.inl hm)
    have hen : entering.eval (graphInputs i s) s.registers = 1 := by
      simpa [hrem, Bool.beq_eq_decide_eq, ← BitVec.toNat_inj, Nat.eq_zero_of_not_pos hz] using he.2.trans hd.2.2
    simpa [Engine.Reactive.advance, hz, hs] using
      sequential_dispatch p image s i h hi hr hend hen run (by simp [hm]) pc hpc
        (by simp [ha, Execution.fields, Execution.actionFields])
  | waiting pc rem =>
    obtain ⟨w, ha⟩ := hc
    have hm : s.registers .mode = 2 := congrArg Reactive.State.mode hv
    have hrem : s.registers .remaining = BitVec.ofFin rem := congrArg Reactive.State.remaining hv
    have hs : samples (s.registers .samples) = slots := congrArg Reactive.State.samples hv
    have hpc : PairedImage.row (s.registers .current) = BitVec.ofFin pc := by
      simpa [PairedEntry.view, Reactive.embed, hm] using congrArg Reactive.State.pc hv
    have run : Running s.registers := by simp [Running, hm]
    have hp := (current_fields p image s h run pc hpc).1
    simp only [ha] at hp
    have hd := wait_decisions w _ _ (graph_equations i s) hm hp
    have he := running_edges _ _ (graph_equations i s) hr ((busy_iff _ _ (graph_equations i s)).mpr run)
    cases hg : w.condition.ready (i .incoming) <;>
      simp only [show graphInputs i s (.base .incoming) = i .incoming from rfl, hg,
        Bool.not_false, Bool.not_true, Bool.false_and, Bool.true_and,
        BitVec.ofBool_false, BitVec.ofBool_true] at hd
    case false =>
      have hen := he.2.trans hd.2.2
      by_cases hz : 0 < rem.val
      case pos =>
        have hend : ending.eval (graphInputs i s) s.registers = 0 := by
          simpa [hd.1, hd.2.1, hrem, Bool.beq_eq_decide_eq, ← BitVec.toNat_inj, Nat.ne_of_gt hz] using he.1
        simpa [advance, hv, hrem, Engine.Reactive.advance, ha, hg, hz, Reactive.embed,
          Reactive.predecessor_counter rem hz] using
          PairedEntry.decrement_graph _ _ (graph_equations i s) hr (commit_zero s i hi) hend hen (Or.inr (Or.inl hm))
      have hend : ending.eval (graphInputs i s) s.registers = 1 := by
        simpa [hd.1, hd.2.1, hrem, Bool.beq_eq_decide_eq, ← BitVec.toNat_inj, Nat.eq_zero_of_not_pos hz] using he.1
      simpa [Engine.Reactive.advance, ha, hg, hz, hd.1, hs] using stop_result p image s i h hi hr hend hen
    have hend : ending.eval (graphInputs i s) s.registers = 0 := by simpa [hd.1, hd.2.1] using he.1
    simpa [Engine.Reactive.advance, ha, hg, hs] using
      sequential_dispatch p image s i h hi hr hend (he.2.trans hd.2.2) run (by simp [hm]) pc hpc
        (by simp [ha, Execution.fields])
  | qualifying pc rem budget =>
    obtain ⟨q, ha⟩ := hc
    have hm : s.registers .mode = 4 := congrArg Reactive.State.mode hv
    have hrem : s.registers .remaining = BitVec.ofFin rem := congrArg Reactive.State.remaining hv
    have hbudget : s.registers .waitLeft = BitVec.ofFin budget := congrArg Reactive.State.waitLeft hv
    have hs : samples (s.registers .samples) = slots := congrArg Reactive.State.samples hv
    have hpc : PairedImage.row (s.registers .current) = BitVec.ofFin pc := by
      simpa [PairedEntry.view, Reactive.embed, hm] using congrArg Reactive.State.pc hv
    have run : Running s.registers := by simp [Running, hm]
    have hp := current_fields p image s h run pc hpc
    simp only [ha] at hp
    have hd := qualify_decisions q _ _ (graph_equations i s) hm hp.1
    have he := running_edges _ _ (graph_equations i s) hr ((busy_iff _ _ (graph_equations i s)).mpr run)
    cases hg : q.condition.ready (i .incoming) <;>
      simp only [show graphInputs i s (.base .incoming) = i .incoming from rfl, hg,
        Bool.not_false, Bool.not_true, Bool.false_and, Bool.true_and,
        BitVec.ofBool_false] at hd
    case false =>
      have hen := he.2.trans hd.2.2
      by_cases hz : 0 < budget.val
      case pos =>
        have hend : ending.eval (graphInputs i s) s.registers = 0 := by
          simpa [hd.1, hd.2.1, hbudget, Bool.beq_eq_decide_eq, ← BitVec.toNat_inj, Nat.ne_of_gt hz] using he.1
        simpa [advance, hv, hbudget, hp.2, Engine.Reactive.advance, ha, hg, hz, Reactive.embed,
          Reactive.predecessor_counter budget hz, qualify_guard q _ _ (graph_equations i s) hp.1,
          show graphInputs i s (.base .incoming) = i .incoming from rfl, Execution.fields] using
          PairedEntry.qualify_graph _ _ (graph_equations i s) hr (commit_zero s i hi) hend hen hm
        done
      have hend : ending.eval (graphInputs i s) s.registers = 1 := by
        simpa [hd.1, hd.2.1, hbudget, Bool.beq_eq_decide_eq, ← BitVec.toNat_inj, Nat.eq_zero_of_not_pos hz] using he.1
      simpa [Engine.Reactive.advance, ha, hg, hz, hd.1, hs] using stop_result p image s i h hi hr hend hen
      done
    have hend : ending.eval (graphInputs i s) s.registers = 0 := by simpa [hd.1, hd.2.1] using he.1
    by_cases hz : 0 < rem.val
    case pos =>
      have hen : entering.eval (graphInputs i s) s.registers = 0 := by
        simpa [hrem, Bool.beq_eq_decide_eq, ← BitVec.toNat_inj, Nat.ne_of_gt hz] using he.2.trans hd.2.2
      have hbload : (s.registers .cached).extractLsb' 0 8 = BitVec.ofFin q.budgetMinusOne := by
        simpa only [hp.1, Execution.fields, BitVec.ofNat_finVal] using parameter_budget (Execution.fields (.qualify q)) rfl
      simpa [advance, hv, hrem, hbload, Engine.Reactive.advance, ha, hg, hz, Reactive.embed,
        Reactive.predecessor_counter rem hz, qualify_guard q _ _ (graph_equations i s) hp.1,
        show graphInputs i s (.base .incoming) = i .incoming from rfl] using
        PairedEntry.qualify_graph _ _ (graph_equations i s) hr (commit_zero s i hi) hend hen hm
      done
    have hen : entering.eval (graphInputs i s) s.registers = 1 := by
      simpa [hrem, Bool.beq_eq_decide_eq, ← BitVec.toNat_inj, Nat.eq_zero_of_not_pos hz] using he.2.trans hd.2.2
    simpa [Engine.Reactive.advance, ha, hg, hz, hs] using
      sequential_dispatch p image s i h hi hr hend hen run (by simp [hm]) pc hpc
        (by simp [ha, Execution.fields])
    done

/-- One edge, with reset and start derived from the actual external request. -/
theorem step (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (i : Values Loader.Machine.Input) (m : Reactive.Model)
    (h : Context p image s) (hi : Rule i) (hc : PairedReference.Coherent p m)
    (hv : PairedEntry.view s.registers = Reactive.embed m) :
    PairedEntry.view (advance s i).registers =
      Reactive.embed (Engine.Reactive.step p m (resetRequested i) (i .command == 5) (i .incoming)) := by
  cases hr : resetRequested i
  case true =>
    simpa [Engine.Reactive.step, hr] using reset_result p image s i h hi
      (by simp only [resetting_value s i hi, hr, BitVec.ofBool_true])
  have hr0 : resetting.eval (graphInputs i s) s.registers = 0 := by
    simp only [resetting_value s i hi, hr, BitVec.ofBool_false]
  cases hb : Engine.Reactive.busy m
  case true => simpa [Engine.Reactive.step, hr, hb] using running p image s i m h hi hc hv hr0 hb
  have hb0 : busy.eval (graphInputs i s) s.registers = 0 := by
    simpa only [hb, BitVec.ofBool_false] using busy_model _ _ m (graph_equations i s) hv
  have he := stopped_edges _ _ (graph_equations i s) hr0 hb0 h.valid
  cases hs : i .command == 5 <;>
    simp only [show graphInputs i s (.base .command) = i .command from rfl, hs,
      BitVec.ofBool_false, BitVec.ofBool_true] at he
  case false =>
    simpa [advance, Engine.Reactive.step, hr, hb, hs] using
      (PairedEntry.stopped_graph _ _ (graph_equations i s) hr0 (commit_zero s i hi) he.1 he.2.1 hb0).trans hv
  have entry := install p image s i h hi hr0 he.1 he.2.1 _ (boot_entry p image s i h hb0)
  simpa only [entrySamples_wire _ _ (graph_equations i s), entrySamplesExpr, Expr.eval,
    he.2.2, if_true, samples_zero, enterNode, Engine.Reactive.step, hb, hs,
    Bool.false_eq_true, if_false, Engine.Reactive.start,
    show (0 : BitVec 8).toFin = (0 : Fin 256) from rfl] using entry
  done

end Pinwheel.Hardware.Storage.PairedTimedStep
