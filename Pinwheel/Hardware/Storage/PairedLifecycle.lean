import Pinwheel.Hardware.Storage.PairedTimed

/-! Accepted commit establishes the E64 execution relation for a new program.
The accepted transcript, rather than power-up values or an extra reset, owns
the program. The same boundary applies to every certified replacement. -/
namespace Pinwheel.Hardware.Storage.PairedLifecycle
open Pinwheel.Hardware PairedController PairedRunning PairedBits PairedControl PairedCertified
open PairedCoverage (Tracked graphInputs advance graph_equations)
set_option backward.isDefEq.respectTransparency false

def Accepted (s : Tracked) (i : Values Loader.Machine.Input) : Prop :=
  commit.eval (graphInputs i s) s.registers = 1

theorem commit_conditions (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hc : commit.eval g s = 1) :
    init.eval g s = 0 ∧ push.eval g s = 0 := by
  have accepted : PairedLoader.commit (PairedUpload.inputs g s) (PairedUpload.control s) = true :=
    by simpa only [PairedUpload.commit_value g s h, Reactive.bool_one] using hc
  obtain ⟨hi, _, _, hcmd, _, _⟩ := PairedLoader.commit_requires _ _ accepted
  rcases PairedUpload.bit_cases (init.eval g s) with hiz | hiz <;>
    simp_all [PairedUpload.inputs, PairedUpload.push_value g s h, PairedLoader.push]
  done

theorem commit_graph (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hc : commit.eval g s = 1) :
    PairedEntry.view (body.step g s) =
      ⟨0, 0, 0, 0, ⟨(idleWord.eval g s).extractLsb' 0 3,
        (idleWord.eval g s).extractLsb' 3 3⟩, Vector.replicate 16 false⟩ := by
  rcases PairedUpload.bit_cases (resetting.eval g s) with hr | hr <;>
    simp [PairedEntry.view, Circuit.step, body, PairedController.next, nextMode_wire g s h,
      nextModeExpr, stopping_wire g s h, stoppingExpr, both, either, Expr.eval, hr, hc]
  all_goals exact samples_zero

theorem commit_idle (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hc : commit.eval g s = 1) :
    idleWord.eval g s = (body.step g s) (.idle ((body.step g s) .active == 1)) := by
  simp only [idleWord_wire g s h, idleWordExpr, Circuit.step, body, PairedController.next,
    both, either, Expr.eval, (commit_conditions g s h hc).1, (commit_conditions g s h hc).2, hc]
  rcases PairedUpload.bit_cases (selected.eval g s) with hs | hs <;> simp [hs]
  done

theorem commit_context (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (i : Values Loader.Machine.Input) (h : PairedRuntime.Invariant s) (hc : Accepted s i)
    (hp : PairedImage.check p image s.ledger.staged = true) :
    Context p image (advance s i) := by
  refine ⟨PairedRuntime.invariant_next s i h, ?_, ?_⟩
  case refine_1 =>
    simp [advance, Circuit.step, body, PairedController.next, Expr.eval, either,
      (commit_conditions _ _ (graph_equations i s) hc).1, show commit.eval (graphInputs i s) s.registers = 1 from hc]
  have accepted : PairedLoader.commit (PairedUpload.inputs (graphInputs i s) s.registers)
      (PairedUpload.control s.registers) = true :=
    by simpa only [Accepted, PairedUpload.commit_value _ _ (graph_equations i s), Reactive.bool_one] using hc
  obtain ⟨hi, hr, hb, hcmd, _, _⟩ := PairedLoader.commit_requires _ _ accepted
  simpa [advance, PairedLoader.record, hi, hr, hb, hcmd, accepted] using hp
  done

theorem commit_view (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (i : Values Loader.Machine.Input) (hc : Accepted s i)
    (h : Context p image (advance s i)) :
    PairedEntry.view (advance s i).registers = Reactive.embed (Engine.Reactive.reset p) := by
  have ha := PairedCoverage.certified_image (advance s i) h.invariant.1 h.valid p image h.certificate
  have hi : idleWord.eval (graphInputs i s) s.registers = p.idle.enabled ++ p.idle.levels :=
    (commit_idle _ _ (graph_equations i s) hc).trans
      ((congrArg (fun b : Values PairedLoader.Slot => b .idle) ha.1).trans ha.2.2.1)
  simpa only [hi, BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left,
    advance, Engine.Reactive.reset, Engine.Reactive.stop, Reactive.embed, Reactive.stopMode] using commit_graph _ _ (graph_equations i s) hc
  done

/-- No extra reset: the actual accepted commit is the execution boundary. -/
theorem after_commit (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (i : Values Loader.Machine.Input) (h : PairedRuntime.Invariant s) (hc : Accepted s i)
    (hp : PairedImage.check p image s.ledger.staged = true) :
    PairedTimed.Related p image (advance s i) (Engine.Reactive.reset p) := by
  exact ⟨commit_context p image s i h hc hp, trivial,
    commit_view p image s i hc (commit_context p image s i h hc hp)⟩

/-- A first upload or replacement commit starts a fresh certified segment.
The previous program, execution state and sample values are unrestricted. -/
theorem retained_segment (p : Execution.Image) (image : PairedImage.Image)
    (n : Netlist Register (SramController.Out Loader.Machine.Output) Input)
    (hn : PairedValidation.core = .ok n) (memory : Memory.SinglePort.Contract S 9 64)
    (actual : Values Register × S) (s : Tracked)
    (hs : PairedCoverage.view memory actual = s.physical) (h : PairedRuntime.Invariant s)
    (commitInput : Values Loader.Machine.Input) (hc : Accepted s commitInput)
    (hp : PairedImage.check p image s.ledger.staged = true)
    (history : List (Values Loader.Machine.Input)) (hi : ∀ i ∈ history, Rule i) :
    (PairedTimed.executable n.component memory).trace
        ((PairedClosed.implementation n.component memory).step commitInput actual) history =
      (PairedTimed.reference p).trace (Engine.Reactive.reset p) history := by
  rw [PairedComposition.retained_correct n hn]
  exact ((PairedTimed.physical_refinement memory).transRule (PairedTimed.refinement p image)).trace_eq
    _ _ ⟨advance s commitInput, (PairedTimed.physical_refinement memory).step commitInput actual s hs,
      after_commit p image s commitInput h hc hp⟩ history hi
  done

end Pinwheel.Hardware.Storage.PairedLifecycle
