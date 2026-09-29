import Pinwheel.Hardware.Storage.PairedTimedStep
import Pinwheel.Hardware.TimedRule

/-! Conditional, cycle-for-cycle E64 traces of the retained paired controller.
The rule delimits one active program. The SRAM law is an explicit parameter. -/
namespace Pinwheel.Hardware.Storage.PairedTimed
open Pinwheel.Hardware PairedController PairedCertified PairedEdges
open PairedCoverage (Tracked graphInputs advance graph_equations)
set_option backward.isDefEq.respectTransparency false

def reference (p : Execution.Image) : Timed.Component (Values Loader.Machine.Input) Reactive.Model Reactive.State where
  step := fun i m => Engine.Reactive.step p m (resetRequested i) (i .command == 5) (i .incoming)
  observe := fun _ m => Reactive.embed m

def tracked : Timed.Component (Values Loader.Machine.Input) Tracked Reactive.State where
  step := fun i s => advance s i
  observe := fun _ s => PairedEntry.view s.registers

def Related (p : Execution.Image) (image : PairedImage.Image) (s : Tracked) (m : Reactive.Model) : Prop :=
  Context p image s ∧ PairedReference.Coherent p m ∧ PairedEntry.view s.registers = Reactive.embed m

def refinement (p : Execution.Image) (image : PairedImage.Image) :
    Timed.RuleRefinement tracked (reference p) Rule where
  Rel := Related p image
  step := fun i s m hi h => ⟨context_next p image s i h.1 hi,
    PairedReference.step p m _ _ _ h.2.1, PairedTimedStep.step p image s i m h.1 hi h.2.1 h.2.2⟩
  observe := fun _ _ _ h => h.2.2

def observe (o : Values Loader.Machine.Output) : Reactive.State :=
  Reactive.fromValues (fun {_} r => o (.core (.state r)))

theorem graph_observe (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    observe (fun {_} o => body.observe g s (.base o)) = PairedEntry.view s := by
  suffices he : (fun {_} r => body.observe g s (.base (.core (.state r)))) =
      ((PairedEntry.view s).values : Values Reactive.Register) from
    (congrArg Reactive.fromValues he).trans (Reactive.from_values (PairedEntry.view s))
  funext w r
  cases r with
  | pc => simp [Circuit.observe, body, Expr.eval, PairedControl.busy_value g s h,
    Reactive.State.values, PairedEntry.view, row, PairedImage.row]
  | sample k => simp [Circuit.observe, body, Expr.eval, Reactive.State.values,
    PairedEntry.view, PairedBits.samples, PairedBits.slice_one, ← BitVec.getLsbD_eq_getElem]
  | _ => rfl
  done

/-- Project the actual controller's public core-state outputs. Loader status
and speculative memory addresses are outside the E64 observation. -/
def executable (c : PairedComposition.Component Input Register (SramController.Out Loader.Machine.Output))
    (memory : Memory.SinglePort.Contract S 9 64) :
    Timed.Component (Values Loader.Machine.Input) (Values Register × S) Reactive.State where
  step := (PairedClosed.implementation c memory).step
  observe := fun i s => observe ((PairedClosed.implementation c memory).observe i s)

def physical_refinement (memory : Memory.SinglePort.Contract S 9 64) :
    Timed.Refinement (executable PairedComposition.graph memory) tracked where
  Rel := fun s t => PairedCoverage.view memory s = t.physical
  step := by
    intro i s t h
    change PairedCoverage.view memory ((PairedClosed.implementation PairedComposition.graph memory).step i s) =
      (advance t i).physical
    rw [PairedCoverage.view_step, h]
    exact (PairedCoverage.physical_advance t i).symm
  observe := by
    intro i s t h
    exact (graph_observe _ _ (PairedSemantics.inputs_equations bindings PairedSemantics.bindings_ordered
      (PairedClosed.feedback i (memory.view s.2).q) s.1)).trans
      (congrArg (fun rs : Values Register => PairedEntry.view rs) (congrArg Prod.fst h))
    done

/-- Every before/after observation of every consumed edge matches E64.
The premise connects the actual memory implementation to a certified ledger. -/
theorem retained_trace (p : Execution.Image) (image : PairedImage.Image)
    (n : Netlist Register (SramController.Out Loader.Machine.Output) Input)
    (hn : PairedValidation.core = .ok n) (memory : Memory.SinglePort.Contract S 9 64)
    (actual : Values Register × S) (s : Tracked) (m : Reactive.Model)
    (hs : PairedCoverage.view memory actual = s.physical) (h : Related p image s m)
    (history : List (Values Loader.Machine.Input)) (hi : ∀ i ∈ history, Rule i) :
    (executable n.component memory).trace actual history = (reference p).trace m history := by
  rw [PairedComposition.retained_correct n hn]
  exact ((physical_refinement memory).transRule (refinement p image)).trace_eq actual m ⟨s, hs, h⟩ history hi

/-- A reset edge establishes the timed relation from any certified active
state; it assumes neither a clean sample register nor an aligned old mode. -/
theorem after_reset (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (i : Values Loader.Machine.Input) (h : Context p image s) (hi : Rule i)
    (hr : resetRequested i = true) : Related p image (advance s i) (Engine.Reactive.reset p) := by
  refine ⟨context_next p image s i h hi, trivial, ?_⟩
  exact reset_result p image s i h hi (by simp only [resetting_value s i hi, hr, BitVec.ofBool_true])

/-- Complete decoded-command segment from arbitrary power-up state. The upload
history establishes ownership; its accepted transcript must certify this E64
program. After one reset, every execution edge has the reference observation. -/
theorem initialized_segment (p : Execution.Image) (image : PairedImage.Image)
    (n : Netlist Register (SramController.Out Loader.Machine.Output) Input)
    (hn : PairedValidation.core = .ok n) (memory : Memory.SinglePort.Contract S 9 64)
    (registers : Values Register) (initial : S) (initializing : Values Loader.Machine.Input)
    (hinit : initializing .init = 1) (uploadHistory : List (Values Loader.Machine.Input))
    (resetInput : Values Loader.Machine.Input) (hrule : Rule resetInput) (hr : resetRequested resetInput = true)
    (history : List (Values Loader.Machine.Input)) (hi : ∀ i ∈ history, Rule i) :
    let t : Tracked := ⟨registers, memory.view initial, {}⟩
    let uploaded := uploadHistory.foldl advance (advance t initializing)
    let actual := (((initializing : Values Loader.Machine.Input) :: uploadHistory) ++ [(resetInput : Values Loader.Machine.Input)]).foldl
      (fun s i => (PairedClosed.implementation n.component memory).step i s) (registers, initial)
    uploaded.registers .valid = 1 → PairedImage.check p image uploaded.ledger.active = true →
      (executable n.component memory).trace actual history =
        (reference p).trace (Engine.Reactive.reset p) history := by
  dsimp only
  intro hv hc
  rw [PairedComposition.retained_correct n hn]
  let t : Tracked := ⟨registers, memory.view initial, {}⟩
  let uploaded := uploadHistory.foldl advance (advance t initializing)
  have context : Context p image uploaded :=
    ⟨PairedRuntime.initialized_run uploadHistory t initializing hinit, hv, hc⟩
  have rel := after_reset p image uploaded resetInput context hrule hr
  refine ((physical_refinement memory).transRule (refinement p image)).trace_eq _ _
    ⟨advance uploaded resetInput, ?_, rel⟩ history hi
  let setupHistory : List (Values Loader.Machine.Input) :=
    ((initializing : Values Loader.Machine.Input) :: uploadHistory) ++ [(resetInput : Values Loader.Machine.Input)]
  have bridge := (PairedCoverage.view_run memory setupHistory (registers, initial)).trans
    (PairedCoverage.physical_run setupHistory t).symm
  simpa only [physical_refinement, uploaded, setupHistory, List.foldl_append, List.foldl_cons, List.foldl_nil] using bridge
  done

end Pinwheel.Hardware.Storage.PairedTimed
