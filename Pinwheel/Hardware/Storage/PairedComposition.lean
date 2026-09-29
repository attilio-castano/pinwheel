import Pinwheel.Hardware.Storage.PairedSemantics

/-! Composing the exact paired graph with the existing package adapters.
These are synchronous edge semantics, not electrical timing or RTL-emitter
correctness claims. No extra cycles or initialized register values are assumed. -/
namespace Pinwheel.Hardware.Storage.PairedComposition
open SramController (Reads Out bypass)

abbrev Component (I R O : Nat → Type) := Timed.Component (Values I) (Values R) (Values O)

def fed (f : Feeder J X I) (c : Component I R O) : Component J (Extended R X) O where
  step := fun i s => Extended.values
    (c.step (f.feed i (Extended.extraValues s)) (Extended.innerValues s))
    (f.step i (Extended.extraValues s))
  observe := fun i s => c.observe (f.feed i (Extended.extraValues s)) (Extended.innerValues s)

theorem feeder_correct (f : Feeder J X I) (n : Netlist R O I) :
    (f.wrap n).component = fed f n.component := by
  unfold Netlist.component fed
  congr 1
  all_goals funext i s w p
  case e_step =>
    cases p <;> simp only [Feeder.wrap, Netlist.extend_inner, Netlist.extend_extra,
      Feeder.outer_correct, Feeder.step, Extended.values]
    rfl
  case e_observe =>
    simp only [Feeder.wrap, Netlist.extend_observe, Feeder.outer_correct]
    rfl

def observed (a : Observer I O X P) (c : Component I R O) : Component I (Extended R X) P where
  step := fun i s => Extended.values (c.step i (Extended.innerValues s))
    (fun x => (a.next x).eval (Observed.values i (c.observe i (Extended.innerValues s)))
      (Extended.extraValues s))
  observe := fun i s {_} p => (a.output p).eval
    (Observed.values i (c.observe i (Extended.innerValues s))) (Extended.extraValues s)

theorem observer_correct (a : Observer I O X P) (n : Netlist R O I) :
    (a.wrap n).component = observed a n.component := by
  unfold Netlist.component observed
  congr 1 <;> funext i s w p
  case e_step => cases p <;> simp only [Observer.inner_step, Observer.extra_step, Extended.values]
  case e_observe => exact Observer.observe a n i s p

def graph : Component PairedController.Input PairedController.Register (Out Loader.Machine.Output) where
  step := fun i s => PairedController.body.step (PairedSemantics.inputs PairedController.bindings i s) s
  observe := fun i s => PairedController.body.observe (PairedSemantics.inputs PairedController.bindings i s) s

theorem retained_correct
    (n : Netlist PairedController.Register (Out Loader.Machine.Output) PairedController.Input)
    (h : PairedValidation.core = .ok n) : n.component = graph := by
  unfold Netlist.component graph
  apply congr (congrArg Timed.Component.mk ?_) ?_
  all_goals funext i s
  · simpa only [PairedSemantics.validation_inputs_eq] using
      (PairedSemantics.validation_core_correct n h i s).1
  · simpa only [PairedSemantics.validation_inputs_eq] using
      (PairedSemantics.validation_core_correct n h i s).2

/-- The same typed adapter composition used by `PairedValidation.chipText`. -/
def package (n : Netlist PairedController.Register (Out Loader.Machine.Output) PairedController.Input) :=
  SramAssembly.observer.wrap ((bypass Chip.pinMap).wrap
    ((bypass Feeder.sampler).wrap ((bypass Serial.receiver).wrap n)))

def packaged (c : Component PairedController.Input PairedController.Register (Out Loader.Machine.Output)) :=
  observed SramAssembly.observer (fed (bypass Chip.pinMap)
    (fed (bypass Feeder.sampler) (fed (bypass Serial.receiver) c)))

theorem package_correct (n : Netlist PairedController.Register (Out Loader.Machine.Output) PairedController.Input) :
    (package n).component = packaged n.component := by
  simp only [package, packaged, observer_correct, feeder_correct]

/-- All package registers and outputs, on every edge, interpret the original
paired graph even when the retained upload-validation optimization is used. -/
theorem retained_package_correct
    (n : Netlist PairedController.Register (Out Loader.Machine.Output) PairedController.Input)
    (h : PairedValidation.core = .ok n) : (package n).component = packaged graph := by
  rw [package_correct, retained_correct n h]

end Pinwheel.Hardware.Storage.PairedComposition
