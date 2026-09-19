import Pinwheel.Latency
import Pinwheel.Hardware.PinSampler

/-! Bridge from the structural two-register pipeline to `Latency.delayed`. -/
namespace Pinwheel.Hardware.PinSampler
open Loader

/-- Bridge to the structural pipeline: the engine-side `incoming` history of the
wrapped netlist is the pin history shifted by two edges, preceded by the
pipeline's power-up contents. -/
theorem delayed_incoming (p : PinBoundary.Samples 2) (inputs : List Machine.Inputs) :
    (delayed p inputs).map (·.1.incoming) =
      ([p.second, p.first] ++ inputs.map (·.incoming)).take inputs.length := by
  induction inputs generalizing p with
  | nil => rfl
  | cons i rest ih =>
    simp only [delayed, List.map_cons, ih, List.length_cons, engineInputs, PinBoundary.engineInput,
      advance, PinBoundary.sampleStep, Bool.false_eq_true, if_false]
    cases rest with
    | nil => rfl
    | cons j more => simp [List.take]

/-- The same statement cycle by cycle, in the vocabulary of `Latency.delayed`. -/
theorem delayed_incoming_get (p : PinBoundary.Samples 2) (inputs : List Machine.Inputs)
    (cycle : Nat) (h : cycle + 2 < inputs.length) :
    ((delayed p inputs)[cycle + 2]?).map (·.1.incoming) = (inputs[cycle]?).map (·.incoming) := by
  have shape := congrArg (fun l => l[cycle + 2]?) (delayed_incoming p inputs)
  simp only [List.getElem?_map] at shape
  rw [shape, List.getElem?_take]
  simp [h, List.getElem?_map]

end Pinwheel.Hardware.PinSampler
