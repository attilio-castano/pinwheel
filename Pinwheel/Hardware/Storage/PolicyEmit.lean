import Pinwheel.Hardware.Storage.PolicyBackend
import Pinwheel.Hardware.Storage.SampledBackend

/-! Emission of a fetch-policy backend, alone and behind the two-register pin
pipeline, and the pipeline theorem, once. Ports and the module name are the
general backend's; a policy contributes its registers and their labels. -/
namespace Pinwheel.Hardware.Storage.Backend.Policy
open Loader

variable {p : Nat} {σ : Type} {X : Nat → Type} {P : FetchPolicy.Policy p σ}

/-- The general backend's registers, then the policy's. -/
def registers (extra : Array (Sigma X)) : Array (Sigma (Register X)) :=
  Backend.registers.map (fun ⟨w, r⟩ => ⟨w, .inner r⟩) ++ extra.map (fun ⟨w, x⟩ => ⟨w, .extra x⟩)

def registerLabel (label : {w : Nat} → X w → String) : {w : Nat} → Register X w → String
  | _, .inner r => Backend.registerLabel r
  | _, .extra x => label x

def moduleText (n : Netlist (Register X) Machine.Output Machine.Input) (extra : Array (Sigma X))
    (label : {w : Nat} → X w → String) : Except String String :=
  Hardware.Netlist.moduleText "pinwheel_atomic_small_dense_cached" n
    Machine.inputs (registers extra) Machine.outputs Machine.inputLabel (registerLabel label)
    Machine.outputLabel

abbrev SampledRegister (X : Nat → Type) := Extended (Register X) PinSampler.Stage

def sampledRegisters (extra : Array (Sigma X)) : Array (Sigma (SampledRegister X)) :=
  (registers extra).map (fun ⟨w, r⟩ => ⟨w, .inner r⟩) ++ #[⟨2, .extra .first⟩, ⟨2, .extra .second⟩]

def sampledLabel (label : {w : Nat} → X w → String) : {w : Nat} → SampledRegister X w → String
  | _, .inner r => registerLabel label r
  | _, .extra .first => "pin_first"
  | _, .extra .second => "pin_second"

def sampledText (n : Netlist (Register X) Machine.Output Machine.Input) (extra : Array (Sigma X))
    (label : {w : Nat} → X w → String) : Except String String :=
  Hardware.Netlist.moduleText "pinwheel_atomic_small_dense_cached" (PinSampler.netlist n)
    Machine.inputs (sampledRegisters extra) Machine.outputs Machine.inputLabel (sampledLabel label)
    Machine.outputLabel

/-- Behind the pipeline, every pre/post-edge observation is the reference
machine's on the delayed pin history, for any power-up pipeline contents, on any
history satisfying a rule the pipeline preserves — one that reads host ports only. -/
theorem sampled_trace_correct (Z : Realization P X) (C : FetchPolicy.Correct P) (R : Rules C)
    (preserved : ∀ (q : PinBoundary.Samples 2) (inputs : List Machine.Inputs),
      (∀ i ∈ inputs, R.Rule i) → ∀ e ∈ PinSampler.delayed q inputs, R.Rule e.1)
    (s : State σ) (h : Valid C s) (q : PinBoundary.Samples 2) (inputs : List Machine.Inputs)
    (hr : ∀ i ∈ inputs, R.Rule i) :
    (PinSampler.component (PinSampler.netlist Z.netlist)).trace
        (Extended.values (s.values Z.values) (PinSampler.stageValues q)) inputs =
      referenceComponent.pairTrace s.reference.machine (PinSampler.delayed q inputs) :=
  (PinSampler.trace_eq Z.netlist (s.values Z.values) q inputs).trans
    ((completeRefinement Z C R).pairTrace_eq _ _ (related Z C R s h) _ (preserved q inputs hr))

/-- The trivial rule survives anything. -/
theorem Rules.none_preserved (C : FetchPolicy.Correct P) (h : ∀ i, C.Rule i)
    (q : PinBoundary.Samples 2) (inputs : List Machine.Inputs)
    (_ : ∀ i ∈ inputs, (Rules.none C h).Rule i) : ∀ e ∈ PinSampler.delayed q inputs, (Rules.none C h).Rule e.1 :=
  fun _ _ => trivial

end Pinwheel.Hardware.Storage.Backend.Policy
