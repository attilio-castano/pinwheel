import Pinwheel.Hardware.Storage.OnePortBackend
import Pinwheel.Hardware.Storage.PolicyEmit

/-! Emission of the one-port backend, alone and behind the two-register pin
pipeline: three word registers and one flag are the policy's. -/
namespace Pinwheel.Hardware.Storage.Backend.OnePort
open Loader

def extra : Array (Sigma Reg) :=
  #[⟨64, .fetched true⟩, ⟨64, .fetched false⟩, ⟨64, .startWord⟩, ⟨1, .second⟩]

def label : {w : Nat} → Reg w → String
  | _, .fetched true => "fetched_taken"
  | _, .fetched false => "fetched_untaken"
  | _, .startWord => "start_word"
  | _, .second => "entered"

def registers : Array (Sigma Register) := Policy.registers extra

def registerLabel : {w : Nat} → Register w → String := Policy.registerLabel label

def moduleText : Except String String := Policy.moduleText netlist extra label

abbrev SampledRegister := Policy.SampledRegister Reg

def sampledRegisters : Array (Sigma SampledRegister) := Policy.sampledRegisters extra

def sampledText : Except String String := Policy.sampledText netlist extra label

/-- Behind the pipeline, every pre/post-edge observation is the reference
machine's on the delayed pin history, for any power-up pipeline contents, on
any history whose pushed words are ready: the pipeline never touches host ports. -/
theorem sampled_trace_correct (s : State) (h : Valid s) (p : PinBoundary.Samples 2)
    (inputs : List Machine.Inputs) (hr : ∀ i ∈ inputs, Rule i) :
    (PinSampler.component (PinSampler.netlist netlist)).trace
        (Extended.values (s.values values) (PinSampler.stageValues p)) inputs =
      referenceComponent.pairTrace s.reference.machine (PinSampler.delayed p inputs) :=
  Policy.sampled_trace_correct realization SinglePort.correct rules
    (fun q inputs h => PinSampler.delayed_rule rules.Rule (fun _ _ hq => hq) q inputs h)
    s h p inputs hr

end Pinwheel.Hardware.Storage.Backend.OnePort
