import Pinwheel.Hardware.Storage.PrefetchBackend
import Pinwheel.Hardware.Storage.PolicyEmit

/-! Emission of the decoupled prefetch backend, alone and behind the two-register
pin pipeline: three word registers are the policy's. -/
namespace Pinwheel.Hardware.Storage.Backend.Prefetch
open Loader

def extra : Array (Sigma Reg) := #[⟨64, .fetched true⟩, ⟨64, .fetched false⟩, ⟨64, .startWord⟩]

def label : {w : Nat} → Reg w → String
  | _, .fetched true => "fetched_taken"
  | _, .fetched false => "fetched_untaken"
  | _, .startWord => "start_word"

def registers : Array (Sigma Register) := Policy.registers extra

def registerLabel : {w : Nat} → Register w → String := Policy.registerLabel label

def moduleText : Except String String := Policy.moduleText netlist extra label

abbrev SampledRegister := Policy.SampledRegister Reg

def sampledRegisters : Array (Sigma SampledRegister) := Policy.sampledRegisters extra

def sampledText : Except String String := Policy.sampledText netlist extra label

/-- Behind the pipeline, every pre/post-edge observation is the reference
machine's on the delayed pin history, for any power-up pipeline contents. -/
theorem sampled_trace_correct (s : State) (h : Valid s) (p : PinBoundary.Samples 2)
    (inputs : List Machine.Inputs) :
    (PinSampler.component (PinSampler.netlist netlist)).trace
        (Extended.values (s.values values) (PinSampler.stageValues p)) inputs =
      referenceComponent.pairTrace s.reference.machine (PinSampler.delayed p inputs) :=
  Policy.sampled_trace_correct realization Decoupled.correct rules
    (Policy.Rules.none_preserved Decoupled.correct (fun _ => trivial)) s h p inputs (fun _ _ => trivial)

end Pinwheel.Hardware.Storage.Backend.Prefetch
