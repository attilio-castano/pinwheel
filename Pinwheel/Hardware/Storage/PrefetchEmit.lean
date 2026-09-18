import Pinwheel.Hardware.Storage.PrefetchBackend
import Pinwheel.Hardware.Storage.SampledBackend

/-! Emission of the decoupled prefetch backend, alone and behind the two-register
pin pipeline. Ports and the module name are the general backend's; three
registers are new and the same-edge successor lookup is gone. -/
namespace Pinwheel.Hardware.Storage.Backend.Prefetch
open Loader

def registers : Array (Sigma Register) :=
  Backend.registers.map (fun ⟨w, r⟩ => ⟨w, .inner r⟩) ++
    #[⟨64, .fetched true⟩, ⟨64, .fetched false⟩, ⟨64, .startWord⟩]

def registerLabel : {w : Nat} → Register w → String
  | _, .inner r => Backend.registerLabel r
  | _, .fetched true => "fetched_taken"
  | _, .fetched false => "fetched_untaken"
  | _, .startWord => "start_word"

def moduleText : Except String String :=
  Hardware.Netlist.moduleText "pinwheel_atomic_small_dense_cached" netlist
    Machine.inputs registers Machine.outputs Machine.inputLabel registerLabel Machine.outputLabel

abbrev SampledRegister := Extended Register PinSampler.Stage

def sampledRegisters : Array (Sigma SampledRegister) :=
  registers.map (fun ⟨w, r⟩ => ⟨w, .inner r⟩) ++ #[⟨2, .extra .first⟩, ⟨2, .extra .second⟩]

def sampledLabel : {w : Nat} → SampledRegister w → String
  | _, .inner r => registerLabel r
  | _, .extra .first => "pin_first"
  | _, .extra .second => "pin_second"

def sampledText : Except String String :=
  Hardware.Netlist.moduleText "pinwheel_atomic_small_dense_cached" (PinSampler.netlist netlist)
    Machine.inputs sampledRegisters Machine.outputs Machine.inputLabel sampledLabel Machine.outputLabel

/-- Behind the pipeline, every pre/post-edge observation is the reference
machine's on the delayed pin history, for any power-up pipeline contents. -/
theorem sampled_trace_correct (s : State) (h : Valid s) (p : PinBoundary.Samples 2)
    (inputs : List Machine.Inputs) :
    (PinSampler.component (PinSampler.netlist netlist)).trace
        (Extended.values s.values (PinSampler.stageValues p)) inputs =
      referenceComponent.pairTrace s.reference.machine (PinSampler.delayed p inputs) :=
  (PinSampler.trace_eq netlist s.values p inputs).trans
    (completeRefinement.pairTrace_eq s.values s.reference.machine ⟨s, rfl, h, rfl⟩ _)

end Pinwheel.Hardware.Storage.Backend.Prefetch
