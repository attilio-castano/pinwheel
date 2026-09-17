import Pinwheel.Hardware.PinSampler
import Pinwheel.Hardware.Storage.BankSelect
import Pinwheel.Hardware.Storage.CacheEnable
import Pinwheel.Hardware.Storage.BackendEmit

/-! The proved 32-entry dense cached backends behind the two-register pin
pipeline. The inner netlists and their proofs are reused unchanged. -/
namespace Pinwheel.Hardware.Storage.Backend.Sampled
open Loader PinSampler

abbrev Register := Extended Backend.Register Stage

/-- A backend netlist whose edges refine the reference machine from every valid state. -/
structure Proved (n : Netlist Backend.Register Machine.Output Machine.Input) where
  refinement : Timed.Refinement (PinSampler.component n) referenceComponent
  related : ∀ s : State, Valid s → refinement.Rel s.values s.reference.machine
  next : ∀ (i : Machine.Inputs) (s : State) {w : Nat} (r : Backend.Register w),
    n.step i.values s.values r = (Backend.next i s).values r

def composed : Proved Backend.netlist :=
  ⟨netlistCompleteRefinement, fun s h => ⟨s, rfl, h, rfl⟩, fun i s _ r => netlist_next i s r⟩

def bankSelect (lateBank : Bool) : Proved (BankSelect.netlist lateBank) :=
  ⟨BankSelect.completeRefinement lateBank, fun s h => ⟨s, rfl, h, rfl⟩,
    fun i s _ r => BankSelect.netlist_next lateBank i s r⟩

def cacheEnable : Proved CacheEnable.netlist :=
  ⟨CacheEnable.completeRefinement, fun s h => ⟨s, rfl, h, rfl⟩,
    fun i s _ r => CacheEnable.netlist_next i s r⟩

/-- Behind the pipeline, every pre/post-edge observation is the reference
machine's on the delayed pin history, for any power-up pipeline contents. -/
theorem trace_correct {n} (proof : Proved n) (s : State) (h : Valid s)
    (p : PinBoundary.Samples 2) (inputs : List Machine.Inputs) :
    (PinSampler.component (PinSampler.netlist n)).trace
        (Extended.values s.values (stageValues p)) inputs =
      referenceComponent.pairTrace s.reference.machine (delayed p inputs) :=
  (PinSampler.trace_eq n s.values p inputs).trans
    (proof.refinement.pairTrace_eq s.values s.reference.machine (proof.related s h) _)

/-- The initializing edge needs no prior cache invariant and no defined pipeline. -/
theorem initialized_trace {n} (proof : Proved n) (s : State) (p : PinBoundary.Samples 2)
    (i : Machine.Inputs) (hi : i.init = true) (inputs : List Machine.Inputs) :
    (PinSampler.component (PinSampler.netlist n)).trace
        ((PinSampler.netlist n).step i.values (Extended.values s.values (stageValues p))) inputs =
      referenceComponent.pairTrace
        (Machine.next (capacityInput (engineInputs i p) s.reference.machine) s.reference.machine)
        (delayed (advance i p) inputs) := by
  have he : (engineInputs i p).init = true := hi
  have hn : (n.step (engineInputs i p).values s.values : Values Backend.Register) =
      (fun {_} r => (Backend.next (engineInputs i p) s).values r) :=
    funext fun _ => funext fun r => proof.next (engineInputs i p) s r
  rw [PinSampler.step_eq, hn, ← initialize_machine_next (engineInputs i p) s he]
  exact trace_correct proof (Backend.next (engineInputs i p) s)
    (initialize_valid (engineInputs i p) s he) (advance i p) inputs

/-- Outputs that show registers whatever input is presented: all state views,
including pin levels and enables, the current address and busy. -/
def Registered : {w : Nat} → Machine.Output w → Bool
  | _, .core (.state _) | _, .core .readA | _, .core .busy | _, .control (.state _) => true
  | _, _ => false

/-- For registered outputs the post-edge input of a pair trace is irrelevant, so
they show exactly what an ordinary trace on the consumed inputs shows. Only the
loader handshakes and the successor-read address are combinational. -/
theorem reference_registered (i j : Machine.Inputs) (s : Machine.State) (o : Machine.Output w)
    (h : Registered o = true) :
    referenceComponent.observe i s o = referenceComponent.observe j s o := by
  cases o with
  | core o =>
    cases o with
    | state r => rfl
    | readA => rfl
    | busy => rfl
    | readB => cases h
  | control o =>
    cases o with
    | state r => rfl
    | push => cases h
    | commit => cases h
    | start => cases h
    | rejected => cases h

def registers : Array (Sigma Register) :=
  Backend.registers.map (fun ⟨w, r⟩ => ⟨w, .inner r⟩) ++
    #[⟨2, .extra .first⟩, ⟨2, .extra .second⟩]

def registerLabel : {w : Nat} → Register w → String
  | _, .inner r => Backend.registerLabel r
  | _, .extra .first => "pin_first"
  | _, .extra .second => "pin_second"

/-- Ports and the module name are unchanged; only two pipeline registers are new. -/
def moduleText (n : Netlist Backend.Register Machine.Output Machine.Input) : Except String String :=
  Hardware.Netlist.moduleText "pinwheel_atomic_small_dense_cached" (PinSampler.netlist n)
    Machine.inputs registers Machine.outputs Machine.inputLabel registerLabel Machine.outputLabel

end Pinwheel.Hardware.Storage.Backend.Sampled
