import Pinwheel.Hardware.Processor.ReadyHost
import Pinwheel.Hardware.Processor.LoadableSystemProofs

/-! Once the loader releases the processor, each emitted-design clock has a
typed counterpart in the feedback model. The processor and the peer react
to their own observed pins on each side of the refinement. -/
namespace Pinwheel.Hardware.Processor.ReadyHost

open Pinwheel.Hardware.StreamingReady
open Pinwheel.Program.StreamingReady

set_option backward.isDefEq.respectTransparency false

private def systemInputs (reset : Bool) (pads : TinyWiring.Pad → BitVec 8) : Values SystemInterface.Input
  | _, .at ⟨0,_⟩ => BitVec.ofBool reset
  | _, .at ⟨1,_⟩ => reply pads
  | _, .at ⟨_+2,_⟩ => 0

def normalPins (reset : Bool) (pads : TinyWiring.Pad → BitVec 8) : Values (LoadableSystem.Input aw)
  | _, .left p => systemInputs reset pads p
  | _, .right _ => 0

private theorem system_pins (reset : Bool) (pads : TinyWiring.Pad → BitVec 8) :
    @LoadableSystem.systemPins aw (@normalPins aw reset pads) = @systemInputs reset pads := by
  funext b p
  match p with
  | .at ⟨0,h⟩ =>
    change BitVec.ofBool reset ||| 0 = BitVec.ofBool reset
    exact BitVec.or_zero
  | .at ⟨n+1,h⟩ => rfl

private theorem model_input (reset : Bool) (pads : TinyWiring.Pad → BitVec 8) :
    SystemCircuit.decode (LoadableSystem.systemPins (normalPins (aw := aw) reset pads)) =
      cpuInput reset pads := by
  rw [system_pins]
  cases reset <;> rfl

abbrev RawHost (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (E : Type) :=
  {raw : Values (SystemCircuit.Register aw) // SystemCircuit.Valid layout rom raw} × E

def projectHost {layout : AddressMap.Layout rw aw} {rom : SystemModel.Rom rw} (state : RawHost layout rom E) : Host aw E :=
  (SystemCircuit.view state.1.val, state.2)

variable (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30) (peer : Peer E)

def circuitEnvironment : CausalSession.Environment (RawHost layout rom E) where
  inputs state drive := pins (peer.reset state.2) (state.1.val (SystemCircuit.mmio MmioCircuit.gpio))
    (peer.sample state.2 drive)
  advance state sampled pads :=
    let i := @normalPins aw (peer.reset state.2) pads
    (⟨(LoadableSystem.circuit layout rom romFits ramFits).step i state.1.val,
       LoadableSystem.preserved layout rom romFits ramFits i state.1.val state.1.property⟩,
     peer.advance state.2 sampled pads)

theorem gpio_output (rst : Bool) (pads : TinyWiring.Pad → BitVec 8) (s : Values (SystemCircuit.Register aw)) (valid : SystemCircuit.Valid layout rom s) :
    (LoadableSystem.circuit layout rom romFits ramFits).observe (normalPins rst pads) s
      (.left (.right MmioInterface.gpioOutput)) = if rst then 0 else s (SystemCircuit.mmio MmioCircuit.gpio) := by
  rw [LoadableSystem.output_eq layout rom romFits ramFits _ _ valid]
  change (MmioInterface.outputValues _ _ MmioInterface.gpioOutput) = _
  rw [model_input]
  cases rst <;> rfl

private theorem advance_project (state : RawHost layout rom E) (sampled : Session.Pins)
    (pads : TinyWiring.Pad → BitVec 8) :
    projectHost ((circuitEnvironment layout rom romFits ramFits peer).advance state sampled pads) =
      (environment layout rom peer).advance (projectHost state) sampled pads := by
  refine Prod.ext ?_ rfl
  change SystemCircuit.view ((LoadableSystem.circuit layout rom romFits ramFits).step
    (normalPins (peer.reset state.2) pads) state.1.val) = _
  rw [LoadableSystem.view_step layout rom romFits ramFits _ _ state.1.property]
  have idle : ¬LoadableSystem.Accepted (normalPins (aw := aw) (peer.reset state.2) pads) := by
    simp [LoadableSystem.Accepted, LoadableSystem.mode, normalPins]
  simp only [LoadableSystem.spec, idle, if_false, SystemCircuit.spec]
  rw [model_input]
  rfl

def projectEdge {layout : AddressMap.Layout rw aw} {rom : SystemModel.Rom rw} (e : CausalSession.Edge (RawHost layout rom E)) : CausalSession.Edge (Host aw E) :=
  ⟨projectHost e.environment, e.input, e.drive, e.pads⟩

/-- On every finite run, feedback from the typed processor yields the same
device state, CPU model state, peer state and public edge history. The
device is arbitrary and may inspect every CPU-driven request nibble. -/
theorem feedback_refines (backend : CausalSession.Backend S) (device : S)
    (host : RawHost layout rom E) (clocks : Nat) :
    let typed := backend.run (circuitEnvironment layout rom romFits ramFits peer) device host clocks
    let model := backend.run (environment layout rom peer) device (projectHost host) clocks
    typed.final = model.final ∧ projectHost typed.environment = model.environment ∧
      typed.edges.map projectEdge = model.edges := by
  induction clocks generalizing host device with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    let edge := backend.sample (circuitEnvironment layout rom romFits ramFits peer) device host
    have same : projectEdge edge = backend.sample (environment layout rom peer) device (projectHost host) := rfl
    have tail := ih (backend.step device edge.input)
      ((circuitEnvironment layout rom romFits ramFits peer).advance host edge.input edge.pads)
    dsimp only at tail ⊢
    rw [advance_project] at tail
    simp only [CausalSession.Backend.run, List.map_cons]
    rw [← same]
    exact ⟨tail.1, tail.2.1, congrArg (List.cons (projectEdge edge)) tail.2.2⟩

end Pinwheel.Hardware.Processor.ReadyHost
