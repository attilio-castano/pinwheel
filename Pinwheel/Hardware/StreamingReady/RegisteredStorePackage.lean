import Pinwheel.Hardware.StreamingReady.RegisteredStore
import Pinwheel.Hardware.StreamingReady.TinyWiring
import Pinwheel.Hardware.StreamingReady.TypedExport

/-! Put the registered instruction read behind the existing quad frontend and
    physical wrapper. The additional read register is private to the core. -/
namespace Pinwheel.Hardware.StreamingReady.RegisteredStorePackage
open Pinwheel.Hardware

structure State (a : Nat) where
  frontend : Values Streaming.Frontend.Register
  core : Values (RegisteredStore.Register a)

def State.project (s : State a) : Package.State a :=
  ⟨s.frontend, RegisteredStore.project s.core⟩

def State.Related (s : State a) : Prop := RegisteredStore.Related s.core

def State.coreInputs (s : State a) (p : Package.Pins) : Values Core.Input :=
  s.project.coreInputs (Package.Components.typed a) p

def State.status (s : State a) (p : Package.Pins) : Values Core.Output :=
  (RegisteredStore.circuit a).observe (s.coreInputs p) s.core

def State.step (s : State a) (p : Package.Pins) : State a :=
  ⟨Streaming.Frontend.circuit.step (p.inputs (s.status p)) s.frontend,
   (RegisteredStore.circuit a).step (s.coreInputs p) s.core⟩

def State.observe (s : State a) (p : Package.Pins) : Values Package.Output
  | _, .miso => Streaming.Frontend.circuit.observe (p.inputs (s.status p)) s.frontend .miso
  | _, .ready => Streaming.Frontend.circuit.observe (p.inputs (s.status p)) s.frontend .ready
  | _, .busy => s.status p .busy
  | _, .levels => s.status p .levels
  | _, .enabled => s.status p .enabled

theorem State.status_eq (s : State a) (p : Package.Pins) :
    @State.status a s p = @Streaming.Package.State.status a s.project (Package.Components.typed a) p :=
  RegisteredStore.observe_eq (s.coreInputs p) s.core

private theorem State.project_step_of_core (s : State a) (p : Package.Pins)
    (core : @RegisteredStore.project a ((RegisteredStore.circuit a).step (s.coreInputs p) s.core) =
      @Circuit.step _ _ _ (Core.circuit a) (s.coreInputs p) (RegisteredStore.project s.core)) :
    (s.step p).project = s.project.step (Package.Components.typed a) p := by
  simp only [State.step, s.status_eq p, Package.State.step, Streaming.Package.State.step,
    Streaming.Package.State.frontendInputs, State.project, Package.Components.typed,
    Streaming.Package.Behavior.ofCircuit]
  rw [core]
  rfl

theorem State.project_step (s : State a) (p : Package.Pins) (h : s.Related) :
    (s.step p).project = s.project.step (Package.Components.typed a) p :=
  s.project_step_of_core p (RegisteredStore.project_step (s.coreInputs p) s.core h)

theorem State.project_cold (s : State a) (p : Package.Pins) (h : p.initialize = 1) :
    (s.step p).project = s.project.step (Package.Components.typed a) p :=
  s.project_step_of_core p (RegisteredStore.project_cold (s.coreInputs p) s.core h)

theorem State.preserves (s : State a) (p : Package.Pins) : (s.step p).Related :=
  RegisteredStore.coherent_after_edge (s.coreInputs p) s.core

theorem State.observe_eq (s : State a) (p : Package.Pins) :
    @State.observe a s p = @Streaming.Package.State.observe a s.project (Package.Components.typed a) p := by
  funext w port
  cases port <;> simp only [State.observe, Streaming.Package.State.observe,
    Streaming.Package.State.frontendInputs, s.status_eq p, Package.Components.typed,
    Streaming.Package.Behavior.ofCircuit, State.project]

def State.physical_step (s : State a) (p : TinyWiring.Pins) : State a :=
  s.step ((TinyWiring.canonical a).enginePins p)

def State.physical_observe (s : State a) (p : TinyWiring.Pins) : TinyWiring.Pad → BitVec 8 :=
  (TinyWiring.canonical a).pads p (s.observe ((TinyWiring.canonical a).enginePins p))

private theorem tinyCertificate : TinyWiring.Certificate a (TinyWiring.canonical a) := by
  constructor <;> intros <;> rfl

private theorem wiringCertificate : Wiring.Certificate a (Wiring.canonical a) := by
  constructor <;> intros <;> rfl

theorem State.physical_project_step (s : State a) (p : TinyWiring.Pins) (h : s.Related) :
    (s.physical_step p).project = (TinyWiring.canonical a).step (Wiring.canonical a)
      (Package.Components.typed a) s.project p := by
  rw [tinyCertificate.step_eq wiringCertificate]
  exact s.project_step _ h

theorem State.physical_observe_eq (s : State a) (p : TinyWiring.Pins) :
    s.physical_observe p = (TinyWiring.canonical a).observe (Wiring.canonical a)
      (Package.Components.typed a) s.project p := by
  funext pad
  rw [tinyCertificate.observe_eq wiringCertificate]
  exact congrArg (fun values : Values Package.Output => (TinyWiring.canonical a).pads p values pad)
    (s.observe_eq _)

private def registerSignal (base : Interface (Core.Register a)) (k : Fin (base.size + 1)) :
    Sigma (RegisteredStore.Register a) :=
  if h : k.val < base.size then
    let p := base.signal ⟨k.val, h⟩
    ⟨p.1, .base p.2⟩
  else ⟨64, .fetched⟩

private def registerPosition (base : Interface (Core.Register a)) (r : RegisteredStore.Register a w) :
    Fin (base.size + 1) :=
  match r with
  | .base r => ⟨(base.position r).val, Nat.lt_succ_of_lt (base.position r).isLt⟩
  | .fetched => ⟨base.size, Nat.lt_succ_self base.size⟩

private def registerLabel (base : Interface (Core.Register a)) : RegisteredStore.Register a w → String
  | .base r => base.label r
  | .fetched => "fetched"

set_option maxRecDepth 4096 in
private theorem fetched_name_unused (supported : a = 1 ∨ a = 2)
    (k : Fin (TypedExport.core a supported).registers.size) :
    (TypedExport.core a supported).registers.label ((TypedExport.core a supported).registers.signal k).2 ≠
      "fetched" := by
  rcases supported with rfl | rfl <;> decide +revert +kernel

private theorem registerSignal_position (base : Interface (Core.Register a))
    (r : RegisteredStore.Register a w) : registerSignal base (registerPosition base r) = ⟨w, r⟩ := by
  cases r with
  | base r =>
    unfold registerSignal registerPosition
    rw [dif_pos (base.position r).isLt]
    change (let p := base.signal (base.position r); (⟨p.1, .base p.2⟩ : Sigma (RegisteredStore.Register a))) = _
    rw [base.signal_position]
  | fetched => simp [registerSignal, registerPosition]

private theorem registerLabel_at (base : Interface (Core.Register a)) (k : Fin (base.size + 1)) :
    registerLabel base (registerSignal base k).2 =
      if h : k.val < base.size then base.label (base.signal ⟨k.val, h⟩).2 else "fetched" := by
  unfold registerSignal
  by_cases h : k.val < base.size
  · rw [dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h]
    rfl

private theorem registerLabel_unique (base : Interface (Core.Register a))
    (unused : ∀ k, base.label (base.signal k).2 ≠ "fetched")
    (k l : Fin (base.size + 1))
    (h : registerLabel base (registerSignal base k).2 = registerLabel base (registerSignal base l).2) :
    k = l := by
  rw [registerLabel_at, registerLabel_at] at h
  by_cases hk : k.val < base.size <;> by_cases hl : l.val < base.size
  · rw [dif_pos hk, dif_pos hl] at h
    have same : (⟨k.val, hk⟩ : Fin base.size) = ⟨l.val, hl⟩ := base.unique _ _ h
    exact Fin.ext (congrArg (fun slot : Fin base.size => slot.val) same)
  · rw [dif_pos hk, dif_neg hl] at h
    exact (unused ⟨k.val, hk⟩ h).elim
  · rw [dif_neg hk, dif_pos hl] at h
    exact (unused ⟨l.val, hl⟩ h.symm).elim
  · apply Fin.ext
    omega
  done

def core (a : Nat) (supported : a = 1 ∨ a = 2) :
    TypedModule Core.Input (RegisteredStore.Register a) Core.Output :=
  let baseline := TypedExport.core a supported
  { name := baseline.name
    circuit := RegisteredStore.circuit a
    inputs := baseline.inputs
    registers := {
      size := baseline.registers.size + 1
      signal := registerSignal baseline.registers
      position := registerPosition baseline.registers
      signal_position := registerSignal_position baseline.registers
      label := registerLabel baseline.registers
      unique := registerLabel_unique baseline.registers (fetched_name_unused supported) }
    outputs := baseline.outputs }

end Pinwheel.Hardware.StreamingReady.RegisteredStorePackage
