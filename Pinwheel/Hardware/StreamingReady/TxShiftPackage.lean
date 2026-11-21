import Pinwheel.Hardware.StreamingReady.PackageSimulation
import Pinwheel.Hardware.StreamingReady.TxShiftCoreProofs

/-! The missing TX pointers have no implementation state. Virtual zero
slots allow the existing status feedback and pin wiring model to describe
the shifted core without changing the package and wrapper types. -/
namespace Pinwheel.Hardware.StreamingReady.TxShiftPackage
open Pinwheel.Hardware

abbrev ShiftBehavior := Package.Behavior Core.Input TxShiftCore.Register Core.Output

def project (s : Values (Core.Register 1)) : Values TxShiftCore.Register :=
  fun r => s r.val

def embed (s : Values TxShiftCore.Register) : Values (Core.Register 1) :=
  fun r => if h : TxShiftCore.retained r then s ⟨r, h⟩ else 0

theorem project_embed (s : Values TxShiftCore.Register) : @project (embed s) = @s := by
  funext w r
  simp only [project, embed, dif_pos r.property]

def components (front : Package.Behavior Streaming.Frontend.Input Streaming.Frontend.Register
    Streaming.Frontend.Output) (candidate : ShiftBehavior) : Package.Components 1 :=
  ⟨front, ⟨fun i s => embed (candidate.step i (project s)),
    fun i s => candidate.observe i (project s)⟩⟩

def typed : Package.Components 1 :=
  components (.ofCircuit Streaming.Frontend.circuit) (.ofCircuit TxShiftCore.circuit)

def RelatedCore (l r : Values (Core.Register 1)) : Prop :=
  @project l = @TxShiftCore.encode r ∧ TxShiftCore.RingInvariant r

abbrev Related := PackageSimulation.Related RelatedCore

theorem simulation : PackageSimulation.Simulates typed (Package.Components.typed 1) RelatedCore where
  frontend := rfl
  step := by
    intro i l r rel
    have h := TxShiftCore.step_encode i r rel.2
    refine ⟨?_, TxShiftCore.invariant_step i r rel.2⟩
    change @project (embed (TxShiftCore.circuit.step i (project l))) =
      @TxShiftCore.encode ((Core.circuit 1).step i r)
    rw [project_embed, rel.1]
    exact h
  observe := by
    intro i l r rel
    change @Circuit.observe _ _ _ TxShiftCore.circuit i (project l) =
      @Circuit.observe _ _ _ (Core.circuit 1) i r
    rw [rel.1]
    exact TxShiftCore.observe_encode i r

private theorem frontend_cold (p : Package.Pins) (ls rs : Values Core.Output)
    (l r : Values Streaming.Frontend.Register) (cold : p.initialize = 1) :
    @Circuit.step _ _ _ Streaming.Frontend.circuit (p.inputs ls) l =
      @Circuit.step _ _ _ Streaming.Frontend.circuit (p.inputs rs) r := by
  funext w reg
  cases reg <;>
    simp only [Circuit.step, Streaming.Frontend.circuit, Streaming.Frontend.next,
      Expr.eval, Streaming.Package.Pins.inputs, cold, ↓reduceIte]

theorem cold_related (l r : Package.State 1) (p : Package.Pins) (cold : p.initialize = 1) :
    Related (l.step typed p) (r.step (Package.Components.typed 1) p) := by
  let li := @Streaming.Package.State.coreInputs 1 l typed p
  let ri := @Streaming.Package.State.coreInputs 1 r (Package.Components.typed 1) p
  have lc : li .initialize = 1 := cold
  have rc : ri .initialize = 1 := cold
  refine ⟨frontend_cold p (l.status typed p) (r.status (Package.Components.typed 1) p)
    l.frontend r.frontend cold, ?_, TxShiftCore.cold_invariant ri r.core rc⟩
  change @project (embed (TxShiftCore.circuit.step li (project l.core))) =
    @TxShiftCore.encode ((Core.circuit 1).step ri r.core)
  rw [project_embed]
  exact TxShiftCore.cold_encode li ri r.core (project l.core) lc rc

end Pinwheel.Hardware.StreamingReady.TxShiftPackage
