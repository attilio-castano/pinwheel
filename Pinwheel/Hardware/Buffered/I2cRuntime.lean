import Pinwheel.Hardware.Buffered.I2cGeometry
import Pinwheel.Hardware.Buffered.I2cResident

/-! Initialized actual SRAM observations and geometry preservation for the
fixed I²C image. Source execution refinement is composed separately. -/
namespace Pinwheel.Hardware.Buffered.I2cLoading
open Pinwheel.Hardware

theorem initialized_i2c_observe (s : SramState.State)
    (i : Values Reactive.Input) (hi : i .initialize = 1)
    (loading runtime : List (Values Reactive.Input))
    (hs : SourceHistory (s.step i) loading)
    (hv : (SramLoading.run (s.step i) SramLoading.Ledger.initial loading).1.registers (.core .valid) = 1)
    (hr : ∀ j ∈ runtime, SramExecution.ExecutingInput j)
    (query : Values Reactive.Input) (hq : SharedBranches.Runtime query) (o : Reactive.Output w) :
    let after := SramLoading.run (s.step i) SramLoading.Ledger.initial loading
    (after.1.run runtime).observe query o =
      Reactive.circuit.observe query
        (SramExecution.reactiveRun
          (SramExecution.withWords (SramExecution.core after.1.registers) I2cSource.fullWords) runtime) o := by
  have ht := SramCorrespondence.initialized_to_execution_observe s i hi loading runtime hv hr query hq o
  exact ht.trans (congrArg (fun state : Values Reactive.Register =>
    Reactive.circuit.observe query (SramExecution.reactiveRun state runtime) o)
    (initialized_source_reference s i hi loading hs hv))

end Pinwheel.Hardware.Buffered.I2cLoading

namespace Pinwheel.Hardware.Buffered.I2cGeometry
open Pinwheel.Hardware

private inductive Scalar : Nat → Type where
  | count : Scalar 7
  | virtualSpan : Scalar 11
  | idleLevels : Scalar 3
  | idleEnabled : Scalar 3

private def Scalar.register : Scalar w → Reactive.Register w
  | .count => .count
  | .virtualSpan => .virtualSpan
  | .idleLevels => .idleLevels
  | .idleEnabled => .idleEnabled

private theorem scalar_withWords (p : Scalar w) (i : Values Reactive.Input)
    (s : Values Reactive.Register) (words : Memory.Contents 6 144) :
    (Reactive.next p.register).eval i (SramExecution.withWords s words) =
      (Reactive.next p.register).eval i s := by
  cases p <;> rfl

private theorem scalar_executing (p : Scalar w) (s : Values Reactive.Register)
    (i : Values Reactive.Input) (hi : SramExecution.ExecutingInput i) :
    Reactive.circuit.step i s p.register = s p.register := by
  have hc : Reactive.committing.eval i s = 0 := by
    simp [Reactive.committing, Reactive.both, Reactive.cmd, Expr.eval, hi.1.2.1]
  cases p <;> simp only [Scalar.register, Circuit.step, Reactive.circuit, Reactive.next,
    Expr.eval, Reactive.cold, SramExecution.resetting_executing i s hi, hc, hi.2.1,
    show (0 : BitVec 1) ≠ 1 from by decide, if_false]

theorem reactive_geometry_step (s : Values Reactive.Register)
    (i : Values Reactive.Input) (hi : SramExecution.ExecutingInput i)
    (h : Geometry s) : Geometry (Reactive.circuit.step i s) :=
  ⟨(scalar_executing .count s i hi).trans h.count,
    (scalar_executing .virtualSpan s i hi).trans h.virtualSpan,
    (scalar_executing .idleLevels s i hi).trans h.idleLevels,
    (scalar_executing .idleEnabled s i hi).trans h.idleEnabled⟩

private theorem scalar_sram_executing (p : Scalar w) (s : SramState.State)
    (i : Values Reactive.Input) (hi : SramExecution.ExecutingInput i) :
    (s.step i).registers (.core p.register) = s.registers (.core p.register) := by
  have hn : SramExecution.nonword p.register := by cases p <;> trivial
  change (Sram.coreNext p.register).eval (s.inputs i) s.registers = _
  rw [SramExecution.coreNext_runtime _ _ hi.1 p.register hn,
    SramExecution.base_inputs, scalar_withWords]
  exact scalar_executing p (SramExecution.core s.registers) i hi

theorem geometry_executing (s : SramState.State)
    (i : Values Reactive.Input) (hi : SramExecution.ExecutingInput i)
    (h : Geometry (SramExecution.core s.registers)) :
    Geometry (SramExecution.core (s.step i).registers) :=
  ⟨(scalar_sram_executing .count s i hi).trans h.count,
    (scalar_sram_executing .virtualSpan s i hi).trans h.virtualSpan,
    (scalar_sram_executing .idleLevels s i hi).trans h.idleLevels,
    (scalar_sram_executing .idleEnabled s i hi).trans h.idleEnabled⟩

theorem geometry_runtime (s : SramState.State) (runtime : List (Values Reactive.Input))
    (hr : ∀ i ∈ runtime, SramExecution.ExecutingInput i)
    (h : Geometry (SramExecution.core s.registers)) :
    Geometry (SramExecution.core (s.run runtime).registers) := by
  induction runtime generalizing s with
  | nil => exact h
  | cons i rest ih =>
    exact ih (s.step i) (fun j hj => hr j (List.mem_cons.mpr (Or.inr hj)))
      (geometry_executing s i (hr i (List.mem_cons.mpr (Or.inl rfl))) h)

/-- Polling, START and RELEASE preserve the source-derived image geometry. -/
theorem initialized_source_geometry_runtime (s : SramState.State)
    (i : Values Reactive.Input) (coldInit : i .initialize = 1)
    (loading runtime : List (Values Reactive.Input))
    (source : I2cLoading.SourceHistory (s.step i) loading)
    (valid : (SramLoading.run (s.step i) SramLoading.Ledger.initial loading).1.registers
      (.core .valid) = 1)
    (hr : ∀ j ∈ runtime, SramExecution.ExecutingInput j) :
    let after := SramLoading.run (s.step i) SramLoading.Ledger.initial loading
    Geometry (SramExecution.core (after.1.run runtime).registers) :=
  geometry_runtime _ runtime hr (initialized_source_geometry s i coldInit loading source valid)

end Pinwheel.Hardware.Buffered.I2cGeometry
