import Pinwheel.Hardware.Buffered.SpiSource

/-! Source-constrained accepted COMMIT operands establish the actual controller's
SPI execution geometry. The invariant is conditional on VALID throughout loading,
so arbitrary startup values and rejected noncanonical commands remain free. -/
namespace Pinwheel.Hardware.Buffered.SpiGeometry
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

structure Geometry (c : SpiSource.Config) (r : Values Reactive.Register) : Prop where
  count : r .count = 4
  virtualSpan : r .virtualSpan = BitVec.ofNat 11 (16 * (c.bytesMinusOne.val + 1) + 2)
  idleLevels : r .idleLevels = 4
  idleEnabled : r .idleEnabled = 7

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

private theorem scalar_controlled (p : Scalar w) (i : Values Sram.Input)
    (s : Values Sram.Register) :
    (Sram.adapt (SharedBranches.adapt (Reactive.next p.register))).eval i s =
      (Sram.control (SharedBranches.adapt (Reactive.next p.register))).eval i s := by
  rw [SramExecution.adapt_correct, SramExecution.control_correct,
    SharedBranches.adapt_correct, SharedBranches.adapt_correct,
    SramExecution.selected_expand, SramExecution.control_expand,
    scalar_withWords, scalar_withWords]
  exact congrArg (fun input : Values Reactive.Input =>
    (Reactive.next p.register).eval input (SramExecution.core s))
    (SramExecution.mappedInput_same i s)

theorem virtualSpan_step (i : Values Sram.Input) (s : Values Sram.Register) :
    Sram.circuit.step i s (.core .virtualSpan) =
      if SramCoverage.resetting.eval i s = 1 then 0
      else if Sram.committing.eval i s = 1 then i (.base .virtualSpan)
      else s (.core .virtualSpan) := by
  change (Sram.adapt (SharedBranches.adapt (Reactive.next Scalar.virtualSpan.register))).eval i s = _
  rw [scalar_controlled .virtualSpan, SramCoverage.control_correct, SharedBranches.adapt_correct]
  simp only [Scalar.register]
  simp only [SramCoverage.resetting, Sram.committing, SramCoverage.control_correct,
    SharedBranches.committing, SharedBranches.adapt_correct, Reactive.next, Expr.eval,
    SramCoverage.mapped_reset, SharedBranches.expandState, SramCoverage.controlState]
  rfl

theorem idleLevels_step (i : Values Sram.Input) (s : Values Sram.Register) :
    Sram.circuit.step i s (.core .idleLevels) =
      if i (.base .initialize) = 1 then 0
      else if Sram.committing.eval i s = 1 then i (.base .idleLevels)
      else s (.core .idleLevels) := by
  change (Sram.adapt (SharedBranches.adapt (Reactive.next Scalar.idleLevels.register))).eval i s = _
  rw [scalar_controlled .idleLevels, SramCoverage.control_correct, SharedBranches.adapt_correct]
  simp only [Scalar.register, Sram.committing, SramCoverage.control_correct,
    SharedBranches.committing, SharedBranches.adapt_correct, Reactive.next, Expr.eval,
    Reactive.cold, SharedBranches.expandState, SramCoverage.controlState]
  rfl

theorem idleEnabled_step (i : Values Sram.Input) (s : Values Sram.Register) :
    Sram.circuit.step i s (.core .idleEnabled) =
      if i (.base .initialize) = 1 then 0
      else if Sram.committing.eval i s = 1 then i (.base .idleEnabled)
      else s (.core .idleEnabled) := by
  change (Sram.adapt (SharedBranches.adapt (Reactive.next Scalar.idleEnabled.register))).eval i s = _
  rw [scalar_controlled .idleEnabled, SramCoverage.control_correct, SharedBranches.adapt_correct]
  simp only [Scalar.register, Sram.committing, SramCoverage.control_correct,
    SharedBranches.committing, SharedBranches.adapt_correct, Reactive.next, Expr.eval,
    Reactive.cold, SharedBranches.expandState, SramCoverage.controlState]
  rfl

private theorem valid_post_facts (i : Values Sram.Input) (s : Values Sram.Register)
    (hv : Sram.circuit.step i s (.core .valid) = 1) :
    SramCoverage.resetting.eval i s ≠ 1 ∧ i (.base .initialize) ≠ 1 ∧
      (Sram.committing.eval i s = 1 ∨ s (.core .valid) = 1) := by
  rw [SramCoverage.valid_step] at hv
  split at hv
  · contradiction
  · rename_i hreset
    have hr : SramCoverage.resetting.eval i s ≠ 1 := fun h => hreset (Or.inl h)
    refine ⟨hr, ?_, ?_⟩
    · exact fun h => hr (SramCoverage.cold_resetting i s h)
    · split at hv
      · exact Or.inl ‹Sram.committing.eval i s = 1›
      · exact Or.inr hv
  done

def WhenValid (c : SpiSource.Config) (s : SramState.State) : Prop :=
  s.registers (.core .valid) = 1 → Geometry c (SramExecution.core s.registers)

theorem source_geometry_step (c : SpiSource.Config) (s : SramState.State)
    (i : Values Reactive.Input) (h : WhenValid c s) (hi : SpiSource.SourceInput c s i) :
    WhenValid c (s.step i) := by
  intro hv
  have facts := valid_post_facts (s.inputs i) s.registers hv
  have cold : i .initialize ≠ 1 := facts.2.1
  by_cases hc : Sram.committing.eval (s.inputs i) s.registers = 1
  · have hs := hi.commit hc
    constructor
    all_goals simp only [SramExecution.core, SramState.State.step, SramCoverage.count_step,
      virtualSpan_step, idleLevels_step, idleEnabled_step, if_neg facts.1,
      if_pos hc, SramState.State.inputs, if_neg cold]
    · exact hs.1
    · exact hs.2.1
    · exact hs.2.2.1
    · exact hs.2.2.2
  · have old := h (facts.2.2.resolve_left hc)
    constructor
    all_goals simp only [SramExecution.core, SramState.State.step, SramCoverage.count_step,
      virtualSpan_step, idleLevels_step, idleEnabled_step, if_neg facts.1,
      if_neg hc, SramState.State.inputs, if_neg cold]
    · exact old.count
    · exact old.virtualSpan
    · exact old.idleLevels
    · exact old.idleEnabled
  done

theorem source_geometry_cold (c : SpiSource.Config) (s : SramState.State)
    (i : Values Reactive.Input) (hi : i .initialize = 1) : WhenValid c (s.step i) := by
  intro hv
  exact False.elim ((valid_post_facts (s.inputs i) s.registers hv).2.1 hi)

theorem source_geometry_run (c : SpiSource.Config) (s : SramState.State)
    (t : SramLoading.Ledger) (loading : List (Values Reactive.Input))
    (h : WhenValid c s) (hs : SpiSource.SourceHistory c s loading) :
    WhenValid c (SramLoading.run s t loading).1 := by
  induction loading generalizing s t with
  | nil => exact h
  | cons i rest ih =>
    exact ih (s.step i) (t.step s i) (source_geometry_step c s i h hs.1) hs.2

/-- Actual accepted source operands establish all nonword execution-geometry
registers at any initialized VALID cut. No initial geometry or image equality
is assumed, and loading order and rejected commands remain unconstrained. -/
theorem initialized_source_geometry (c : SpiSource.Config) (s : SramState.State)
    (i : Values Reactive.Input) (coldInit : i .initialize = 1)
    (loading : List (Values Reactive.Input))
    (source : SpiSource.SourceHistory c (s.step i) loading)
    (valid : (SramLoading.run (s.step i) SramLoading.Ledger.initial loading).1.registers
      (.core .valid) = 1) :
    let after := SramLoading.run (s.step i) SramLoading.Ledger.initial loading
    Geometry c (SramExecution.core after.1.registers) :=
  source_geometry_run c (s.step i) SramLoading.Ledger.initial loading
    (source_geometry_cold c s i coldInit) source valid

theorem Geometry.withWords {c : SpiSource.Config} {s : Values Reactive.Register}
    (h : Geometry c s) (words : Memory.Contents 6 144) :
    Geometry c (SramExecution.withWords s words) :=
  ⟨h.count, h.virtualSpan, h.idleLevels, h.idleEnabled⟩

private theorem scalar_executing (p : Scalar w) (s : Values Reactive.Register)
    (i : Values Reactive.Input) (hi : SramExecution.ExecutingInput i) :
    Reactive.circuit.step i s p.register = s p.register := by
  have hc : Reactive.committing.eval i s = 0 := by
    simp [Reactive.committing, Reactive.both, Reactive.cmd, Expr.eval, hi.1.2.1]
  cases p <;> simp only [Scalar.register, Circuit.step, Reactive.circuit, Reactive.next,
    Expr.eval, Reactive.cold, SramExecution.resetting_executing i s hi, hc, hi.2.1,
    show (0 : BitVec 1) ≠ 1 from by decide, if_false]
  done

theorem reactive_geometry_step (c : SpiSource.Config) (s : Values Reactive.Register)
    (i : Values Reactive.Input) (hi : SramExecution.ExecutingInput i)
    (h : Geometry c s) : Geometry c (Reactive.circuit.step i s) := by
  constructor
  · exact (scalar_executing .count s i hi).trans h.count
  · exact (scalar_executing .virtualSpan s i hi).trans h.virtualSpan
  · exact (scalar_executing .idleLevels s i hi).trans h.idleLevels
  · exact (scalar_executing .idleEnabled s i hi).trans h.idleEnabled

theorem reactive_geometry_runtime (c : SpiSource.Config) (s : Values Reactive.Register)
    (runtime : List (Values Reactive.Input))
    (hr : ∀ i ∈ runtime, SramExecution.ExecutingInput i) (h : Geometry c s) :
    Geometry c (SramExecution.reactiveRun s runtime) := by
  induction runtime generalizing s with
  | nil => exact h
  | cons i rest ih =>
    exact ih (Reactive.circuit.step i s) (fun j hj => hr j (List.mem_cons.mpr (Or.inr hj)))
      (reactive_geometry_step c s i (hr i (List.mem_cons.mpr (Or.inl rfl))) h)

private theorem scalar_sram_executing (p : Scalar w) (s : SramState.State)
    (i : Values Reactive.Input) (hi : SramExecution.ExecutingInput i) :
    (s.step i).registers (.core p.register) = s.registers (.core p.register) := by
  have hn : SramExecution.nonword p.register := by cases p <;> trivial
  change (Sram.coreNext p.register).eval (s.inputs i) s.registers = _
  rw [SramExecution.coreNext_runtime _ _ hi.1 p.register hn,
    SramExecution.base_inputs, scalar_withWords]
  exact scalar_executing p (SramExecution.core s.registers) i hi

theorem geometry_executing (c : SpiSource.Config) (s : SramState.State)
    (i : Values Reactive.Input) (hi : SramExecution.ExecutingInput i)
    (h : Geometry c (SramExecution.core s.registers)) :
    Geometry c (SramExecution.core (s.step i).registers) := by
  constructor
  · exact (scalar_sram_executing .count s i hi).trans h.count
  · exact (scalar_sram_executing .virtualSpan s i hi).trans h.virtualSpan
  · exact (scalar_sram_executing .idleLevels s i hi).trans h.idleLevels
  · exact (scalar_sram_executing .idleEnabled s i hi).trans h.idleEnabled

theorem geometry_runtime (c : SpiSource.Config) (s : SramState.State)
    (runtime : List (Values Reactive.Input))
    (hr : ∀ i ∈ runtime, SramExecution.ExecutingInput i)
    (h : Geometry c (SramExecution.core s.registers)) :
    Geometry c (SramExecution.core (s.run runtime).registers) := by
  induction runtime generalizing s with
  | nil => exact h
  | cons i rest ih =>
    exact ih (s.step i) (fun j hj => hr j (List.mem_cons.mpr (Or.inr hj)))
      (geometry_executing c s i (hr i (List.mem_cons.mpr (Or.inl rfl))) h)

/-- Every admitted runtime prefix retains the source-derived geometry of the
actual initialized SRAM controller, including polling, START and RELEASE. -/
theorem initialized_source_geometry_runtime (c : SpiSource.Config) (s : SramState.State)
    (i : Values Reactive.Input) (coldInit : i .initialize = 1)
    (loading runtime : List (Values Reactive.Input))
    (source : SpiSource.SourceHistory c (s.step i) loading)
    (valid : (SramLoading.run (s.step i) SramLoading.Ledger.initial loading).1.registers
      (.core .valid) = 1)
    (hr : ∀ j ∈ runtime, SramExecution.ExecutingInput j) :
    let after := SramLoading.run (s.step i) SramLoading.Ledger.initial loading
    Geometry c (SramExecution.core (after.1.run runtime).registers) :=
  geometry_runtime c _ runtime hr
    (initialized_source_geometry c s i coldInit loading source valid)

end Pinwheel.Hardware.Buffered.SpiGeometry
