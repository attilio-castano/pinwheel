import Pinwheel.Hardware.Buffered.I2cLoading
import Pinwheel.Hardware.Buffered.SpiGeometry

/-! Accepted I²C COMMIT operands determine actual controller geometry.
The shared SRAM scalar equations are reused from `SpiGeometry`; they have no
SPI configuration premise. -/
namespace Pinwheel.Hardware.Buffered.I2cGeometry
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

structure Geometry (r : Values Reactive.Register) : Prop where
  count : r .count = 50
  virtualSpan : r .virtualSpan = 270
  idleLevels : r .idleLevels = 0
  idleEnabled : r .idleEnabled = 0

private theorem valid_post_facts (i : Values Sram.Input) (s : Values Sram.Register)
    (hv : Sram.circuit.step i s (.core .valid) = 1) :
    SramCoverage.resetting.eval i s ≠ 1 ∧ i (.base .initialize) ≠ 1 ∧
      (Sram.committing.eval i s = 1 ∨ s (.core .valid) = 1) := by
  rw [SramCoverage.valid_step] at hv
  split at hv
  · contradiction
  · rename_i hreset
    have hr : SramCoverage.resetting.eval i s ≠ 1 := fun h => hreset (Or.inl h)
    refine ⟨hr, fun h => hr (SramCoverage.cold_resetting i s h), ?_⟩
    split at hv
    · exact Or.inl ‹Sram.committing.eval i s = 1›
    · exact Or.inr hv
  done

def WhenValid (s : SramState.State) : Prop :=
  s.registers (.core .valid) = 1 → Geometry (SramExecution.core s.registers)

theorem source_geometry_step (s : SramState.State) (i : Values Reactive.Input)
    (h : WhenValid s) (hi : I2cLoading.SourceInput s i) : WhenValid (s.step i) := by
  intro hv
  have facts := valid_post_facts (s.inputs i) s.registers hv
  by_cases hc : Sram.committing.eval (s.inputs i) s.registers = 1
  · have hs := hi.commit hc
    constructor
    all_goals simp only [SramExecution.core, SramState.State.step, SramCoverage.count_step,
      SpiGeometry.virtualSpan_step, SpiGeometry.idleLevels_step, SpiGeometry.idleEnabled_step,
      if_neg facts.1, if_pos hc, SramState.State.inputs]
    all_goals simp only [hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, ite_self]
    done
  · have old := h (facts.2.2.resolve_left hc)
    have cold : i .initialize ≠ 1 := facts.2.1
    constructor
    all_goals simp only [SramExecution.core, SramState.State.step, SramCoverage.count_step,
      SpiGeometry.virtualSpan_step, SpiGeometry.idleLevels_step, SpiGeometry.idleEnabled_step,
      if_neg facts.1, if_neg hc, SramState.State.inputs, if_neg cold]
    · exact old.count
    · exact old.virtualSpan
    · exact old.idleLevels
    · exact old.idleEnabled
  done

theorem source_geometry_cold (s : SramState.State) (i : Values Reactive.Input)
    (hi : i .initialize = 1) : WhenValid (s.step i) := by
  intro hv
  exact False.elim ((valid_post_facts (s.inputs i) s.registers hv).2.1 hi)

theorem source_geometry_run (s : SramState.State) (t : SramLoading.Ledger)
    (loading : List (Values Reactive.Input)) (h : WhenValid s)
    (hs : I2cLoading.SourceHistory s loading) :
    WhenValid (SramLoading.run s t loading).1 := by
  induction loading generalizing s t with
  | nil => exact h
  | cons i rest ih => exact ih (s.step i) (t.step s i) (source_geometry_step s i h hs.1) hs.2

theorem initialized_source_geometry (s : SramState.State) (i : Values Reactive.Input)
    (coldInit : i .initialize = 1) (loading : List (Values Reactive.Input))
    (source : I2cLoading.SourceHistory (s.step i) loading)
    (valid : (SramLoading.run (s.step i) SramLoading.Ledger.initial loading).1.registers
      (.core .valid) = 1) :
    let after := SramLoading.run (s.step i) SramLoading.Ledger.initial loading
    Geometry (SramExecution.core after.1.registers) :=
  source_geometry_run (s.step i) SramLoading.Ledger.initial loading
    (source_geometry_cold s i coldInit) source valid

theorem Geometry.withWords {s : Values Reactive.Register} (h : Geometry s)
    (words : Memory.Contents 6 144) : Geometry (SramExecution.withWords s words) :=
  ⟨h.count, h.virtualSpan, h.idleLevels, h.idleEnabled⟩

end Pinwheel.Hardware.Buffered.I2cGeometry
