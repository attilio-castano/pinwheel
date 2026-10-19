import Pinwheel.Hardware.Buffered.SpiRelation
import Pinwheel.Hardware.Buffered.SpiAdmission
import Pinwheel.Hardware.Buffered.SpiEntry
import Pinwheel.Hardware.Buffered.SpiWord
import Pinwheel.Hardware.Buffered.SpiEntryControls
import Pinwheel.Hardware.Buffered.SpiDatapath
import Pinwheel.Hardware.Buffered.SpiFrame
import Pinwheel.Hardware.Buffered.SpiScratch
import Pinwheel.Hardware.Buffered.SpiPins

/-! The source state is constructed from one actual admitted START. There is no
caller-supplied relation or post-edge observation premise. -/
namespace Pinwheel.Hardware.Buffered.SpiRefinement
open Pinwheel.Hardware Pinwheel.Program

private theorem starting_fields (c : SpiSource.Config)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (starting : Reactive.starting.eval i r = 1)
    (image : ∀ k, r (.word k) = SpiSource.fullWords c k) :
    Reactive.entryWord.eval i r = SpiSource.word c 0 ∧
    Reactive.entryControl.eval i r = SpiSource.control c 0 ∧
    Reactive.entryBranch.eval i r = 0 := by
  have record := (SpiAdmission.starting_record i r starting).trans (image 0)
  simp only [Reactive.entryWord, Reactive.entryControl, Reactive.entryBranch,
    Expr.eval, record, SpiSource.fullWords,
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 88),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 64 + 24 ≤ 88),
    BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left]
  simp
  done

private theorem starting_legal (c : SpiSource.Config)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (starting : Reactive.starting.eval i r = 1)
    (image : ∀ k, r (.word k) = SpiSource.fullWords c k)
    (geometry : SpiGeometry.Geometry c r) : Reactive.legalEntry.eval i r = 1 := by
  have controls := SpiAdmission.starting_controls i r starting
  have fields := starting_fields c i r starting image
  have positive : 0 < SpiCoordinates.bitSpan c :=
    Nat.lt_of_lt_of_le (by decide : 0 < 16) (SpiCoordinates.bitSpan_bounds c).1
  have control := SpiEntry.control_legal c 0 i r (Nat.zero_le _)
    (by simpa [SpiCoordinates.physicalPC, positive] using controls.pc)
    (by simpa using controls.virtualPC)
    (by simpa [SpiCoordinates.outer, positive] using controls.outer)
    (by simpa [SpiCoordinates.inner, positive] using controls.inner)
    (by simpa [SpiCoordinates.physicalPC, positive] using fields.2.1)
    geometry.count geometry.virtualSpan
  simp [Reactive.legalEntry, Reactive.both, Expr.eval, control.1, control.2,
    SpiWord.canonical c 0 i r fields.1,
    (SpiWord.branches c 0 i r fields.1 fields.2.2).1,
    (SpiWord.branches c 0 i r fields.1 fields.2.2).2]
  done

private theorem starting_data_available
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (starting : Reactive.starting.eval i r = 1)
    (consuming : Reactive.consuming.eval i r = 1)
    (appending : Reactive.appending.eval i r = 0)
    (positive : 0 < (i .txLength).toNat) :
    Datapath (i .txData) (SpiCircuit.runEntryTick i r)
      ⟨SpiStart.request r i, 1, []⟩ := by
  have facts := SpiCircuit.starting_facts i r starting
  constructor
  all_goals simp [Transfer.Execution.Bounded, Transfer.Request.Bounded, capacity,
    SpiStart.request, SpiCircuit.runEntryTick, Reactive.entryTx,
    Reactive.entryTxLength, Reactive.entryConsumed, Reactive.entryRxLength,
    Reactive.entryCapacity, Expr.eval, starting, consuming, appending,
    facts.txLength, facts.rxCapacity, SpiDatapath.shift_one,
    Nat.succ_le_iff, positive]
  exact Nat.add_lt_add_right facts.transfer 1
  done

private theorem starting_data_exhausted
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (starting : Reactive.starting.eval i r = 1)
    (consuming : Reactive.consuming.eval i r = 0)
    (appending : Reactive.appending.eval i r = 0) :
    Datapath (i .txData) (SpiCircuit.stopEntryTick i r)
      ⟨SpiStart.request r i, 0, []⟩ := by
  have facts := SpiCircuit.starting_facts i r starting
  constructor
  all_goals simp [Transfer.Execution.Bounded, Transfer.Request.Bounded, capacity,
    SpiStart.request, SpiCircuit.stopEntryTick, SpiCircuit.runEntryTick, Reactive.entryTx,
    Reactive.entryTxLength, Reactive.entryConsumed, Reactive.entryRxLength,
    Reactive.entryCapacity, Expr.eval, starting, consuming, appending,
    facts.txLength, facts.rxCapacity]
  exact Nat.add_lt_add_right facts.transfer 1
  done

private theorem starting_running (c : SpiSource.Config)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (starting : Reactive.starting.eval i r = 1)
    (image : ∀ k, r (.word k) = SpiSource.fullWords c k)
    (geometry : SpiGeometry.Geometry c r)
    (consuming : Reactive.consuming.eval i r = 1)
    (appending : Reactive.appending.eval i r = 0)
    (positive : 0 < (i .txLength).toNat) :
    Running c (i .txData) (SpiCircuit.runEntryTick i r)
      (Program.Buffered.start (BufferedSPI.program c) capacity (SpiStart.seed c r i))
      ⟨SpiStart.request r i, 1, []⟩ 0 c.halfCyclesMinusOne := by
  have source := SpiInterpreter.start_available c capacity (SpiStart.seed c r i)
    ⟨SpiStart.request r i, 0, []⟩ ((i .txData).getLsbD 0) rfl rfl
    (by simp [SpiStart.request, SpiPacking.txBits, positive])
  rw [source]
  have controls := SpiAdmission.starting_controls i r starting
  rcases starting_fields c i r starting image with ⟨word, control, _⟩
  rcases SpiWord.fields c 0 i r word with
    ⟨_, capture, _, duration, _, _⟩
  have facts := SpiCircuit.starting_facts i r starting
  refine ⟨⟨SpiFrame.geometry_runEntryTick c i r geometry, image, facts.valid,
    starting_data_available i r starting consuming appending positive,
    rfl, ?_, rfl, SpiScratch.starting_scratch_zero i r starting capture⟩,
    rfl, rfl, Nat.zero_le _, ?_, ?_, facts.retained, rfl, rfl⟩
  · simpa [SpiCircuit.runEntryTick, Reactive.entryTx, Expr.eval, starting]
      using (SpiPins.low_entry_pins c i r word).symm
  · exact SpiFrame.run_entry_at c 0 i r
      (by simpa [SpiCoordinates.physicalPC, SpiCoordinates.bitSpan] using controls.pc)
      (by simpa using controls.virtualPC)
      (by simpa [SpiCoordinates.outer, SpiCoordinates.bitSpan] using controls.outer)
      (by simpa [SpiCoordinates.inner, SpiCoordinates.bitSpan] using controls.inner)
      (by simpa [SpiCoordinates.physicalPC, SpiCoordinates.bitSpan] using control)
      geometry.count geometry.virtualSpan image
  · simpa [SpiCircuit.runEntryTick] using duration
  done

private theorem starting_stopped (c : SpiSource.Config)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (starting : Reactive.starting.eval i r = 1)
    (image : ∀ k, r (.word k) = SpiSource.fullWords c k)
    (geometry : SpiGeometry.Geometry c r)
    (consuming : Reactive.consuming.eval i r = 0)
    (appending : Reactive.appending.eval i r = 0)
    (complete : Reactive.entryComplete.eval i r = 0)
    (empty : (i .txLength).toNat = 0) :
    Stopped c (i .txData) (SpiCircuit.stopEntryTick i r)
      (Program.Buffered.start (BufferedSPI.program c) capacity (SpiStart.seed c r i))
      ⟨SpiStart.request r i, 0, []⟩ false := by
  have source := SpiInterpreter.start_exhausted c capacity (SpiStart.seed c r i)
    ⟨SpiStart.request r i, 0, []⟩ rfl rfl (by simp [SpiStart.request, empty])
  rw [source]
  refine ⟨⟨⟨geometry.count, geometry.virtualSpan, geometry.idleLevels, geometry.idleEnabled⟩,
    image, (SpiCircuit.starting_facts i r starting).valid,
    starting_data_exhausted i r starting consuming appending,
    rfl, ?_, rfl,
    SpiScratch.starting_scratch_zero i r starting
      (SpiWord.fields c 0 i r (starting_fields c i r starting image).1).2.1⟩,
    rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [SpiCircuit.stopEntryTick, BufferedSPI.program,
      geometry.idleLevels, geometry.idleEnabled]
  · simp [SpiCircuit.stopEntryTick, complete]
  done

/-- An actual admitted START establishes the relation to a source request built
from its operands. Empty TX faults immediately, and unused payload bits remain
in the full shift-register ghost. The sampler seed includes the START edge. -/
theorem start_related (c : SpiSource.Config)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (image : ∀ k, r (.word k) = SpiSource.fullWords c k)
    (geometry : SpiGeometry.Geometry c r)
    (starting : Reactive.starting.eval i r = 1) :
    Related c (i .txData) (Reactive.circuit.step i r)
      (Program.Buffered.start (BufferedSPI.program c) capacity (SpiStart.seed c r i)) := by
  have controls := SpiAdmission.starting_controls i r starting
  have pre := SpiEntryControls.starting_preEntry i r starting
    (starting_legal c i r starting image geometry)
  have scalar := SpiWord.fields c 0 i r (starting_fields c i r starting image).1
  have kind : Reactive.kind.eval i r = 1 := scalar.1
  have wants : Reactive.wantsRx.eval i r = 0 := by
    simp [Reactive.wantsRx, Expr.eval, scalar.2.2.2.2.2]
  by_cases positive : 0 < (i .txLength).toNat
  · have flags := SpiEntryControls.low_available i r pre kind wants
      (by simpa [Reactive.entryConsumed, Reactive.entryTxLength, Expr.eval, starting] using positive)
    rw [SpiCircuit.run_entry_step i r controls.executing controls.releasing
      controls.entering flags.stopping flags.running (Or.inr (Or.inl kind))]
    exact Or.inl ⟨⟨SpiStart.request r i, 1, []⟩, 0, c.halfCyclesMinusOne,
      starting_running c i r starting image geometry flags.consuming flags.appending positive⟩
    done
  · have empty : (i .txLength).toNat = 0 := by omega
    have flags := SpiEntryControls.low_exhausted i r pre kind wants
      (by simpa [Reactive.entryConsumed, Reactive.entryTxLength, Expr.eval, starting] using positive)
    rw [SpiCircuit.stop_entry_step i r controls.executing controls.releasing
      controls.entering flags.stopping flags.noTimeout]
    exact Or.inr ⟨⟨SpiStart.request r i, 0, []⟩, false,
      starting_stopped c i r starting image geometry flags.consuming flags.appending
        flags.complete empty⟩
    done
  done

end Pinwheel.Hardware.Buffered.SpiRefinement
