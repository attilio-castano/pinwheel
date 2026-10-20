import Pinwheel.Hardware.Buffered.SpiShift
import Pinwheel.Hardware.Buffered.SpiReceive
import Pinwheel.Hardware.Buffered.SpiTerminal
import Pinwheel.Hardware.Buffered.SpiSramRelation
import Pinwheel.Hardware.Buffered.SpiStartRefinement

/-! Universal SPI execution-prefix composition, through initialized digital
SRAM loading and the actual packed Reactive circuit. -/
namespace Pinwheel.Hardware.Buffered.SpiRefinement
open Pinwheel.Hardware Pinwheel.Program

theorem related_step {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    (h : Related c payload r s) (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i) :
    Related c payload (Reactive.circuit.step i r)
      (Program.Buffered.advance (BufferedSPI.program c) capacity s (i .rawInputs)) := by
  rcases h with ⟨e, pc, remaining, running⟩ | ⟨e, complete, stopped⟩
  case inr => exact Or.inr ⟨e, complete, stopped.step i quiet⟩
  case inl =>
    by_cases positive : 0 < remaining.val
    case pos => exact Or.inl ⟨e, pc, _, running.countdown positive i quiet⟩
    case neg =>
      have zero : remaining = 0 := Fin.ext (by omega)
      subst remaining
      have bound := SpiEntry.physicalPC_lt_four c running.nextPC.val
        (Nat.add_le_add_right running.within 1)
      have choice : SpiCoordinates.physicalPC c running.nextPC.val = 0 ∨
          SpiCoordinates.physicalPC c running.nextPC.val = 1 ∨
          SpiCoordinates.physicalPC c running.nextPC.val = 2 ∨
          SpiCoordinates.physicalPC c running.nextPC.val = 3 := by omega
      rcases choice with physical | physical | physical | physical
      · exact running.low_step i quiet physical
      · exact running.high_step i quiet physical
      · exact Or.inl ⟨e, running.nextPC, c.halfCyclesMinusOne, running.release_step i quiet physical⟩
      · exact Or.inr ⟨e, true, running.halt_step i quiet physical⟩
      done
    done
  done

theorem related_run {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    (initial : Related c payload r s) (incoming : Nat → BitVec 2) (edges : Nat) :
    Related c payload (SpiStart.packedRun r incoming edges)
      (Program.Buffered.run (BufferedSPI.program c) capacity s incoming edges) := by
  induction edges
  case zero => exact initial
  case succ n ih =>
    rw [SpiStart.packedRun_succ, Program.Buffered.run]
    exact related_step ih (SpiStart.quietInput (incoming n)) ⟨rfl, rfl⟩
  done

theorem started_run (c : SpiSource.Config) (i : Values Reactive.Input)
    (r : Values Reactive.Register)
    (image : ∀ k, r (.word k) = SpiSource.fullWords c k)
    (geometry : SpiGeometry.Geometry c r) (starting : Reactive.starting.eval i r = 1)
    (incoming : Nat → BitVec 2) (edges : Nat) :
    Related c (i .txData) (SpiStart.packedRun (Reactive.circuit.step i r) incoming edges)
      (Program.Buffered.run (BufferedSPI.program c) capacity
        (Program.Buffered.start (BufferedSPI.program c) capacity (SpiStart.seed c r i)) incoming edges) :=
  related_run (start_related c i r image geometry starting) incoming edges

/-- Cold initialization and actually accepted source uploads establish the
complete relation. No source/circuit relation, image equality, successful peer,
full TX payload, or matching pin observation is assumed. START is tested on the
actual cut's control registers. Every later command-zero input prefix is free.
-/
theorem initialized_run (c : SpiSource.Config) (s : SramState.State)
    (cold : Values Reactive.Input) (coldInit : cold .initialize = 1)
    (loading : List (Values Reactive.Input))
    (source : SpiSource.SourceHistory c (s.step cold) loading)
    (valid : (SramLoading.run (s.step cold) SramLoading.Ledger.initial loading).1.registers
      (.core .valid) = 1)
    (start : Values Reactive.Input)
    (starting : Reactive.starting.eval start
      (SramExecution.core (SramLoading.run (s.step cold) SramLoading.Ledger.initial loading).1.registers) = 1)
    (incoming : Nat → BitVec 2) (edges : Nat) :
    let after := SramLoading.run (s.step cold) SramLoading.Ledger.initial loading
    RelatedSram c (start .txData)
      ((after.1.step start).run (SpiStart.clocks incoming edges))
      (Program.Buffered.run (BufferedSPI.program c) capacity
        (Program.Buffered.start (BufferedSPI.program c) capacity
          (SpiStart.seed c (SramExecution.core after.1.registers) start)) incoming edges) := by
  let after := SramLoading.run (s.step cold) SramLoading.Ledger.initial loading
  let base : Values Reactive.Register := SramExecution.core after.1.registers
  let reference : Values Reactive.Register := SramExecution.withWords base (SpiSource.fullWords c)
  have referenceEq : @SramExecution.reference after.1 after.2.rows after.2.dictionaryWords = @reference :=
    SpiSource.initialized_source_reference c s cold coldInit loading source valid
  have geometry : SpiGeometry.Geometry c reference :=
    (SpiGeometry.initialized_source_geometry c s cold coldInit loading source valid).withWords
      (SpiSource.fullWords c)
  have accepted : Reactive.starting.eval start reference = 1 :=
    (SramExecution.starting_withWords start base (SpiSource.fullWords c)).trans starting
  have result := started_run c start reference (fun _ => rfl) geometry accepted incoming edges
  have startExecuting := (SpiAdmission.starting_controls start base starting).executing
  have runtime : ∀ j ∈ @start :: SpiStart.clocks incoming edges, SramExecution.ExecutingInput j :=
    List.forall_mem_cons.mpr ⟨startExecuting, SpiStart.clocks_executing incoming edges⟩
  have execution := SramCorrespondence.initialized_to_execution s cold coldInit loading
    (@start :: SpiStart.clocks incoming edges) valid runtime
  change @SramExecution.reference (after.1.run (@start :: SpiStart.clocks incoming edges))
    after.2.rows after.2.dictionaryWords =
    @SramExecution.reactiveRun (SramExecution.reference after.1 after.2.rows after.2.dictionaryWords)
      (@start :: SpiStart.clocks incoming edges) at execution
  rw [referenceEq] at execution
  change @SramExecution.reference ((after.1.step start).run (SpiStart.clocks incoming edges))
    after.2.rows after.2.dictionaryWords =
    @SpiStart.packedRun (Reactive.circuit.step start reference) incoming edges at execution
  have initialized := SramCorrespondence.initialized_resident s cold coldInit loading valid
  have invariants := SramExecution.runtime_invariants after.1
    (@start :: SpiStart.clocks incoming edges) after.2.rows after.2.dictionaryWords
    initialized.2.1 initialized.2.2 runtime
  refine ⟨after.2.rows, after.2.dictionaryWords, invariants.1, invariants.2, ?_⟩
  change Related c (start .txData)
    (SramExecution.reference ((after.1.step start).run (SpiStart.clocks incoming edges))
      after.2.rows after.2.dictionaryWords)
    (Program.Buffered.run (BufferedSPI.program c) capacity
      (Program.Buffered.start (BufferedSPI.program c) capacity (SpiStart.seed c base start)) incoming edges)
  rw [execution]
  exact result
  done

end Pinwheel.Hardware.Buffered.SpiRefinement
