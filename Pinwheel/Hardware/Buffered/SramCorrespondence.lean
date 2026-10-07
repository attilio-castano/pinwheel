import Pinwheel.Hardware.Buffered.SramLoading
import Pinwheel.Hardware.Buffered.SramExecution

/-! Initialized accepted loading establishes the resident binary image used by
the actual SRAM execution proof. Source lowering, serial framing, emitted RTL
and physical macro timing keep their separate evidence boundaries. -/
namespace Pinwheel.Hardware.Buffered.SramCorrespondence
open Pinwheel.Hardware
open SramState SramLoading

private theorem dictionary_bit : ∀ k : BitVec 4,
    (65535 : BitVec 16).getLsbD k.toNat = true := by
  decide +kernel

theorem resident_of_coverage (s : State) (t : Ledger)
    (ha : Agrees s t) (hc : Coherent t) (hw : Covered s t)
    (hrows : ∀ k : BitVec 6, k.toNat < (s.registers (.core .count)).toNat →
      (s.registers (.core .written)).getLsbD k.toNat = true)
    (hdict : s.registers .branchWritten = 65535) :
    SramExecution.Resident s t.rows t.dictionaryWords := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun k hk => known_metadata s t ha hc k
      (hw.rows k (hrows k (by simpa only [SramExecution.live, decide_eq_true_eq] using hk)))
  · exact fun k => known_dictionary s t ha k
      (hw.dictionary k (by simpa only [hdict] using dictionary_bit k))
  · exact fun port k hk => (known_word s t ha k
      (hw.rows k (hrows k (by simpa only [SramExecution.live, decide_eq_true_eq] using hk))) port).trans
      (row_word t k).symm
  · exact fun hk => (known_start s t ha hc
      (hw.rows 0 (hrows 0 (by simpa only [SramExecution.live, decide_eq_true_eq] using hk)))).trans
      (row_word t 0).symm
  done

structure Established (s : State) (t : Ledger) : Prop where
  agrees : Agrees s t
  coherent : Coherent t
  covered : Covered s t
  admitted : SramCoverage.ValidCoverage s.registers
  count : SramCoverage.ValidCount s.registers

theorem established_step (s : State) (t : Ledger) (i : Values Reactive.Input)
    (h : Established s t) : Established (s.step i) (t.step s i) :=
  ⟨agrees_step s t i h.agrees, coherent_step s t i h.coherent,
    covered_step s t i h.covered,
    SramCoverage.valid_next (s.inputs i) s.registers h.admitted,
    SramCoverage.valid_count_next (s.inputs i) s.registers h.count⟩

theorem established_cold (s : State) (i : Values Reactive.Input)
    (hi : i .initialize = 1) : Established (s.step i) Ledger.initial :=
  ⟨agrees_initial _, coherent_initial, covered_cold s i hi _,
    SramCoverage.valid_cold (s.inputs i) s.registers hi,
    SramCoverage.valid_count_cold (s.inputs i) s.registers hi⟩

theorem established_run (inputs : List (Values Reactive.Input)) (s : State) (t : Ledger)
    (h : Established s t) : Established (run s t inputs).1 (run s t inputs).2 := by
  induction inputs generalizing s t with
  | nil => exact h
  | cons i rest ih => exact ih (s.step i) (t.step s i) (established_step s t i h)
  done

/-- After initialization, any command history which leaves VALID asserted has
a completely uploaded resident image. Array and Q startup values are arbitrary.
-/
theorem initialized_established (s : State) (i : Values Reactive.Input)
    (hi : i .initialize = 1) (inputs : List (Values Reactive.Input)) :
    Established (run (s.step i) Ledger.initial inputs).1
      (run (s.step i) Ledger.initial inputs).2 :=
  established_run inputs (s.step i) Ledger.initial (established_cold s i hi)

theorem Established.resident {s : State} {t : Ledger} (h : Established s t)
    (hv : s.registers (.core .valid) = 1) :
    SramExecution.Resident s t.rows t.dictionaryWords :=
  resident_of_coverage s t h.agrees h.coherent h.covered
    (h.admitted hv).1 (h.admitted hv).2

theorem ready_of_post_resident (s : State) (i : Values Reactive.Input)
    (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56)
    (hv : (s.step i).registers (.core .valid) = 1)
    (h : SramExecution.Resident (s.step i) rows dictionary) :
    SramExecution.Ready (s.step i) rows := by
  have hw := SramCoverage.valid_post_no_row (s.inputs i) s.registers hv
  apply SramExecution.ready_renewed s i rows hw
  intro port k hk
  have hp := h.2.2.1 port k hk
  simpa only [State.step, Sram.array_read_preserves_bank (s.inputs i) s.registers s.arrays hw port] using hp
  done

def ReadyWhenValid (s : State) (t : Ledger) : Prop :=
  s.registers (.core .valid) = 1 → SramExecution.Ready s t.rows

theorem ready_step (s : State) (t : Ledger) (i : Values Reactive.Input)
    (h : Established s t) : ReadyWhenValid (s.step i) (t.step s i) :=
  fun hv => ready_of_post_resident s i (t.step s i).rows (t.step s i).dictionaryWords hv
    ((established_step s t i h).resident hv)

theorem ready_run (inputs : List (Values Reactive.Input)) (s : State) (t : Ledger)
    (h : Established s t) (hr : ReadyWhenValid s t) :
    ReadyWhenValid (run s t inputs).1 (run s t inputs).2 := by
  induction inputs generalizing s t with
  | nil => exact hr
  | cons i rest ih =>
    exact ih (s.step i) (t.step s i) (established_step s t i h) (ready_step s t i h)
  done

/-- COMMIT and later valid edges establish both candidate responses using the
actual prospective core addresses. READY is derived, rather than an assumption
about initialized SRAM Q or an extra bubble before START.
-/
theorem initialized_ready (s : State) (i : Values Reactive.Input)
    (hi : i .initialize = 1) (inputs : List (Values Reactive.Input)) :
    ReadyWhenValid (run (s.step i) Ledger.initial inputs).1
      (run (s.step i) Ledger.initial inputs).2 := by
  apply ready_run inputs (s.step i) Ledger.initial (established_cold s i hi)
  intro hv
  change Sram.circuit.step (s.inputs i) s.registers (.core .valid) = 1 at hv
  rw [SramCoverage.valid_step] at hv
  simp only [SramCoverage.cold_resetting (s.inputs i) s.registers hi, true_or, if_true] at hv
  exact False.elim ((by decide +kernel : (0 : BitVec 1) ≠ 1) hv)
  done

/-- A valid cut in any initialized command history has a nonempty, bounded,
completely initialized resident image and both actual candidate responses.
-/
theorem initialized_resident (s : State) (i : Values Reactive.Input)
    (hi : i .initialize = 1) (loading : List (Values Reactive.Input))
    (hv : (run (s.step i) Ledger.initial loading).1.registers (.core .valid) = 1) :
    let after := run (s.step i) Ledger.initial loading
    (0 < (after.1.registers (.core .count)).toNat ∧
      (after.1.registers (.core .count)).toNat ≤ 64) ∧
      SramExecution.Resident after.1 after.2.rows after.2.dictionaryWords ∧
      SramExecution.Ready after.1 after.2.rows :=
  ⟨(initialized_established s i hi loading).count hv,
    (initialized_established s i hi loading).resident hv,
    initialized_ready s i hi loading hv⟩

/-- Initialized loading establishes the image and Q premises of the universal
runtime theorem. The full-register reference starts with the actual cut's core
state and the independently tracked accepted image, then evolves independently.
Every permitted runtime prefix has the same complete reference state.
-/
theorem initialized_to_execution (s : State) (i : Values Reactive.Input)
    (hi : i .initialize = 1) (loading runtime : List (Values Reactive.Input))
    (hv : (run (s.step i) Ledger.initial loading).1.registers (.core .valid) = 1)
    (hr : ∀ j ∈ runtime, SramExecution.ExecutingInput j) :
    let after := run (s.step i) Ledger.initial loading
    @SramExecution.reference (after.1.run runtime) after.2.rows after.2.dictionaryWords =
      @SramExecution.reactiveRun
        (SramExecution.reference after.1 after.2.rows after.2.dictionaryWords) runtime :=
  SramExecution.runtime_run (run (s.step i) Ledger.initial loading).1 runtime
    (run (s.step i) Ledger.initial loading).2.rows
    (run (s.step i) Ledger.initial loading).2.dictionaryWords
    (initialized_resident s i hi loading hv).2.1
    (initialized_resident s i hi loading hv).2.2 hr

/-- All public observations, including TX/RX prefixes, retained outcome and
owner counters, agree after every initialized fixed-image runtime prefix.
-/
theorem initialized_to_execution_observe (s : State) (i : Values Reactive.Input)
    (hi : i .initialize = 1) (loading runtime : List (Values Reactive.Input))
    (hv : (run (s.step i) Ledger.initial loading).1.registers (.core .valid) = 1)
    (hr : ∀ j ∈ runtime, SramExecution.ExecutingInput j)
    (query : Values Reactive.Input) (hq : SharedBranches.Runtime query)
    (o : Reactive.Output w) :
    let after := run (s.step i) Ledger.initial loading
    (after.1.run runtime).observe query o =
      Reactive.circuit.observe query
        (SramExecution.reactiveRun
          (SramExecution.reference after.1 after.2.rows after.2.dictionaryWords) runtime) o :=
  SramExecution.observe_run (run (s.step i) Ledger.initial loading).1 runtime
    (run (s.step i) Ledger.initial loading).2.rows
    (run (s.step i) Ledger.initial loading).2.dictionaryWords
    (initialized_resident s i hi loading hv).2.1
    (initialized_resident s i hi loading hv).2.2 hr query hq o

end Pinwheel.Hardware.Buffered.SramCorrespondence
