import Pinwheel.Hardware.Buffered.SramExecutionSupport

/-! Actual SRAM resident-image selection and execution correspondence. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Pinwheel.Hardware.Buffered.SramExecution
open Pinwheel.Hardware

def selectedShared (i : Values Sram.Input) (s : Values Sram.Register) :
    Values SharedBranches.Register := fun r => (Sram.registerExpr r).eval i s

def controlShared (i : Values Sram.Input) (s : Values Sram.Register) :
    Values SharedBranches.Register := fun r => (Sram.controlRegister r).eval i s

def core (s : Values Sram.Register) : Values Reactive.Register := fun r => s (.core r)

theorem base_inputs (state : SramState.State) (i : Values Reactive.Input) :
    (fun {w} (p : Reactive.Input w) => state.inputs i (.base p)) = @i := by
  funext w p
  rfl
  done

def selectedWords (i : Values Sram.Input) (s : Values Sram.Register) : Memory.Contents 6 144 :=
  fun k => SharedBranches.expandState (selectedShared i s) (.word k)

def controlWords (i : Values Sram.Input) (s : Values Sram.Register) : Memory.Contents 6 144 :=
  fun k => SharedBranches.expandState (controlShared i s) (.word k)

theorem selected_expand (i : Values Sram.Input) (s : Values Sram.Register) :
    @SharedBranches.expandState (selectedShared i s) = @withWords (core s) (selectedWords i s) := by
  funext w r
  cases r <;> rfl
  done

theorem control_expand (i : Values Sram.Input) (s : Values Sram.Register) :
    @SharedBranches.expandState (controlShared i s) = @withWords (core s) (controlWords i s) := by
  funext w r
  cases r <;> rfl
  done

theorem adapt_correct (e : SharedBranches.E w) (i : Values Sram.Input)
    (s : Values Sram.Register) :
    (Sram.adapt e).eval i s = e.eval (fun p => i (.base p)) (selectedShared i s) := by
  simp only [Sram.adapt, MemoBind.eval_bind, Expr.eval]
  rfl
  done

theorem control_correct (e : SharedBranches.E w) (i : Values Sram.Input)
    (s : Values Sram.Register) :
    (Sram.control e).eval i s = e.eval (fun p => i (.base p)) (controlShared i s) := by
  simp only [Sram.control, MemoBind.eval_bind, Expr.eval]
  rfl
  done

theorem mappedInput_same (i : Values Sram.Input) (s : Values Sram.Register) :
    @SharedBranches.mappedInput (fun p => i (.base p)) (selectedShared i s) =
      @SharedBranches.mappedInput (fun p => i (.base p)) (controlShared i s) := by
  funext w p
  cases p <;> rfl
  done

theorem scalar_valid_withWords (i : Values Reactive.Input) (s : Values Reactive.Register)
    (words : Memory.Contents 6 144) :
    (Reactive.next .valid).eval i (withWords s words) = (Reactive.next .valid).eval i s := rfl

theorem scalar_count_withWords (i : Values Reactive.Input) (s : Values Reactive.Register)
    (words : Memory.Contents 6 144) :
    (Reactive.next .count).eval i (withWords s words) = (Reactive.next .count).eval i s := rfl

theorem scalar_valid_controlled (i : Values Sram.Input) (s : Values Sram.Register) :
    (Sram.adapt (SharedBranches.adapt (Reactive.next .valid))).eval i s =
      (Sram.control (SharedBranches.adapt (Reactive.next .valid))).eval i s := by
  rw [adapt_correct, control_correct, SharedBranches.adapt_correct,
    SharedBranches.adapt_correct, selected_expand, control_expand,
    scalar_valid_withWords, scalar_valid_withWords]
  exact congrArg (fun input : Values Reactive.Input => (Reactive.next .valid).eval input (core s))
    (mappedInput_same i s)
  done

theorem scalar_count_controlled (i : Values Sram.Input) (s : Values Sram.Register) :
    (Sram.adapt (SharedBranches.adapt (Reactive.next .count))).eval i s =
      (Sram.control (SharedBranches.adapt (Reactive.next .count))).eval i s := by
  rw [adapt_correct, control_correct, SharedBranches.adapt_correct,
    SharedBranches.adapt_correct, selected_expand, control_expand,
    scalar_count_withWords, scalar_count_withWords]
  exact congrArg (fun input : Values Reactive.Input => (Reactive.next .count).eval input (core s))
    (mappedInput_same i s)
  done


theorem adapted_runtime (e : Reactive.E w) (i : Values Sram.Input)
    (s : Values Sram.Register) (h : SharedBranches.Runtime (fun p => i (.base p))) :
    (Sram.adapt (SharedBranches.adapt e)).eval i s =
      e.eval (fun p => i (.base p)) (withWords (core s) (selectedWords i s)) := by
  rw [adapt_correct, SharedBranches.adapt_correct,
    SharedBranches.mappedInput_runtime _ _ h, selected_expand]
  done

theorem controlled_runtime (e : Reactive.E w) (i : Values Sram.Input)
    (s : Values Sram.Register) (h : SharedBranches.Runtime (fun p => i (.base p))) :
    (Sram.control (SharedBranches.adapt e)).eval i s =
      e.eval (fun p => i (.base p)) (withWords (core s) (controlWords i s)) := by
  rw [control_correct, SharedBranches.adapt_correct,
    SharedBranches.mappedInput_runtime _ _ h, control_expand]
  done

theorem starting_runtime (i : Values Sram.Input) (s : Values Sram.Register)
    (h : SharedBranches.Runtime (fun p => i (.base p))) :
    Sram.starting.eval i s = Reactive.starting.eval (fun p => i (.base p)) (core s) :=
  (controlled_runtime Reactive.starting i s h).trans (starting_withWords _ _ _)

theorem entryPC_runtime (i : Values Sram.Input) (s : Values Sram.Register)
    (h : SharedBranches.Runtime (fun p => i (.base p))) :
    Sram.entryPC.eval i s = Reactive.entryPC.eval (fun p => i (.base p)) (core s) :=
  (controlled_runtime Reactive.entryPC i s h).trans (entryPC_withWords _ _ _)

theorem branchDecision_runtime (i : Values Sram.Input) (s : Values Sram.Register)
    (h : SharedBranches.Runtime (fun p => i (.base p))) :
    Sram.branchDecision.eval i s = Reactive.branchBit.eval (fun p => i (.base p)) (core s) :=
  (controlled_runtime Reactive.branchBit i s h).trans (branchBit_withWords _ _ _)

def live (count : BitVec 7) (k : BitVec 6) : Bool := decide (k.toNat < count.toNat)

def projectedRow (count : BitVec 7) (rows : Memory.Contents 6 92) (k : BitVec 6) : BitVec 92 :=
  SramCandidates.project (live count k) (rows k)

def residentWords (count : BitVec 7) (rows : Memory.Contents 6 92)
    (dictionary : Memory.Contents 4 56) : Memory.Contents 6 144 := fun k =>
  dictionary ((projectedRow count rows k).extractLsb' 88 4) ++
    (projectedRow count rows k).extractLsb' 0 88

def candidateAddress (s : Values Sram.Register) (b : Bool) : BitVec 6 :=
  ((SramCandidates.candidate b).eval (fun _ => 0) (core s)).extractLsb' 0 6

def candidateAddresses (s : Values Sram.Register) : Fin 2 → BitVec 6 :=
  fun port => candidateAddress s (decide (port = 1))

def Ready (state : SramState.State) (rows : Memory.Contents 6 92) : Prop :=
  SramCandidates.Ready state.arrays (fun k => (rows k).extractLsb' 0 64)
    (live (state.registers (.core .count))) (candidateAddresses state.registers)

def Resident (state : SramState.State) (rows : Memory.Contents 6 92)
    (dictionary : Memory.Contents 4 56) : Prop :=
  (∀ k, live (state.registers (.core .count)) k = true →
    state.registers (.metadata k) = (rows k).extractLsb' 64 28) ∧
  (∀ k, state.registers (.branch k) = dictionary k) ∧
  (∀ port k, live (state.registers (.core .count)) k = true →
    (state.arrays port).contents k = (rows k).extractLsb' 0 64) ∧
  (live (state.registers (.core .count)) 0 = true →
    state.registers .startWord = (rows 0).extractLsb' 0 64)

private theorem bit_cases (v : BitVec 1) : v = 0 ∨ v = 1 := by bv_omega

private theorem band_zero_left : ∀ value : BitVec 1, (0 : BitVec 1) &&& value = 0 := by
  decide +kernel

private theorem port_bool (b : Bool) : decide (SramState.port b = 1) = b := by
  cases b <;> decide

theorem ready_at (state : SramState.State) (rows : Memory.Contents 6 92)
    (h : Ready state rows) (b : Bool) :
    SramCandidates.project (live (state.registers (.core .count))
      (candidateAddress state.registers b)) (state.arrays (SramState.port b)).q =
    SramCandidates.project (live (state.registers (.core .count))
      (candidateAddress state.registers b))
      ((rows (candidateAddress state.registers b)).extractLsb' 0 64) := by
  simpa only [Ready, SramCandidates.Ready, candidateAddresses, port_bool] using
    h (SramState.port b)
  done

def entryAddress (s : Values Sram.Register) (i : Values Reactive.Input) : BitVec 6 :=
  (Reactive.entryPC.eval i (core s)).extractLsb' 0 6

theorem entering_runtime (i : Values Sram.Input) (s : Values Sram.Register)
    (h : SharedBranches.Runtime (fun p => i (.base p))) :
    (Sram.adapt (SharedBranches.adapt Reactive.entering)).eval i s =
      Reactive.entering.eval (fun p => i (.base p)) (core s) :=
  (adapted_runtime Reactive.entering i s h).trans (entering_withWords _ _ _)

theorem entryAddress_start (state : SramState.State) (i : Values Reactive.Input)
    (hr : SharedBranches.Runtime i) (hs : Sram.starting.eval (state.inputs i) state.registers = 1) :
    entryAddress state.registers i = 0 := by
  have ht := starting_runtime (state.inputs i) state.registers hr
  have he := SramCandidates.start_entry_pc i (core state.registers) (ht.symm.trans hs)
  exact congrArg (fun pc : BitVec 7 => pc.extractLsb' 0 6) he
  done

theorem entryAddress_dispatch (state : SramState.State) (i : Values Reactive.Input)
    (hr : SharedBranches.Runtime i)
    (he : Reactive.entering.eval i (core state.registers) = 1)
    (hs : Sram.starting.eval (state.inputs i) state.registers = 0) :
    entryAddress state.registers i = candidateAddress state.registers
      (decide (Sram.branchDecision.eval (state.inputs i) state.registers = 1)) := by
  have ht := starting_runtime (state.inputs i) state.registers hr
  have hp := SramCandidates.actual_entry_pc i (core state.registers) he (ht.symm.trans hs)
  dsimp only [entryAddress, candidateAddress]
  rw [hp, SramCandidates.chosen_candidate,
    branchDecision_runtime (state.inputs i) state.registers hr]
  exact congrArg (fun pc : BitVec 7 => pc.extractLsb' 0 6)
    (SramCandidates.candidate_input_independent _ i (fun _ => 0) (core state.registers))
  done

theorem instruction_dispatch (state : SramState.State) (i : Values Reactive.Input)
    (hs : Sram.starting.eval (state.inputs i) state.registers = 0) :
    Sram.instruction.eval (state.inputs i) state.registers =
      (state.arrays (SramState.port
        (decide (Sram.branchDecision.eval (state.inputs i) state.registers = 1)))).q := by
  by_cases hb : Sram.branchDecision.eval (state.inputs i) state.registers = 1
  all_goals simp only [Sram.instruction, Expr.eval, hs,
    show (0 : BitVec 1) ≠ 1 from by decide, hb, decide_true, decide_false,
    SramState.State.inputs, ↓reduceIte]
  done

theorem instruction_selected (state : SramState.State) (i : Values Reactive.Input)
    (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56)
    (hr : SharedBranches.Runtime i) (hresident : Resident state rows dictionary)
    (hready : Ready state rows) (he : Reactive.entering.eval i (core state.registers) = 1) :
    SramCandidates.project (live (state.registers (.core .count)) (entryAddress state.registers i))
      (Sram.instruction.eval (state.inputs i) state.registers) =
    SramCandidates.project (live (state.registers (.core .count)) (entryAddress state.registers i))
      ((rows (entryAddress state.registers i)).extractLsb' 0 64) := by
  rcases bit_cases (Sram.starting.eval (state.inputs i) state.registers) with hs | hs
  · rw [entryAddress_dispatch state i hr he hs, instruction_dispatch state i hs]
    exact ready_at state rows hready _
  · rw [entryAddress_start state i hr hs, Sram.instruction_start _ _ hs]
    cases hl : live (state.registers (.core .count)) 0
    · simp only [SramCandidates.project, Bool.false_eq_true, ↓reduceIte]
    · simp only [SramCandidates.project, ↓reduceIte, hresident.2.2.2 hl]
  done

theorem selected_row (state : SramState.State) (i : Values Reactive.Input)
    (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56)
    (hr : SharedBranches.Runtime i) (hresident : Resident state rows dictionary)
    (hready : Ready state rows) (he : Reactive.entering.eval i (core state.registers) = 1) :
    (Sram.rowExpr (entryAddress state.registers i)).eval (state.inputs i) state.registers =
      projectedRow (state.registers (.core .count)) rows (entryAddress state.registers i) := by
  by_cases hl : (entryAddress state.registers i).toNat < (state.registers (.core .count)).toNat
  · have hbool : live (state.registers (.core .count)) (entryAddress state.registers i) = true :=
      by simp only [live, hl, decide_true]
    have hi := instruction_selected state i rows dictionary hr hresident hready he
    simp only [SramCandidates.project, hbool, ↓reduceIte] at hi
    rw [Sram.rowExpr_live _ _ _ hl, hresident.1 _ hbool, hi]
    simpa only [projectedRow, SramCandidates.project, hbool, ↓reduceIte] using
      (BitVec.extractLsb'_append_extractLsb' (x := rows (entryAddress state.registers i))
        (w := 28) (len := 64))
  · rw [Sram.rowExpr_tail _ _ _ (Nat.le_of_not_gt hl)]
    simp only [projectedRow, live, hl, decide_false, SramCandidates.project,
      Bool.false_eq_true, ↓reduceIte]
  done

theorem selected_word (state : SramState.State) (i : Values Reactive.Input)
    (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56)
    (hr : SharedBranches.Runtime i) (hresident : Resident state rows dictionary)
    (hready : Ready state rows) (he : Reactive.entering.eval i (core state.registers) = 1) :
    selectedWords (state.inputs i) state.registers (entryAddress state.registers i) =
      residentWords (state.registers (.core .count)) rows dictionary (entryAddress state.registers i) := by
  simp only [selectedWords, SharedBranches.expandState, selectedShared,
    Sram.registerExpr, Expr.eval]
  rw [selected_row state i rows dictionary hr hresident hready he]
  exact congrArg (fun branch : BitVec 56 => branch ++
    (projectedRow (state.registers (.core .count)) rows (entryAddress state.registers i)).extractLsb' 0 88)
    (hresident.2.1 _)
  done

theorem entryRecord_eq (state : SramState.State) (i : Values Reactive.Input)
    (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56)
    (hr : SharedBranches.Runtime i) (hresident : Resident state rows dictionary)
    (hready : Ready state rows) :
    (Sram.adapt (SharedBranches.adapt Reactive.entryRecord)).eval (state.inputs i) state.registers =
      Reactive.entryRecord.eval i (withWords (core state.registers)
        (residentWords (state.registers (.core .count)) rows dictionary)) := by
  rw [adapted_runtime _ _ _ hr, base_inputs]
  by_cases he : Reactive.entering.eval i (core state.registers) = 1
  · simpa only [Reactive.entryRecord, Expr.eval, entering_withWords, entryPC_withWords,
      he, ↓reduceIte, Execution.readTree_correct, withWords, entryAddress] using
      selected_word state i rows dictionary hr hresident hready he
  · simp only [Reactive.entryRecord, Expr.eval, entering_withWords, he, ↓reduceIte]
  done

theorem scalar_written_withWords (i : Values Reactive.Input) (s : Values Reactive.Register)
    (words : Memory.Contents 6 144) :
    (Reactive.next .written).eval i (withWords s words) =
      (Reactive.next .written).eval i s := rfl

theorem coreNext_runtime (i : Values Sram.Input) (s : Values Sram.Register)
    (hr : SharedBranches.Runtime (fun p => i (.base p))) (r : Reactive.Register w)
    (hn : nonword r) :
    (Sram.coreNext r).eval i s =
      (Reactive.next r).eval (fun p => i (.base p)) (withWords (core s) (selectedWords i s)) := by
  cases r
  case word k => exact False.elim hn
  case written =>
    rw [Sram.coreNext, Sram.next_written, control_correct]
    have ht := congrArg (fun values : Values Reactive.Register => values .written)
      (SharedBranches.step_runtime (fun p => i (.base p)) (controlShared i s) hr)
    change SharedBranches.rowWrittenNext.eval (fun p => i (.base p)) (controlShared i s) =
      (Reactive.next .written).eval (fun p => i (.base p))
        (SharedBranches.expandState (controlShared i s)) at ht
    rw [control_expand, scalar_written_withWords] at ht
    rw [scalar_written_withWords]
    exact ht
  all_goals exact adapted_runtime _ i s hr
  done

theorem step_eq (state : SramState.State) (i : Values Reactive.Input)
    (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56)
    (hr : SharedBranches.Runtime i) (hresident : Resident state rows dictionary)
    (hready : Ready state rows) (r : Reactive.Register w) (hn : nonword r) :
    (state.step i).registers (.core r) =
      Reactive.circuit.step i (withWords (core state.registers)
        (residentWords (state.registers (.core .count)) rows dictionary)) r := by
  change (Sram.coreNext r).eval (state.inputs i) state.registers = _
  rw [coreNext_runtime _ _ hr r hn, base_inputs]
  have he := entryRecord_eq state i rows dictionary hr hresident hready
  rw [adapted_runtime _ _ _ hr, base_inputs] at he
  exact reactive_next_congr i (core state.registers) _ _ he r hn
  done

theorem observe_eq (state : SramState.State) (i : Values Reactive.Input)
    (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56)
    (hr : SharedBranches.Runtime i) (hresident : Resident state rows dictionary)
    (hready : Ready state rows) (o : Reactive.Output w) :
    state.observe i o = Reactive.circuit.observe i (withWords (core state.registers)
      (residentWords (state.registers (.core .count)) rows dictionary)) o := by
  change (Sram.adapt (SharedBranches.output o)).eval (state.inputs i) state.registers = _
  rw [adapt_correct, base_inputs]
  change SharedBranches.circuit.observe i (selectedShared (state.inputs i) state.registers) o = _
  rw [SharedBranches.observe_runtime _ _ hr, selected_expand]
  have he := entryRecord_eq state i rows dictionary hr hresident hready
  rw [adapted_runtime _ _ _ hr, base_inputs] at he
  exact reactive_observe_congr i (core state.registers) _ _ he o
  done

/-- One actual nonwrite edge establishes both prospective candidate responses.
The premise concerns initialized words needed by the post-edge resident count;
it does not assume pre-edge Q availability. -/
theorem ready_renewed (state : SramState.State) (i : Values Reactive.Input)
    (rows : Memory.Contents 6 92)
    (hw : (Sram.request .write).eval (state.inputs i) state.registers = 0)
    (hbank : ∀ port k, live ((state.step i).registers (.core .count)) k = true →
      (state.arrays port).contents k = (rows k).extractLsb' 0 64) : Ready (state.step i) rows := by
  have ha := Sram.actual_candidate_availability (state.inputs i) state.registers state.arrays
    (fun k => (rows k).extractLsb' 0 64)
    (live ((state.step i).registers (.core .count))) hw hbank
  unfold Ready candidateAddresses candidateAddress core
  intro port
  simpa only [SramState.State.step, Sram.readAddress_correct] using ha port
  done

/-- Resident execution permits polling, START, RELEASE and rejected opcode 5.
Reset and upload/COMMIT/dictionary commands belong to the initialized loader
history, rather than to this fixed-image runtime trace. -/
def ExecutingInput (i : Values Reactive.Input) : Prop :=
  SharedBranches.Runtime i ∧ i .initialize = 0 ∧ i .command ≠ 7#3

theorem rowWriting_runtime (i : Values Sram.Input) (s : Values Sram.Register)
    (hr : SharedBranches.Runtime (fun p => i (.base p))) : Sram.rowWriting.eval i s = 0 := by
  rw [Sram.rowWriting, control_correct]
  simp only [SharedBranches.rowWriting, SharedBranches.both, Expr.eval,
    SharedBranches.writing_runtime _ _ hr]
  simp
  done

theorem tableWriting_runtime (i : Values Sram.Input) (s : Values Sram.Register)
    (hr : SharedBranches.Runtime (fun p => i (.base p))) : Sram.tableWriting.eval i s = 0 := by
  rw [Sram.tableWriting, control_correct]
  simp only [SharedBranches.tableWriting, SharedBranches.both, Expr.eval,
    SharedBranches.writing_runtime _ _ hr]
  simp
  done

theorem committing_runtime (i : Values Sram.Input) (s : Values Sram.Register)
    (hr : SharedBranches.Runtime (fun p => i (.base p))) : Sram.committing.eval i s = 0 := by
  rw [Sram.committing, control_correct]
  exact SharedBranches.committing_runtime _ _ hr
  done

theorem resetting_executing (i : Values Reactive.Input) (s : Values Reactive.Register)
    (hi : ExecutingInput i) : Reactive.resetting.eval i s = 0 := by
  dsimp only [Reactive.resetting, Reactive.either, Reactive.warm, Reactive.cold,
    Reactive.both, Reactive.cmd, Expr.eval]
  by_cases hc : i .command = 7#3
  · exact False.elim (hi.2.2 hc)
  · simp [hi.2.1, hc]
  done

theorem count_executing (state : SramState.State) (i : Values Reactive.Input)
    (hi : ExecutingInput i) :
    (state.step i).registers (.core .count) = state.registers (.core .count) := by
  change (Sram.coreNext .count).eval (state.inputs i) state.registers = _
  rw [coreNext_runtime _ _ hi.1 .count True.intro, base_inputs, scalar_count_withWords]
  have hc : Reactive.committing.eval i (core state.registers) = 0 := by
    simp [Reactive.committing, Reactive.both, Reactive.cmd, Expr.eval, hi.1.2.1]
  simp only [Reactive.next, Expr.eval, resetting_executing _ _ hi, hc,
    show (0 : BitVec 1) ≠ 1 from by decide, ↓reduceIte]
  rfl
  done

theorem resident_executing (state : SramState.State) (i : Values Reactive.Input)
    (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56)
    (hi : ExecutingInput i) (hresident : Resident state rows dictionary) :
    Resident (state.step i) rows dictionary := by
  have hw := rowWriting_runtime (state.inputs i) state.registers hi.1
  have hc := committing_runtime (state.inputs i) state.registers hi.1
  have ht := tableWriting_runtime (state.inputs i) state.registers hi.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hl
    rw [count_executing state i hi] at hl
    simpa [SramState.State.step, Circuit.step, Sram.circuit, Sram.next, Expr.eval, hw, hc]
      using hresident.1 k hl
  · intro k
    simpa [SramState.State.step, Circuit.step, Sram.circuit, Sram.next, Expr.eval, ht]
      using hresident.2.1 k
  · intro port k hl
    rw [count_executing state i hi] at hl
    change (Memory.Sram.step (Sram.arrayRequest (state.inputs i) state.registers)
      state.arrays port).contents k = _
    rw [Sram.array_read_preserves_bank _ _ _ hw port]
    exact hresident.2.2.1 port k hl
  · intro hl
    rw [count_executing state i hi] at hl
    change Sram.circuit.step (state.inputs i) state.registers .startWord = _
    rw [Sram.start_mirror_nonwrite _ _ hw]
    exact hresident.2.2.2 hl
  done

theorem ready_executing (state : SramState.State) (i : Values Reactive.Input)
    (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56)
    (hi : ExecutingInput i) (hresident : Resident state rows dictionary) :
    Ready (state.step i) rows := by
  apply ready_renewed state i rows (rowWriting_runtime _ _ hi.1)
  intro port k hl
  rw [count_executing state i hi] at hl
  exact hresident.2.2.1 port k hl
  done

def reference (state : SramState.State) (rows : Memory.Contents 6 92)
    (dictionary : Memory.Contents 4 56) : Values Reactive.Register :=
  withWords (core state.registers) (residentWords (state.registers (.core .count)) rows dictionary)

theorem reference_core (state : SramState.State) (rows : Memory.Contents 6 92)
    (dictionary : Memory.Contents 4 56) (r : Reactive.Register w) (hn : nonword r) :
    reference state rows dictionary r = state.registers (.core r) := by
  cases r
  case word k => exact False.elim hn
  all_goals rfl
  done

theorem reference_step_eq (state : SramState.State) (i : Values Reactive.Input)
    (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56)
    (hi : ExecutingInput i) (hresident : Resident state rows dictionary)
    (hready : Ready state rows) :
    @reference (state.step i) rows dictionary =
      (fun {w} (r : Reactive.Register w) => Reactive.circuit.step i (reference state rows dictionary) r) := by
  funext w r
  by_cases hn : nonword r
  · rw [reference_core _ _ _ r hn]
    exact step_eq state i rows dictionary hi.1 hresident hready r hn
  · cases r
    case word k =>
      have hw : Reactive.writing.eval i (reference state rows dictionary) = 0 := by
        simp [Reactive.writing, Reactive.both, Reactive.cmd, Expr.eval, hi.1.1]
      have hc : Reactive.committing.eval i (reference state rows dictionary) = 0 := by
        simp [Reactive.committing, Reactive.both, Reactive.cmd, Expr.eval, hi.1.2.1]
      simp only [Circuit.step, Reactive.circuit, Reactive.next, Reactive.both, Expr.eval,
        hw, hc, band_zero_left, show (0 : BitVec 1) ≠ 1 from by decide, ↓reduceIte]
      change residentWords ((state.step i).registers (.core .count)) rows dictionary k =
        residentWords (state.registers (.core .count)) rows dictionary k
      rw [count_executing state i hi]
    all_goals simp only [nonword, not_true_eq_false] at hn
  done

def reactiveRun (s : Values Reactive.Register) (inputs : List (Values Reactive.Input)) :
    Values Reactive.Register :=
  @List.foldl (Values Reactive.Register) (Values Reactive.Input)
    (fun current input => fun {w} (r : Reactive.Register w) => Reactive.circuit.step input current r)
    @s inputs

/-- Every finite fixed-image runtime trace agrees with the full-register
reactive engine, including all loop/cached/sampler/buffer/owner fields. -/
theorem runtime_run (state : SramState.State) (inputs : List (Values Reactive.Input))
    (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56)
    (hresident : Resident state rows dictionary) (hready : Ready state rows)
    (hinputs : ∀ i ∈ inputs, ExecutingInput i) :
    @reference (state.run inputs) rows dictionary =
      @reactiveRun (reference state rows dictionary) inputs := by
  induction inputs generalizing state
  case nil => rfl
  case cons i inputs ih =>
    have hi : ExecutingInput i := hinputs @i (by simp)
    have htail : ∀ j ∈ inputs, ExecutingInput j :=
      fun j hj => hinputs @j (@List.mem_cons_of_mem (Values Reactive.Input) @i @j inputs hj)
    have ht := ih (state.step i) (resident_executing state i rows dictionary hi hresident)
      (ready_executing state i rows dictionary hi hresident) htail
    change @reference ((state.step i).run inputs) rows dictionary =
      @reactiveRun (fun {w} (r : Reactive.Register w) =>
        Reactive.circuit.step i (reference state rows dictionary) r) inputs
    rw [ht, reference_step_eq state i rows dictionary hi hresident hready]
  done

theorem runtime_invariants (state : SramState.State) (inputs : List (Values Reactive.Input))
    (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56)
    (hresident : Resident state rows dictionary) (hready : Ready state rows)
    (hinputs : ∀ i ∈ inputs, ExecutingInput i) :
    Resident (state.run inputs) rows dictionary ∧ Ready (state.run inputs) rows := by
  induction inputs generalizing state
  case nil => exact ⟨hresident, hready⟩
  case cons i inputs ih =>
    have hi : ExecutingInput i := hinputs @i (by simp)
    exact ih (state.step i) (resident_executing state i rows dictionary hi hresident)
      (ready_executing state i rows dictionary hi hresident)
      (fun j hj => hinputs @j (@List.mem_cons_of_mem (Values Reactive.Input) @i @j inputs hj))
  done

/-- Every public observation after every finite runtime prefix agrees. Thus
the state theorem also covers output timing, retained ownership and results. -/
theorem observe_run (state : SramState.State) (inputs : List (Values Reactive.Input))
    (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56)
    (hresident : Resident state rows dictionary) (hready : Ready state rows)
    (hinputs : ∀ i ∈ inputs, ExecutingInput i) (i : Values Reactive.Input)
    (hr : SharedBranches.Runtime i) (o : Reactive.Output w) :
    (state.run inputs).observe i o =
      Reactive.circuit.observe i (reactiveRun (reference state rows dictionary) inputs) o := by
  have hinv := runtime_invariants state inputs rows dictionary hresident hready hinputs
  have ht := observe_eq (state.run inputs) i rows dictionary hr hinv.1 hinv.2 o
  change (state.run inputs).observe i o =
    Reactive.circuit.observe i (reference (state.run inputs) rows dictionary) o at ht
  rw [runtime_run state inputs rows dictionary hresident hready hinputs] at ht
  exact ht
  done

end Pinwheel.Hardware.Buffered.SramExecution
