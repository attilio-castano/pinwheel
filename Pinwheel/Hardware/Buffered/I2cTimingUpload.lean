import Pinwheel.Hardware.Buffered.I2cTimingLoading
import Pinwheel.Hardware.Buffered.I2cUploadAdequacy

/-! Concrete accepted uploads for every duration/budget pair. Retiming changes
instruction data, while the loader's idle admission and coverage laws are
independent of that data. VALID is derived rather than assumed. -/
namespace Pinwheel.Hardware.Buffered.I2cTiming.Upload
open Pinwheel.Hardware I2cCanonicalUpload
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def rowInput (duration budget : Fin 256) (k : BitVec 6) : Values Reactive.Input
  | _, .word => I2cTiming.word duration budget k
  | _, p => I2cCanonicalUpload.rowInput k p

def rowRun (duration budget : Fin 256) (s : SramState.State) : Nat → SramState.State
  | 0 => s
  | n + 1 => (rowRun duration budget s n).step (rowInput duration budget (BitVec.ofNat 6 n))

def rows (duration budget : Fin 256) : List (Values Reactive.Input) :=
  (List.finRange 50).map fun k => @rowInput duration budget (BitVec.ofNat 6 k.val)

def loading (duration budget : Fin 256) : List (Values Reactive.Input) :=
  tables ++ rows duration budget ++ [@commitInput]

theorem row_loader (duration budget : Fin 256) (k : BitVec 6) :
    LifecycleUpload.Input (rowInput duration budget k) :=
  ⟨rfl, by simp [rowInput, I2cCanonicalUpload.rowInput],
    by simp [rowInput, I2cCanonicalUpload.rowInput]⟩

theorem row_writing (duration budget : Fin 256) (s : SramState.State) (k : BitVec 6)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0) :
    SramCoverage.writing.eval (s.inputs (rowInput duration budget k)) s.registers = 1 ∧
      Sram.rowWriting.eval (s.inputs (rowInput duration budget k)) s.registers = 1 := by
  exact I2cCanonicalUpload.row_writing s k phase retained

structure Rows (duration budget : Fin 256) (s : SramState.State) (n : Nat) : Prop where
  phase : (rowRun duration budget s n).core .phase = 0
  retained : (rowRun duration budget s n).core .retained = 0
  pending : (rowRun duration budget s n).core .pending = 1
  covered : ∀ k : Fin 64, k.val < n → ((rowRun duration budget s n).core .written).getLsbD k.val = true
  dictionary : ∀ k : Fin 16, ((rowRun duration budget s n).registers .branchWritten).getLsbD k.val = true
  generation : (rowRun duration budget s n).core .generation = s.core .generation

theorem rows_run (duration budget : Fin 256) (s : SramState.State) (n : Nat)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0) (pending : s.core .pending = 1)
    (dictionary : ∀ k : Fin 16, (s.registers .branchWritten).getLsbD k.val = true) :
    Rows duration budget s n := by
  induction n
  case zero => exact ⟨phase, retained, pending, by intro k impossible; omega, dictionary, rfl⟩
  case succ n ih =>
    have input := row_loader duration budget (BitVec.ofNat 6 n)
    have reset := reset_zero (rowRun duration budget s n)
      (rowInput duration budget (BitVec.ofNat 6 n)) rfl input.warm
    have writing := row_writing duration budget _ (BitVec.ofNat 6 n) ih.phase ih.retained
    have commit := no_commit (rowRun duration budget s n)
      (rowInput duration budget (BitVec.ofNat 6 n)) (by simp [rowInput, I2cCanonicalUpload.rowInput])
    have idle := LifecycleUpload.idle_step (rowRun duration budget s n)
      (rowInput duration budget (BitVec.ofNat 6 n)) input ih.phase ih.retained
    refine ⟨idle.1, idle.2, write_pending _ _ reset writing.1 commit, ?_, ?_, ?_⟩
    · intro k within
      change (((rowRun duration budget s n).step
        (rowInput duration budget (BitVec.ofNat 6 n))).core .written).getLsbD k.val = true
      by_cases same : k.val = n
      · exact written_here _ _ reset writing.1 writing.2 k
          (by change BitVec.ofNat 6 n = BitVec.ofNat 6 k.val; rw [same])
      · exact written_keep _ _ reset writing.1 ih.pending k (ih.covered k (by omega))
    · intro k
      exact table_keep _ _ reset writing.1 ih.pending k (ih.dictionary k)
    · exact (no_commit_generation _ _ rfl input.warm commit).trans ih.generation

theorem rowRun_eq (duration budget : Fin 256) (s : SramState.State) (n : Nat) :
    rowRun duration budget s n = s.run
      ((List.finRange n).map fun k => @rowInput duration budget (BitVec.ofNat 6 k.val)) := by
  induction n
  case zero => rfl
  case succ n ih =>
    simp only [rowRun, ih, List.finRange_succ_last, List.map_append, List.map_map,
      List.map_cons, List.map_nil, SramState.State.run, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    rfl

def written (duration budget : Fin 256) (s : SramState.State) : SramState.State :=
  rowRun duration budget (tableRun s 16) 50

theorem loading_eq (duration budget : Fin 256) (s : SramState.State) :
    s.run (loading duration budget) = (written duration budget s).step commitInput := by
  unfold written
  rw [rowRun_eq, tableRun_eq]
  simp [loading, tables, rows, SramState.State.run, List.foldl_append]

theorem loading_valid (duration budget : Fin 256) (s : SramState.State)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0)
    (space : s.core .generation ≠ 65535) :
    (s.run (loading duration budget)).core .valid = 1 := by
  have table := tables_run s 16 phase retained
  have row := rows_run duration budget (tableRun s 16) 50 table.phase table.retained
    (table.pending (by decide)) (fun k => table.covered k k.isLt)
  have accepted := commit_accepted _ row.phase row.retained row.pending
    (by rw [row.generation, table.generation]; exact space) row.covered (dictionary_full _ row.dictionary)
  rw [loading_eq]
  exact commit_valid _ accepted

private theorem no_row (s : SramState.State) (i : Values Reactive.Input)
    (command : i .command ≠ 1#3) : SramLoading.rowAccepted s i = false := by
  simp [SramLoading.rowAccepted, Sram.rowWriting, SramCoverage.control_correct,
    SharedBranches.rowWriting, SharedBranches.both, SharedBranches.cmd, Expr.eval,
    SramCoverage.baseInput, SramState.State.inputs, command]

private theorem no_table (s : SramState.State) (i : Values Reactive.Input)
    (command : i .command ≠ 6#3) : SramLoading.tableAccepted s i = false := by
  simp [SramLoading.tableAccepted, Sram.tableWriting, SramCoverage.control_correct,
    SharedBranches.tableWriting, SharedBranches.both, SharedBranches.cmd, Expr.eval,
    SramCoverage.baseInput, SramState.State.inputs, command]

theorem table_source (duration budget : Fin 256) (s : SramState.State) (k : BitVec 4) :
    Loading.SourceInput duration budget s (tableInput k) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [no_row s (tableInput k) (by simp [tableInput])]
  · intro _
    change I2cSource.dictionary k = I2cSource.dictionary ((0#2 ++ k).extractLsb' 0 4)
    rw [BitVec.extractLsb'_append_eq_right]
  · rw [no_commit s (tableInput k) (by simp [tableInput])]
    intro impossible
    contradiction

theorem row_source (duration budget : Fin 256) (s : SramState.State) (k : BitVec 6) :
    Loading.SourceInput duration budget s (rowInput duration budget k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro _
    exact ⟨rfl, rfl, BitVec.extractLsb'_append_eq_right⟩
  · simp [no_table s (rowInput duration budget k) (by simp [rowInput, I2cCanonicalUpload.rowInput])]
  · rw [no_commit s (rowInput duration budget k) (by simp [rowInput, I2cCanonicalUpload.rowInput])]
    intro impossible
    contradiction

theorem commit_source (duration budget : Fin 256) (s : SramState.State) :
    Loading.SourceInput duration budget s commitInput := by
  refine ⟨?_, ?_, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  · simp [no_row s commitInput (by simp [commitInput])]
  · simp [no_table s commitInput (by simp [commitInput])]

private theorem history_of_members (duration budget : Fin 256) (s : SramState.State)
    (inputs : List (Values Reactive.Input))
    (all : ∀ i ∈ inputs, ∀ actual, Loading.SourceInput duration budget actual i) :
    Loading.SourceHistory duration budget s inputs := by
  induction inputs generalizing s
  case nil => trivial
  case cons i rest ih =>
    exact ⟨all i (by simp) s, ih (s.step i)
      (fun j member => all j (List.mem_cons.mpr (Or.inr member)))⟩

theorem source_history (duration budget : Fin 256) (s : SramState.State) :
    Loading.SourceHistory duration budget s (loading duration budget) := by
  apply history_of_members
  intro i member actual
  rcases List.mem_append.mp member with first | last
  · rcases List.mem_append.mp first with table | row
    · obtain ⟨k, _, eq⟩ := List.mem_map.mp table
      subst i
      exact table_source duration budget actual _
    · obtain ⟨k, _, eq⟩ := List.mem_map.mp row
      subst i
      exact row_source duration budget actual _
  · have eq : @i = @commitInput := by simpa using last
    subst i
    exact commit_source duration budget actual

theorem cold_installed (duration budget : Fin 256) (s : SramState.State)
    (reset : Values Reactive.Input) (cold : reset .initialize = 1) :
    Refinement.InstalledSram (source duration budget) (layout duration budget)
      ((s.step reset).run (loading duration budget)) := by
  have resetting : Reactive.resetting.eval reset s.core = 1 := by
    simp [Reactive.resetting, Reactive.cold, Reactive.either, Expr.eval, cold]
  have ownership := Lifecycle.reset_ownership s reset resetting
  have generation := (Lifecycle.cold_counters s reset cold).1
  have valid := loading_valid duration budget (s.step reset) ownership.2.2 ownership.2.1 (by simp [generation])
  have installed := Loading.initialized_installed duration budget s reset cold (loading duration budget)
    (source_history duration budget (s.step reset))
  rw [I2cReloadSession.loading_run] at installed
  exact installed valid

theorem reset_installed (duration budget : Fin 256) (s : SramState.State)
    (reset : Values Reactive.Input) (resetting : Reactive.resetting.eval reset s.core = 1)
    (inputs : List (Values Reactive.Input))
    (history : Loading.SourceHistory duration budget (s.step reset) inputs)
    (valid : ((s.step reset).run inputs).core .valid = 1) :
    Refinement.InstalledSram (source duration budget) (layout duration budget)
      ((s.step reset).run inputs) := by
  let after := SramLoading.run (s.step reset) SramLoading.Ledger.initial inputs
  have oldValid := (Lifecycle.reset_ownership s reset resetting).1
  have initial : Loading.WhenValid (s.step reset) := by
    intro asserted
    exact False.elim ((by decide : (0 : BitVec 1) ≠ 1) (oldValid.symm.trans asserted))
  have actualValid : after.1.registers (.core .valid) = 1 := by
    rw [I2cReloadSession.loading_run]
    exact valid
  have established := SramCorrespondence.established_run inputs (s.step reset)
    SramLoading.Ledger.initial (SramResetLoading.established_reset s reset resetting)
  have ready := SramCorrespondence.ready_run inputs (s.step reset) SramLoading.Ledger.initial
    (SramResetLoading.established_reset s reset resetting)
    (SramResetLoading.ready_reset s reset resetting) actualValid
  have geometry := Loading.geometry_run duration budget (s.step reset)
    SramLoading.Ledger.initial inputs initial history actualValid
  have known := Loading.known_run duration budget (s.step reset) SramLoading.Ledger.initial
    inputs (Loading.known_initial duration budget) history
  have count : after.1.registers (.core .count) = 50 := geometry.count
  have reference : @SramExecution.reference after.1 after.2.rows after.2.dictionaryWords =
      @SramExecution.withWords after.1.core (fullWords duration budget) := by
    unfold SramExecution.reference
    rw [count, Loading.resident_source_words duration budget after.1 after.2
      known established actualValid count]
    rfl
  have installed : Refinement.InstalledSram (source duration budget) (layout duration budget) after.1 := by
    refine ⟨after.2.rows, after.2.dictionaryWords, established.resident actualValid, ready, ?_, actualValid⟩
    rw [reference]
    exact ⟨geometry.count, geometry.virtualSpan, geometry.idleLevels, geometry.idleEnabled, fun _ => rfl⟩
  rw [I2cReloadSession.loading_run] at installed
  exact installed

theorem warm_installed (duration budget : Fin 256) (s : SramState.State)
    (reset : Values Reactive.Input) (cold : reset .initialize = 0) (warm : reset .command = 7)
    (space : (s.core .generation).toNat ≤ 65533) :
    Refinement.InstalledSram (source duration budget) (layout duration budget)
      ((s.step reset).run (loading duration budget)) := by
  have resetting : Reactive.resetting.eval reset s.core = 1 := by
    simp [Reactive.resetting, Reactive.cold, Reactive.warm, Reactive.both,
      Reactive.either, Reactive.cmd, Expr.eval, cold, warm]
  have ownership := Lifecycle.reset_ownership s reset resetting
  exact reset_installed duration budget s reset resetting (loading duration budget)
    (source_history duration budget _) (loading_valid duration budget (s.step reset)
      ownership.2.2 ownership.2.1 (warm_space s reset cold warm space))

end Pinwheel.Hardware.Buffered.I2cTiming.Upload
