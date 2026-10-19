import Pinwheel.Hardware.Buffered.I2cUploadMasks

namespace Pinwheel.Hardware.Buffered.I2cCanonicalUpload
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def tableRun (s : SramState.State) : Nat → SramState.State
  | 0 => s
  | n + 1 => (tableRun s n).step (tableInput (BitVec.ofNat 4 n))

def rowRun (s : SramState.State) : Nat → SramState.State
  | 0 => s
  | n + 1 => (rowRun s n).step (rowInput (BitVec.ofNat 6 n))

theorem tableRun_eq (s : SramState.State) (n : Nat) :
    tableRun s n = s.run ((List.finRange n).map fun k => @tableInput (BitVec.ofNat 4 k.val)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tableRun, ih, List.finRange_succ_last, List.map_append, List.map_map,
      List.map_cons, List.map_nil, SramState.State.run, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    rfl
  done

theorem rowRun_eq (s : SramState.State) (n : Nat) :
    rowRun s n = s.run ((List.finRange n).map fun k => @rowInput (BitVec.ofNat 6 k.val)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rowRun, ih, List.finRange_succ_last, List.map_append, List.map_map,
      List.map_cons, List.map_nil, SramState.State.run, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    rfl
  done

theorem table_loader (k : BitVec 4) : LifecycleUpload.Input (tableInput k) :=
  ⟨rfl, by simp [tableInput], by simp [tableInput]⟩

theorem row_loader (k : BitVec 6) : LifecycleUpload.Input (rowInput k) :=
  ⟨rfl, by simp [rowInput], by simp [rowInput]⟩

theorem no_commit_generation (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (warm : i .command ≠ 7#3)
    (commit : Sram.committing.eval (s.inputs i) s.registers = 0) :
    (s.step i).core .generation = s.core .generation := by
  simp [Lifecycle.generation_step, cold, warm, commit]
  done

structure Tables (s : SramState.State) (n : Nat) : Prop where
  phase : (tableRun s n).core .phase = 0
  retained : (tableRun s n).core .retained = 0
  pending : 0 < n → (tableRun s n).core .pending = 1
  covered : ∀ k : Fin 16, k.val < n → ((tableRun s n).registers .branchWritten).getLsbD k.val = true
  generation : (tableRun s n).core .generation = s.core .generation

theorem tables_run (s : SramState.State) (n : Nat)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0) : Tables s n := by
  induction n with
  | zero => exact ⟨phase, retained, by omega, by intro k impossible; omega, rfl⟩
  | succ n ih =>
    have input := table_loader (BitVec.ofNat 4 n)
    have reset := reset_zero (tableRun s n) (tableInput (BitVec.ofNat 4 n)) rfl input.warm
    have writing := table_writing (tableRun s n) (BitVec.ofNat 4 n) ih.phase ih.retained
    have commit := no_commit (tableRun s n) (tableInput (BitVec.ofNat 4 n)) (by simp [tableInput])
    have idle := LifecycleUpload.idle_step (tableRun s n) (tableInput (BitVec.ofNat 4 n)) input ih.phase ih.retained
    refine ⟨idle.1, idle.2, fun _ => write_pending _ _ reset writing.1 commit, ?_, ?_⟩
    · intro k within
      change (((tableRun s n).step (tableInput (BitVec.ofNat 4 n))).registers .branchWritten).getLsbD k.val = true
      by_cases same : k.val = n
      · apply table_here _ _ reset writing.1 writing.2 k
        change (0#2 ++ BitVec.ofNat 4 n).extractLsb' 0 4 = BitVec.ofNat 4 k.val
        rw [BitVec.extractLsb'_append_eq_right, same]
      · have previous : k.val < n := by omega
        exact table_keep _ _ reset writing.1 (ih.pending (by omega)) k (ih.covered k previous)
    · exact (no_commit_generation _ _ rfl input.warm commit).trans ih.generation
  done

structure Rows (s : SramState.State) (n : Nat) : Prop where
  phase : (rowRun s n).core .phase = 0
  retained : (rowRun s n).core .retained = 0
  pending : (rowRun s n).core .pending = 1
  covered : ∀ k : Fin 64, k.val < n → ((rowRun s n).core .written).getLsbD k.val = true
  dictionary : ∀ k : Fin 16, ((rowRun s n).registers .branchWritten).getLsbD k.val = true
  generation : (rowRun s n).core .generation = s.core .generation

theorem rows_run (s : SramState.State) (n : Nat)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0)
    (pending : s.core .pending = 1)
    (dictionary : ∀ k : Fin 16, (s.registers .branchWritten).getLsbD k.val = true) : Rows s n := by
  induction n with
  | zero => exact ⟨phase, retained, pending, by intro k impossible; omega, dictionary, rfl⟩
  | succ n ih =>
    have input := row_loader (BitVec.ofNat 6 n)
    have reset := reset_zero (rowRun s n) (rowInput (BitVec.ofNat 6 n)) rfl input.warm
    have writing := row_writing (rowRun s n) (BitVec.ofNat 6 n) ih.phase ih.retained
    have commit := no_commit (rowRun s n) (rowInput (BitVec.ofNat 6 n)) (by simp [rowInput])
    have idle := LifecycleUpload.idle_step (rowRun s n) (rowInput (BitVec.ofNat 6 n)) input ih.phase ih.retained
    refine ⟨idle.1, idle.2, write_pending _ _ reset writing.1 commit, ?_, ?_, ?_⟩
    · intro k within
      change (((rowRun s n).step (rowInput (BitVec.ofNat 6 n))).core .written).getLsbD k.val = true
      by_cases same : k.val = n
      · exact written_here _ _ reset writing.1 writing.2 k (by change BitVec.ofNat 6 n = BitVec.ofNat 6 k.val; rw [same])
      · have previous : k.val < n := by omega
        exact written_keep _ _ reset writing.1 ih.pending k (ih.covered k previous)
    · intro k
      exact table_keep _ _ reset writing.1 ih.pending k (ih.dictionary k)
    · exact (no_commit_generation _ _ rfl input.warm commit).trans ih.generation
  done

end Pinwheel.Hardware.Buffered.I2cCanonicalUpload
