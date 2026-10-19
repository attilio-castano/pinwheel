import Pinwheel.Hardware.Buffered.SerialUploadControl

namespace Pinwheel.Hardware.Buffered.SerialUpload
open Pinwheel.Hardware I2cCanonicalUpload
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

structure TableProgress (generation : BitVec 16) (n : Nat) (s : SramState.State) : Prop where
  phase : s.core .phase = 0
  retained : s.core .retained = 0
  pending : 0 < n → s.core .pending = 1
  dictionary : ∀ k : Fin 16, k.val < n → (s.registers .branchWritten).getLsbD k.val = true
  generation : s.core .generation = generation

structure RowProgress (generation : BitVec 16) (n : Nat) (s : SramState.State) : Prop where
  phase : s.core .phase = 0
  retained : s.core .retained = 0
  pending : s.core .pending = 1
  dictionary : ∀ k : Fin 16, (s.registers .branchWritten).getLsbD k.val = true
  covered : ∀ k : Fin 64, k.val < n → (s.core .written).getLsbD k.val = true
  generation : s.core .generation = generation

theorem TableProgress.quiet {generation n s} (h : TableProgress generation n s)
    (i : Values Reactive.Input) (quiet : Serial.Frames.Quiet i) :
    TableProgress generation n (s.step i) := by
  have held := quiet_hold s i quiet
  have idle := LifecycleUpload.idle_step s i
    ⟨quiet.1, by simp [quiet.2], by simp [quiet.2]⟩ h.phase h.retained
  exact ⟨idle.1, idle.2, fun positive => held.pending.trans (h.pending positive),
    fun k within => by rw [held.dictionary]; exact h.dictionary k within,
    held.generation.trans h.generation⟩
  done

theorem RowProgress.quiet {generation n s} (h : RowProgress generation n s)
    (i : Values Reactive.Input) (quiet : Serial.Frames.Quiet i) :
    RowProgress generation n (s.step i) := by
  have held := quiet_hold s i quiet
  have idle := LifecycleUpload.idle_step s i
    ⟨quiet.1, by simp [quiet.2], by simp [quiet.2]⟩ h.phase h.retained
  exact ⟨idle.1, idle.2, held.pending.trans h.pending,
    fun k => by rw [held.dictionary]; exact h.dictionary k,
    fun k within => by rw [held.written]; exact h.covered k within,
    held.generation.trans h.generation⟩
  done

theorem TableProgress.write {generation n s} (h : TableProgress generation n s)
    (i : Values Reactive.Input) (input : Table i (BitVec.ofNat 4 n)) :
    TableProgress generation (n+1) (s.step i) := by
  have loader : LifecycleUpload.Input i :=
    ⟨input.cold, by simp [input.command], by simp [input.command]⟩
  have reset := reset_zero s i input.cold loader.warm
  have writing := table_writing s i _ input h.phase h.retained
  have commit := no_commit s i (by simp [input.command])
  have idle := LifecycleUpload.idle_step s i loader h.phase h.retained
  refine ⟨idle.1, idle.2, fun _ => write_pending s i reset writing.1 commit, ?_,
    (no_commit_generation s i input.cold loader.warm commit).trans h.generation⟩
  intro k within
  by_cases same : k.val = n
  · apply table_here s i reset writing.1 writing.2 k
    rw [input.address, BitVec.extractLsb'_append_eq_right, same]
  · exact table_keep s i reset writing.1 (h.pending (by omega)) k (h.dictionary k (by omega))
  done

theorem RowProgress.write {generation n s} (h : RowProgress generation n s)
    (i : Values Reactive.Input) (input : Row i (BitVec.ofNat 6 n)) :
    RowProgress generation (n+1) (s.step i) := by
  have loader : LifecycleUpload.Input i :=
    ⟨input.cold, by simp [input.command], by simp [input.command]⟩
  have reset := reset_zero s i input.cold loader.warm
  have writing := row_writing s i _ input h.phase h.retained
  have commit := no_commit s i (by simp [input.command])
  have idle := LifecycleUpload.idle_step s i loader h.phase h.retained
  refine ⟨idle.1, idle.2, write_pending s i reset writing.1 commit,
    fun k => table_keep s i reset writing.1 h.pending k (h.dictionary k), ?_,
    (no_commit_generation s i input.cold loader.warm commit).trans h.generation⟩
  intro k within
  by_cases same : k.val = n
  · exact written_here s i reset writing.1 writing.2 k (input.address.trans (by rw [same]))
  · exact written_keep s i reset writing.1 h.pending k (h.covered k (by omega))
  done

theorem TableProgress.rows {generation s} (h : TableProgress generation 16 s) :
    RowProgress generation 0 s :=
  ⟨h.phase, h.retained, h.pending (by decide), fun k => h.dictionary k k.isLt,
    by intro k impossible; omega, h.generation⟩

structure Complete (generation : BitVec 16) (s : SramState.State) : Prop where
  phase : s.core .phase = 0
  retained : s.core .retained = 0
  valid : s.core .valid = 1
  generation : (s.core .generation).toNat = generation.toNat + 1

theorem Complete.quiet {generation s} (h : Complete generation s)
    (i : Values Reactive.Input) (quiet : Serial.Frames.Quiet i) : Complete generation (s.step i) := by
  have held := quiet_hold s i quiet
  have idle := LifecycleUpload.idle_step s i
    ⟨quiet.1, by simp [quiet.2], by simp [quiet.2]⟩ h.phase h.retained
  exact ⟨idle.1, idle.2, held.valid.trans h.valid, by rw [held.generation]; exact h.generation⟩
  done

theorem RowProgress.commit {generation s} (h : RowProgress generation 50 s)
    (i : Values Reactive.Input) (input : Commit i) (space : generation ≠ 65535) :
    Complete generation (s.step i) := by
  have loader : LifecycleUpload.Input i :=
    ⟨input.cold, by simp [input.command], by simp [input.command]⟩
  have reset := reset_zero s i input.cold loader.warm
  have accepted := commit_accepted s i input h.phase h.retained h.pending
    (by rw [h.generation]; exact space) h.covered (dictionary_full s h.dictionary)
  have noWriting := SramCoverage.commit_no_writing (s.inputs i) s.registers accepted
  change SramCoverage.writing.eval (s.inputs i) s.registers = 0#1 at noWriting
  have idle := LifecycleUpload.idle_step s i loader h.phase h.retained
  refine ⟨idle.1, idle.2, ?_, ?_⟩
  · change Sram.circuit.step (s.inputs i) s.registers (.core .valid) = 1
    rw [SramCoverage.valid_step]
    simp [reset, noWriting, accepted]
  · rw [Lifecycle.commit_generation_sequence s i accepted, h.generation]
  done

end Pinwheel.Hardware.Buffered.SerialUpload
