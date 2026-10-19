import Pinwheel.Hardware.Buffered.I2cReloadSession

/-! A concrete finite source upload: every shared dictionary entry, every
resident instruction row, then the canonical COMMIT operands. No SRAM contents
or registered responses are supplied by this command sequence. -/
namespace Pinwheel.Hardware.Buffered.I2cCanonicalUpload
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def tableInput (k : BitVec 4) : Values Reactive.Input
  | _, .command => 6
  | _, .address => 0#2 ++ k
  | _, .branch => I2cSource.dictionary k
  | _, _ => 0

def rowInput (k : BitVec 6) : Values Reactive.Input
  | _, .command => 1
  | _, .address => k
  | _, .word => I2cSource.word k
  | _, .control => I2cSource.control k
  | _, .branch => 0#52 ++ I2cSource.branchIndex k
  | _, _ => 0

def commitInput : Values Reactive.Input
  | _, .command => 2
  | _, .count => 50
  | _, .virtualSpan => 270
  | _, _ => 0

def tables : List (Values Reactive.Input) :=
  (List.finRange 16).map fun k => @tableInput (BitVec.ofNat 4 k.val)

def rows : List (Values Reactive.Input) :=
  (List.finRange 50).map fun k => @rowInput (BitVec.ofNat 6 k.val)

def loading : List (Values Reactive.Input) := tables ++ rows ++ [@commitInput]

private theorem no_row (s : SramState.State) (i : Values Reactive.Input)
    (command : i .command ≠ 1#3) : SramLoading.rowAccepted s i = false := by
  simp [SramLoading.rowAccepted, Sram.rowWriting, SramCoverage.control_correct,
    SharedBranches.rowWriting, SharedBranches.both, SharedBranches.cmd, Expr.eval,
    SramCoverage.baseInput, SramState.State.inputs, command]
  done

private theorem no_table (s : SramState.State) (i : Values Reactive.Input)
    (command : i .command ≠ 6#3) : SramLoading.tableAccepted s i = false := by
  simp [SramLoading.tableAccepted, Sram.tableWriting, SramCoverage.control_correct,
    SharedBranches.tableWriting, SharedBranches.both, SharedBranches.cmd, Expr.eval,
    SramCoverage.baseInput, SramState.State.inputs, command]
  done

theorem table_source (s : SramState.State) (k : BitVec 4) :
    I2cLoading.SourceInput s (tableInput k) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [no_row s (tableInput k) (by simp [tableInput])]
  · intro _
    exact congrArg I2cSource.dictionary BitVec.extractLsb'_append_eq_right.symm
  · intro accepted
    have command := SramCoverage.commit_command (s.inputs (tableInput k)) s.registers accepted
    change (6 : BitVec 3) = 2 at command
    contradiction
  done

theorem row_source (s : SramState.State) (k : BitVec 6) :
    I2cLoading.SourceInput s (rowInput k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro _
    exact ⟨rfl, rfl, BitVec.extractLsb'_append_eq_right⟩
  · simp [no_table s (rowInput k) (by simp [rowInput])]
  · intro accepted
    have command := SramCoverage.commit_command (s.inputs (rowInput k)) s.registers accepted
    change (1 : BitVec 3) = 2 at command
    contradiction
  done

theorem commit_source (s : SramState.State) : I2cLoading.SourceInput s commitInput := by
  refine ⟨?_, ?_, ?_⟩
  · simp [no_row s commitInput (by decide)]
  · simp [no_table s commitInput (by decide)]
  · intro _
    exact ⟨rfl, rfl, rfl, rfl⟩
  done

private theorem history (s : SramState.State) (inputs : List (Values Reactive.Input))
    (all : ∀ state i, i ∈ inputs → I2cLoading.SourceInput state i) :
    I2cLoading.SourceHistory s inputs := by
  induction inputs generalizing s
  case nil => trivial
  case cons i rest ih =>
    exact ⟨all s i (by simp), ih (s.step i) (fun state j member =>
      all state j (List.mem_cons.mpr (Or.inr member)))⟩
  done

theorem source_history (s : SramState.State) : I2cLoading.SourceHistory s loading := by
  apply history
  intro state i member
  simp only [loading, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (table | row) | commit
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp table
    exact table_source state _
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp row
    exact row_source state _
  · subst i
    exact commit_source state
  done

theorem loader_inputs : ∀ i ∈ loading, LifecycleUpload.Input i := by
  intro i member
  simp only [loading, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (table | row) | commit
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp table
    exact ⟨rfl, by simp [tableInput], by simp [tableInput]⟩
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp row
    exact ⟨rfl, by simp [rowInput], by simp [rowInput]⟩
  · subst i
    exact ⟨rfl, by decide, by decide⟩
  done

theorem loading_length : loading.length = 67 := by decide +kernel

end Pinwheel.Hardware.Buffered.I2cCanonicalUpload
