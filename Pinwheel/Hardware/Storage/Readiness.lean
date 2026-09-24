import Pinwheel.Hardware.Storage.SinglePort
import Pinwheel.Hardware.Execution.RecordProofs
import Pinwheel.Hardware.Loader.ProgramImage

/-! The one-port instruction rule and its preservation through encoding and upload.
Compiler-specific certificates live in `Pinwheel.Compile.Readiness`; image
construction belongs to `Loader.ProgramImage`. -/
namespace Pinwheel.Hardware.Storage.Readiness
open Engine.Reactive Loader.ProgramImage

/-- An instruction the one-port organization can run: not a branching `checked`
record of one cycle. -/
def ready {a s : Nat} : Instruction a s → Bool
  | .checked c =>
    match c.finish with
    | .branch .. => c.action.durationMinusOne.val != 0
    | _ => true
  | _ => true

private theorem ofFin_eq_zero (d : Fin 256) : ((BitVec.ofFin d : BitVec 8) == 0) = (d.val == 0) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simpa using this
  · intro h
    apply BitVec.eq_of_toNat_eq
    simpa using h

/-- The word-level rule is the instruction-level one. -/
theorem ready_encode (op : Execution.Operation) : SinglePort.Ready (Execution.encode op) = ready op := by
  unfold SinglePort.Ready Execution.encode
  rw [Execution.unpack_pack]
  cases op with
  | checked c =>
    obtain ⟨action, guard, terminal, finish⟩ := c
    cases finish with
    | branch slot yes no =>
      simp only [Execution.fields, Execution.finishFields, Execution.actionFields, ready, ofFin_eq_zero, bne]
      cases action.durationMinusOne.val == 0 <;> rfl
    | sequential => rfl
    | jump pc => rfl
  | action a => rfl
  | wait w => rfl
  | qualify q => rfl
  | halt => rfl

theorem ready_widen (ins : Instruction) : ready (Execution.widenInstruction ins) = ready ins := by
  cases ins with
  | checked c =>
    obtain ⟨action, guard, terminal, finish⟩ := c
    cases finish <;> rfl
  | action a => rfl
  | wait w => rfl
  | qualify q => rfl
  | halt => rfl

/-- A word whose finish field is clear — an address, the idle pins, the last
address — satisfies the rule whatever its low bits. -/
theorem ready_small (w : BitVec 64) (h : w.toNat < 2 ^ 41) : SinglePort.Ready w = true := by
  have hf : (Execution.unpack w).finish = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [Execution.unpack, BitVec.extractLsb'_toNat]
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]
    rfl
  simp [SinglePort.Ready, hf]

/-- An image all of whose instructions are ready. -/
def Image (p : Execution.Image) : Prop := ∀ pc : Fin 256, ready p.memory[pc] = true

theorem words_ready (p : Execution.Image) (h : Image p) :
    ∀ w ∈ (Execution.imageWords p).toList, SinglePort.Ready w = true := by
  intro w hw
  simp only [Execution.imageWords, Vector.toList_map, List.mem_map] at hw
  obtain ⟨op, hop, rfl⟩ := hw
  rw [ready_encode]
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hop
  have hk' : k < 256 := by simpa using hk
  simpa using h ⟨k, hk'⟩

/-- Every word pushed for a ready image satisfies the one-port rule. -/
theorem upload_ready (p : Execution.Image) (h : Image p) (ws : List (BitVec 64))
    (hu : upload p = some ws) : ∀ w ∈ ws, SinglePort.Ready w = true := by
  unfold upload at hu
  simp only [Option.map_eq_some_iff] at hu
  obtain ⟨image, himage, rfl⟩ := hu
  intro w hw
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with (hdict | ⟨a, _, rfl⟩) | rfl | rfl
  · -- a dictionary word: a word of the program, or the halt padding
    rw [lowered_dictionary _ image himage] at hdict
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hdict
    simp only [Vector.getElem_toList, Vector.getElem_ofFn]
    cases hget : ((Execution.imageWords p).toList.eraseDups)[k]? with
    | none => decide
    | some word =>
      have hmem : word ∈ (Execution.imageWords p).toList :=
        List.mem_eraseDups.mp (List.mem_of_getElem? hget)
      simpa using words_ready p h word hmem
  · apply ready_small
    simp only [BitVec.toNat_setWidth]
    have ha := a.isLt
    have : a.toNat % 2 ^ 64 = a.toNat := Nat.mod_eq_of_lt (by omega)
    omega
  · apply ready_small
    simp only [BitVec.toNat_setWidth]
    have hb := (p.idle.enabled ++ p.idle.levels : BitVec 6).isLt
    have : (p.idle.enabled ++ p.idle.levels : BitVec 6).toNat % 2 ^ 64 =
        (p.idle.enabled ++ p.idle.levels : BitVec 6).toNat := Nat.mod_eq_of_lt (by omega)
    omega
  · apply ready_small
    simp only [BitVec.toNat_ofNat]
    have hl := p.last.isLt
    have : p.last.val % 2 ^ 64 = p.last.val := Nat.mod_eq_of_lt (by omega)
    omega

end Pinwheel.Hardware.Storage.Readiness
