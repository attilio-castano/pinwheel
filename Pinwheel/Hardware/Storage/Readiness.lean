import Pinwheel.Hardware.Storage.SinglePort
import Pinwheel.Hardware.Execution.RecordProofs
import Pinwheel.Compile.I2CRead
import Pinwheel.Compile.UARTRx
import Pinwheel.Engine.Compatibility

/-! The one-port rule, at the level of programs and compilers.

`SinglePort.Ready` is a condition on 64-bit words. Here it is a condition on
instructions (`ready`), shown to be the same thing through the record encoding,
carried to every word the host pushes for an image (`upload_ready`), and then
proved — not tested — for the compilers: the I²C write and register read for
every request whenever a phase lasts at least two cycles, UART and SPI
transmission always; and the UART receiver never, because it polls for the start
bit with one-cycle branching records. -/
namespace Pinwheel.Hardware.Storage.Readiness
open Engine.Reactive

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

/-- The 322 words the host pushes for an image: the dictionary, the addresses,
the idle pins and the last address. -/
def upload (p : Execution.Image) : Option (List (BitVec 64)) :=
  (Execution.lowerIndexed (Execution.imageWords p)).map fun image =>
    image.val.dictionary.toList ++ image.val.addresses.toList.map (·.zeroExtend 64) ++
      [(p.idle.enabled ++ p.idle.levels : BitVec 6).zeroExtend 64, BitVec.ofNat 64 p.last.val]

theorem words_ready (p : Execution.Image) (h : Image p) :
    ∀ w ∈ (Execution.imageWords p).toList, SinglePort.Ready w = true := by
  intro w hw
  simp only [Execution.imageWords, Vector.toList_map, List.mem_map] at hw
  obtain ⟨op, hop, rfl⟩ := hw
  rw [ready_encode]
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hop
  have hk' : k < 256 := by simpa using hk
  simpa using h ⟨k, hk'⟩

/-- The dictionary the lowering builds: the distinct words in order, padded with halt. -/
theorem lowered_dictionary (words : Execution.Words) (image : {image : Execution.Indexed // image.expand = words})
    (h : Execution.lowerIndexed words = some image) :
    image.val.dictionary = Vector.ofFn fun k => (words.toList.eraseDups)[k.val]?.getD 4 := by
  unfold Execution.lowerIndexed at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · rw [← Option.some.inj h]
    · exact absurd h (by simp)

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

/-! ### The compilers -/

theorem ready_ite {a s : Nat} {c : Prop} [Decidable c] {x y : Instruction a s}
    (hx : ready x = true) (hy : ready y = true) : ready (if c then x else y) = true := by
  split <;> assumption

theorem ready_dite {a s : Nat} {c : Prop} [Decidable c] {x : c → Instruction a s}
    {y : ¬c → Instruction a s} (hx : ∀ h, ready (x h) = true) (hy : ∀ h, ready (y h) = true) :
    ready (dite c x y) = true := by
  split
  · exact hx _
  · exact hy _

theorem i2c_bit_ready (cfg : I2C.Config) (r : I2C.Request) (slot : Fin 18) (phase : Nat)
    (h : cfg.phaseMinusOne.val ≠ 0) : ready (Compile.I2C.bitInstruction cfg r slot phase) = true := by
  unfold Compile.I2C.bitInstruction
  split
  · rfl
  · rfl
  · rfl
  · simp only [ready, Compile.I2C.fallFinish]
    split <;> simp [h]

/-- The compiled I²C write is ready for every request whenever a phase lasts at
least two cycles. -/
theorem i2c_write (cfg : I2C.Config) (r : I2C.Request) (h : cfg.phaseMinusOne.val ≠ 0) :
    Image (Execution.widenProgram (Compile.I2C.program cfg r)) := by
  intro pc
  simp only [Execution.widenProgram, Fin.getElem_fin, Vector.getElem_ofFn]
  split
  · rw [ready_widen]
    simp only [Program.fetch, Compile.I2C.program, Vector.getElem_ofFn, Compile.I2C.instruction]
    repeat' (first | apply ready_ite | apply ready_dite | intro _ | rfl | exact i2c_bit_ready cfg r _ _ h)
  · rfl

theorem i2c_read_bit_ready (cfg : I2C.Config) (r : I2C.RegisterRead.Request) (slot : Fin 36) (phase : Nat)
    (h : cfg.phaseMinusOne.val ≠ 0) : ready (Compile.I2CRead.bitInstruction cfg r slot phase) = true := by
  unfold Compile.I2CRead.bitInstruction
  split
  · rfl
  · rfl
  · rfl
  · simp only [ready, Compile.I2CRead.fallFinish]
    repeat' split
    all_goals simp [h]

/-- The compiled I²C register read is ready under the same condition. -/
theorem i2c_read (cfg : I2C.Config) (r : I2C.RegisterRead.Request) (h : cfg.phaseMinusOne.val ≠ 0) :
    Image (Compile.I2CRead.program cfg r) := by
  intro pc
  simp only [Compile.I2CRead.program, Fin.getElem_fin, Vector.getElem_ofFn, Compile.I2CRead.instruction]
  repeat' (first | apply ready_ite | apply ready_dite | intro _ | rfl | exact i2c_read_bit_ready cfg r _ _ h)

/-- Programs of the original engine have no `checked` records at all. -/
theorem embedded (p : Engine.Program) : Image (Execution.widenProgram (embedProgram p)) := by
  intro pc
  simp only [Execution.widenProgram, Fin.getElem_fin, Vector.getElem_ofFn]
  split
  · rw [ready_widen]
    simp only [Program.fetch, embedProgram, Vector.getElem_ofFn]
    split
    · cases p.memory[pc.val] <;> rfl
    · rfl
  · rfl

/-- The UART receiver polls for the start bit with one-cycle branching records:
it is never ready, at any bit period. -/
theorem uart_receiver (cfg : UART.Rx.Config) : ¬ Image (Compile.UARTRx.program cfg) := by
  intro h
  have h0 := h 0
  simp [Compile.UARTRx.program, Compile.UARTRx.instruction, Compile.UARTRx.poll, ready] at h0

end Pinwheel.Hardware.Storage.Readiness
