import Pinwheel.Hardware.Storage.Readiness
import Pinwheel.Compile.I2CRead
import Pinwheel.Compile.UARTRx
import Pinwheel.Engine.Compatibility

/-! Compiler certificates for the one-port program rule. -/
namespace Pinwheel.Compile.Readiness
open Hardware Hardware.Storage.Readiness Engine.Reactive

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

end Pinwheel.Compile.Readiness
