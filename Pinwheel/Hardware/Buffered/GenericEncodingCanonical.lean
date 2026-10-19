import Pinwheel.Hardware.Buffered.GenericWord

/-! Typed source operands always encode a canonical instruction word. This
fact is independent of source timing values and controller transitions. -/
namespace Pinwheel.Hardware.Buffered.GenericEncoding
open Pinwheel.Hardware Pinwheel.Program GenericCertificate
set_option maxRecDepth 10000

private theorem low2_zero (upper : BitVec w) :
    (upper ++ (0#1) ++ (0#1)).extractLsb' 0 2 = 0 := by
  rw [BitVec.append_assoc]
  simp only [BitVec.extractLsb'_cast, BitVec.extractLsb'_append_eq_right]
  rfl

private theorem low4_zero (upper : BitVec w) :
    (upper ++ (0#2) ++ (0#2)).extractLsb' 0 4 = 0 := by
  rw [BitVec.append_assoc]
  simp only [BitVec.extractLsb'_cast, BitVec.extractLsb'_append_eq_right]
  rfl

private theorem append_ne_three (input : Option (Fin 2)) : append input ≠ 3#2 := by
  cases input
  case none => decide
  case some input =>
    intro equal
    have numeric := congrArg BitVec.toNat equal
    simp [append] at numeric
    have := input.isLt
    omega

private theorem output_ne_three (output : Fin 3) : BitVec.ofNat 2 output.val ≠ 3#2 := by
  intro equal
  have numeric := congrArg BitVec.toNat equal
  simp at numeric
  have := output.isLt
  omega

private theorem capture_valid (c : Option (Engine.Reactive.Capture 15)) :
    ~~~(~~~(capture c).extractLsb' 0 1 &&& BitVec.ofBool (!decide (capture c = 0#6))) = 1 := by
  cases c
  case none => decide
  case some c =>
    have enabled : (capture (some c)).extractLsb' 0 1 = 1 := by
      simp only [capture, BitVec.extractLsb'_append_eq_right]
    rw [enabled]
    simp

theorem canonical_instruction (i : Program.Buffered.Instruction) : WordCanonical (encode i) := by
  unfold WordCanonical
  simp only [Reactive.canonical, Reactive.entryTerminal, Reactive.isKind, Reactive.kind,
    Reactive.entryCapture, Reactive.terminalCapture, Reactive.captureCanonical,
    Reactive.both, Reactive.either, Expr.eval, GenericWord.check_word]
  cases operation : i.operation
  all_goals simp (disch := decide) only [encode, instruction, action, empty, operation, Fields.word,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le,
    BitVec.extractLsb'_eq_self, Nat.reduceSub]
  all_goals simp [low2_zero, low4_zero, append_ne_three, output_ne_three, capture_valid]
  case fault reason => cases reason <;> decide

end Pinwheel.Hardware.Buffered.GenericEncoding
