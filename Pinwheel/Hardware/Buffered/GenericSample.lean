import Pinwheel.Hardware.Buffered.GenericEntryFlags

/-! The packed append selector reads the source input from preedge stage2.
Terminal words ignore append operands; the correspondence is used precisely
when the source result actually appends. -/
namespace Pinwheel.Hardware.Buffered.GenericSample
open Pinwheel.Hardware Pinwheel.Program

private theorem selector_some : ∀ (input : Fin 2) (bits : BitVec 2),
    ((if BitVec.ofBool (decide (GenericEncoding.append (some input) = (2 : BitVec 2))) =
        (1 : BitVec 1) then bits.extractLsb' 1 1 else bits.extractLsb' 0 1).getLsbD 0) =
      bits[input.val] := by
  decide +kernel

theorem sampled_of_append (append : Option (Fin 2))
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (field : (Reactive.entryWord.eval i r).extractLsb' 22 2 = GenericEncoding.append append) :
    (Reactive.sampled.eval i r).getLsbD 0 = (r .stage2)[(append.getD 0).val] := by
  cases append
  case none =>
    simp [Reactive.sampled, Expr.eval, field, GenericEncoding.append]
  case some input =>
    simp only [Reactive.sampled, Expr.eval, field, Option.getD_some]
    exact selector_some input (r .stage2)

theorem sampled (instruction : Program.Buffered.Instruction)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction)
    (active : GenericEntryFlags.runs instruction = true) :
    (Reactive.sampled.eval i r).getLsbD 0 = GenericEffects.sample instruction (r .stage2) := by
  apply sampled_of_append instruction.append i r
  rw [word, GenericWord.append_field]
  rcases instruction with ⟨operation, append, preserveLevels, preserveEnabled⟩
  cases operation <;> simp_all [GenericEntryFlags.runs, GenericEncoding.instruction]
  done

theorem receive_runs (instruction : Program.Buffered.Instruction) (e : Transfer.Execution)
    (inputs : Engine.Reactive.Inputs)
    (receive : (GenericEffects.result instruction e inputs).receive = true) :
    GenericEntryFlags.runs instruction = true := by
  rcases instruction with ⟨operation, append, preserveLevels, preserveEnabled⟩
  cases operation <;> simp_all [GenericEntryFlags.runs, GenericEffects.result]

theorem sampled_on_receive (instruction : Program.Buffered.Instruction) (e : Transfer.Execution)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction)
    (receive : (GenericEffects.result instruction e (r .stage2)).receive = true) :
    (Reactive.sampled.eval i r).getLsbD 0 =
      (GenericEffects.result instruction e (r .stage2)).sample := by
  rw [GenericEffects.result_sample]
  exact sampled instruction i r word (receive_runs instruction e (r .stage2) receive)

end Pinwheel.Hardware.Buffered.GenericSample
