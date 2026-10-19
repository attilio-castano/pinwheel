import Pinwheel.Hardware.Buffered.GenericCertificate

/-! The finite branch descriptor's eager NEXT validation implies that source
checked-instruction normalization is defined. These are static operand facts. -/
namespace Pinwheel.Hardware.Buffered.GenericNormalize
open Pinwheel.Hardware Pinwheel.Program
set_option maxRecDepth 4096

private theorem branch_parts (sample : BitVec 4) (yes no : BitVec 24) :
    let descriptor : BitVec 56 := (0 : BitVec 2) ++ no ++ yes ++ sample ++ (2 : BitVec 2)
    descriptor.extractLsb' 0 2 = 2 ∧ descriptor[6] = yes[0] ∧ descriptor[30] = no[0] := by
  bv_decide

private theorem endpoint_bit (pc : Program.Buffered.PC) (q : GenericLayout.Coordinates) :
    (GenericLayout.endpoint pc q)[0] = false := by
  have low := (GenericLayout.endpoint_fields pc q).2.2.2.2
  simpa using congrArg (fun word : BitVec 1 => word.getLsbD 0) low
  done

private theorem target_bit (map : Program.Buffered.PC → GenericLayout.Coordinates)
    (target : Program.Buffered.Target) :
    (GenericLayout.target map target)[0] =
      match target with | .next => true | .absolute _ => false := by
  cases target
  all_goals simp [GenericLayout.target, endpoint_bit]
  all_goals done

theorem finish_isSome (pc : Program.Buffered.PC)
    (map : Program.Buffered.PC → GenericLayout.Coordinates)
    (word : BitVec 64) (kind : word.extractLsb' 0 3 = 6)
    (finish : Program.Buffered.Finish)
    (normal : GenericCertificate.nextNormalizes pc word (GenericLayout.finish map finish) = true) :
    (finish.eval pc).isSome = true := by
  cases finish
  case sequential => rfl
  case jump => rfl
  case branch sample yes no =>
    have parts := branch_parts (BitVec.ofNat 4 sample.val)
      (GenericLayout.target map yes) (GenericLayout.target map no)
    simp only [GenericCertificate.nextNormalizes, GenericLayout.finish, kind,
      parts.1, parts.2.1, parts.2.2, target_bit] at normal
    by_cases bound : pc.val + 1 < 1024
    case pos =>
      cases yes
      all_goals cases no
      all_goals simp [Program.Buffered.Finish.eval, Program.Buffered.Target.eval, bound]
      all_goals done
    case neg =>
      have last : pc.val = 1023 := by have := pc.isLt; omega
      cases yes
      all_goals cases no
      all_goals simp [last] at normal
      all_goals rfl
      all_goals done

theorem checked_finish_isSome (pc : Program.Buffered.PC)
    (map : Program.Buffered.PC → GenericLayout.Coordinates)
    (instruction : Program.Buffered.Instruction) (action : Engine.Reactive.Action 15)
    (guard : Engine.Reactive.Check) (terminal : Option (Engine.Reactive.Capture 15))
    (finish : Program.Buffered.Finish)
    (operation : instruction.operation = .checked action guard terminal finish)
    (normal : GenericCertificate.nextNormalizes pc (GenericEncoding.encode instruction)
      (GenericLayout.instructionFinish map instruction) = true) :
    (finish.eval pc).isSome = true := by
  have fields := congrArg GenericEncoding.Fields.kind (GenericEncoding.decode_encode instruction)
  have kind : (GenericEncoding.encode instruction).extractLsb' 0 3 = 6 := by
    simpa only [GenericEncoding.decode, GenericEncoding.instruction, operation] using fields
  exact finish_isSome pc map (GenericEncoding.encode instruction) kind finish
    (by simpa only [GenericLayout.instructionFinish, operation] using normal)
  done

theorem normalize_isSome (s : Program.Buffered.State) (pc : Program.Buffered.PC)
    (map : Program.Buffered.PC → GenericLayout.Coordinates)
    (instruction : Program.Buffered.Instruction)
    (normal : GenericCertificate.nextNormalizes pc (GenericEncoding.encode instruction)
      (GenericLayout.instructionFinish map instruction) = true) :
    (Program.Buffered.normalize s pc instruction).isSome = true := by
  cases operation : instruction.operation
  all_goals simp [Program.Buffered.normalize, operation]
  case checked action guard terminal finish =>
    have defined := checked_finish_isSome pc map instruction action guard terminal finish operation normal
    cases equality : finish.eval pc
    all_goals simp_all
    all_goals done

end Pinwheel.Hardware.Buffered.GenericNormalize
