import Pinwheel.Hardware.Buffered.GenericCertificate

/-! Generic binary instruction-field projections and static validator transport
for the actual packed entry graph. -/
namespace Pinwheel.Hardware.Buffered.GenericWord
open Pinwheel.Hardware Pinwheel.Program GenericEncoding GenericCertificate

theorem kind_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 0 3 =
      (GenericEncoding.instruction instruction).kind :=
  congrArg Fields.kind (decode_encode instruction)

theorem levels_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 3 3 =
      (GenericEncoding.instruction instruction).levels :=
  congrArg Fields.levels (decode_encode instruction)

theorem enabled_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 6 3 =
      (GenericEncoding.instruction instruction).enabled :=
  congrArg Fields.enabled (decode_encode instruction)

theorem duration_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 9 8 =
      (GenericEncoding.instruction instruction).duration :=
  congrArg Fields.duration (decode_encode instruction)

theorem preserveLevels_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 17 3 =
      (GenericEncoding.instruction instruction).preserveLevels :=
  congrArg Fields.preserveLevels (decode_encode instruction)

theorem output_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 20 2 =
      (GenericEncoding.instruction instruction).output :=
  congrArg Fields.output (decode_encode instruction)

theorem append_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 22 2 =
      (GenericEncoding.instruction instruction).append :=
  congrArg Fields.append (decode_encode instruction)

theorem shiftEnable_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 24 1 =
      (GenericEncoding.instruction instruction).shiftEnable :=
  congrArg Fields.shiftEnable (decode_encode instruction)

theorem invert_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 25 1 =
      (GenericEncoding.instruction instruction).invert :=
  congrArg Fields.invert (decode_encode instruction)

theorem preserveEnabled_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 26 3 =
      (GenericEncoding.instruction instruction).preserveEnabled :=
  congrArg Fields.preserveEnabled (decode_encode instruction)

theorem capture_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 29 6 =
      (GenericEncoding.instruction instruction).capture :=
  congrArg Fields.capture (decode_encode instruction)

theorem terminal_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 35 6 =
      (GenericEncoding.instruction instruction).terminal :=
  congrArg Fields.terminal (decode_encode instruction)

theorem checkMask_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 41 2 =
      (GenericEncoding.instruction instruction).checkMask :=
  congrArg Fields.checkMask (decode_encode instruction)

theorem checkValue_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 43 2 =
      (GenericEncoding.instruction instruction).checkValue :=
  congrArg Fields.checkValue (decode_encode instruction)

theorem waitInput_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 45 1 =
      (GenericEncoding.instruction instruction).waitInput :=
  congrArg Fields.waitInput (decode_encode instruction)

theorem waitLevel_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 46 1 =
      (GenericEncoding.instruction instruction).waitLevel :=
  congrArg Fields.waitLevel (decode_encode instruction)

theorem budget_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 47 8 =
      (GenericEncoding.instruction instruction).budget :=
  congrArg Fields.budget (decode_encode instruction)

theorem timeout_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 55 1 =
      (GenericEncoding.instruction instruction).timeout :=
  congrArg Fields.timeout (decode_encode instruction)

theorem reserved_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 56 8 =
      (GenericEncoding.instruction instruction).reserved :=
  congrArg Fields.reserved (decode_encode instruction)

theorem check_record (word : BitVec 64) (branch : BitVec 56) :
    Reactive.entryRecord.eval checkInput (checkState word branch) =
      branch ++ (0 : BitVec 24) ++ word := by
  simp [Reactive.entryRecord, Reactive.entering, Reactive.starting,
    Reactive.free, Reactive.busy, Reactive.resetting, Reactive.warm, Reactive.cold,
    Reactive.cmd, Reactive.space, Reactive.both, Reactive.either, Expr.eval,
    checkInput, checkState, Execution.readTree_correct]
  done

theorem check_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 41 4 =
      (GenericEncoding.instruction instruction).checkValue ++
      (GenericEncoding.instruction instruction).checkMask := by
  rw [← checkValue_field instruction, ← checkMask_field instruction]
  bv_decide

theorem wait_field (instruction : Program.Buffered.Instruction) :
    (encode instruction).extractLsb' 45 2 =
      (GenericEncoding.instruction instruction).waitLevel ++
      (GenericEncoding.instruction instruction).waitInput := by
  rw [← waitLevel_field instruction, ← waitInput_field instruction]
  bv_decide

theorem check_word (word : BitVec 64) (branch : BitVec 56) :
    Reactive.entryWord.eval checkInput (checkState word branch) = word := by
  simp only [Reactive.entryWord, Expr.eval, check_record]
  bv_decide

theorem check_branch (word : BitVec 64) (branch : BitVec 56) :
    Reactive.entryBranch.eval checkInput (checkState word branch) = branch := by
  simp only [Reactive.entryBranch, Expr.eval, check_record]
  bv_decide

theorem canonical_congr (i j : Values Reactive.Input)
    (r s : Values Reactive.Register)
    (word : Reactive.entryWord.eval i r = Reactive.entryWord.eval j s) :
    Reactive.canonical.eval i r = Reactive.canonical.eval j s := by
  simp only [Reactive.canonical, Reactive.entryTerminal, Reactive.isKind,
    Reactive.kind, Reactive.entryCapture, Reactive.terminalCapture,
    Reactive.captureCanonical, Reactive.both, Reactive.either, Expr.eval, word]
  rfl

theorem branchCanonical_congr (i j : Values Reactive.Input)
    (r s : Values Reactive.Register)
    (word : Reactive.entryWord.eval i r = Reactive.entryWord.eval j s)
    (branch : Reactive.entryBranch.eval i r = Reactive.entryBranch.eval j s) :
    Reactive.branchCanonical.eval i r = Reactive.branchCanonical.eval j s := by
  simp only [Reactive.branchCanonical, Reactive.endpointCanonical, Reactive.isKind,
    Reactive.kind, Reactive.both, Reactive.either, Expr.eval, word, branch]
  rfl

theorem canonical (word : BitVec 64) (i : Values Reactive.Input) (r : Values Reactive.Register)
    (entryWord : Reactive.entryWord.eval i r = word) (valid : WordCanonical word) :
    Reactive.canonical.eval i r = 1 :=
  (canonical_congr i checkInput r (checkState word 0)
    (entryWord.trans (check_word word 0).symm)).trans valid

theorem branchCanonical (word : BitVec 64) (branch : BitVec 56)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (entryWord : Reactive.entryWord.eval i r = word)
    (entryBranch : Reactive.entryBranch.eval i r = branch)
    (valid : BranchCanonical word branch) :
    Reactive.branchCanonical.eval i r = 1 :=
  (branchCanonical_congr i checkInput r (checkState word branch)
    (entryWord.trans (check_word word branch).symm)
    (entryBranch.trans (check_branch word branch).symm)).trans valid

end Pinwheel.Hardware.Buffered.GenericWord

