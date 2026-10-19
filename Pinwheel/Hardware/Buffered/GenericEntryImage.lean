import Pinwheel.Hardware.Buffered.GenericRelation
import Pinwheel.Hardware.Buffered.GenericWord
import Pinwheel.Hardware.Buffered.GenericControl

/-! Static source records supply the actual packed entry fetch. The dynamic
premises identify only the selected address and installed memory image. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

theorem sourceRecord {p : Program.Buffered.Program} (layout : GenericCertificate.Layout p)
    (pc : Program.Buffered.PC) (within : pc.val < p.code.span)
    (instruction : Program.Buffered.Instruction) (fetch : p.fetch pc = some instruction) :
    layout.words ((layout.map pc).row.setWidth 6) =
      GenericLayout.record layout.map
        ((layout.words ((layout.map pc).row.setWidth 6)).extractLsb' 64 24) instruction := by
  rcases layout.sourceRecord pc within with ⟨other, found, record⟩
  have same : other = instruction := Option.some.inj (found.symm.trans fetch)
  exact same ▸ record

theorem sourceWord {p : Program.Buffered.Program} (layout : GenericCertificate.Layout p)
    (pc : Program.Buffered.PC) (within : pc.val < p.code.span)
    (instruction : Program.Buffered.Instruction) (fetch : p.fetch pc = some instruction) :
    (layout.words ((layout.map pc).row.setWidth 6)).extractLsb' 0 64 =
      GenericEncoding.encode instruction := by
  have record := congrArg (fun word : BitVec 144 => word.extractLsb' 0 64)
    (sourceRecord layout pc within instruction fetch)
  simpa only [GenericLayout.record, BitVec.extractLsb'_append_eq_right] using record

theorem sourceBranch {p : Program.Buffered.Program} (layout : GenericCertificate.Layout p)
    (pc : Program.Buffered.PC) (within : pc.val < p.code.span)
    (instruction : Program.Buffered.Instruction) (fetch : p.fetch pc = some instruction) :
    (layout.words ((layout.map pc).row.setWidth 6)).extractLsb' 88 56 =
      GenericLayout.instructionFinish layout.map instruction := by
  have record := congrArg (fun word : BitVec 144 => word.extractLsb' 88 56)
    (sourceRecord layout pc within instruction fetch)
  simpa (disch := decide) only [GenericLayout.record,
    BitVec.extractLsb'_append_eq_of_le, BitVec.extractLsb'_append_eq_left,
    BitVec.extractLsb'_eq_self, Nat.reduceSub] using record

theorem entryRecord {p : Program.Buffered.Program} (layout : GenericCertificate.Layout p)
    (i : Values Reactive.Input) (r : Values Reactive.Register) (pc : Program.Buffered.PC)
    (entering : Reactive.entering.eval i r = 1)
    (address : Reactive.entryPC.eval i r = (layout.map pc).row)
    (image : ∀ k, r (.word k) = layout.words k) :
    Reactive.entryRecord.eval i r = layout.words ((layout.map pc).row.setWidth 6) := by
  simp [Reactive.entryRecord, Expr.eval, entering, address,
    Execution.readTree_correct, image, BitVec.setWidth_eq_extractLsb']
  done

theorem entryWord {p : Program.Buffered.Program} (layout : GenericCertificate.Layout p)
    (i : Values Reactive.Input) (r : Values Reactive.Register) (pc : Program.Buffered.PC)
    (within : pc.val < p.code.span) (instruction : Program.Buffered.Instruction)
    (fetch : p.fetch pc = some instruction)
    (entering : Reactive.entering.eval i r = 1)
    (address : Reactive.entryPC.eval i r = (layout.map pc).row)
    (image : ∀ k, r (.word k) = layout.words k) :
    Reactive.entryWord.eval i r = GenericEncoding.encode instruction := by
  simpa only [Reactive.entryWord, Expr.eval,
    entryRecord layout i r pc entering address image] using
    sourceWord layout pc within instruction fetch

theorem entryBranch {p : Program.Buffered.Program} (layout : GenericCertificate.Layout p)
    (i : Values Reactive.Input) (r : Values Reactive.Register) (pc : Program.Buffered.PC)
    (within : pc.val < p.code.span) (instruction : Program.Buffered.Instruction)
    (fetch : p.fetch pc = some instruction)
    (entering : Reactive.entering.eval i r = 1)
    (address : Reactive.entryPC.eval i r = (layout.map pc).row)
    (image : ∀ k, r (.word k) = layout.words k) :
    Reactive.entryBranch.eval i r = GenericLayout.instructionFinish layout.map instruction := by
  simpa only [Reactive.entryBranch, Expr.eval,
    entryRecord layout i r pc entering address image] using
    sourceBranch layout pc within instruction fetch

theorem sourceNormalizes {p : Program.Buffered.Program} (layout : GenericCertificate.Layout p)
    (pc : Program.Buffered.PC) (within : pc.val < p.code.span)
    (instruction : Program.Buffered.Instruction) (fetch : p.fetch pc = some instruction) :
    GenericCertificate.nextNormalizes pc (GenericEncoding.encode instruction)
      (GenericLayout.instructionFinish layout.map instruction) = true := by
  simpa only [sourceWord layout pc within instruction fetch,
    sourceBranch layout pc within instruction fetch] using layout.normalizes pc within

theorem entryLegal {p : Program.Buffered.Program} (layout : GenericCertificate.Layout p)
    (i : Values Reactive.Input) (r : Values Reactive.Register) (pc : Program.Buffered.PC)
    (within : pc.val < p.code.span)
    (entering : Reactive.entering.eval i r = 1)
    (address : Reactive.entryPC.eval i r = (layout.map pc).row)
    (outer : Reactive.entryOuter.eval i r = (layout.map pc).outer)
    (inner : Reactive.entryInner.eval i r = (layout.map pc).inner)
    (virtualPC : Reactive.entryVirtual.eval i r = BitVec.ofNat 11 pc.val)
    (image : ∀ k, r (.word k) = layout.words k)
    (count : r .count = BitVec.ofNat 7 layout.count.val)
    (span : r .virtualSpan = BitVec.ofNat 11 p.code.span) :
    Reactive.legalEntry.eval i r = 1 := by
  have record := entryRecord layout i r pc entering address image
  have word : Reactive.entryWord.eval i r =
      (layout.words ((layout.map pc).row.setWidth 6)).extractLsb' 0 64 := by
    simp only [Reactive.entryWord, Expr.eval, record]
  have branch : Reactive.entryBranch.eval i r =
      (layout.words ((layout.map pc).row.setWidth 6)).extractLsb' 88 56 := by
    simp only [Reactive.entryBranch, Expr.eval, record]
  have control : Reactive.entryControl.eval i r =
      (layout.words ((layout.map pc).row.setWidth 6)).extractLsb' 64 24 := by
    simp only [Reactive.entryControl, Expr.eval, record]
  have bounds := GenericControl.inBounds layout pc within i r address virtualPC count span
  have canonical := GenericWord.canonical _ i r word (layout.canonical pc within)
  have branches := GenericWord.branchCanonical _ _ i r word branch
    (layout.branchCanonical pc within)
  have controls := GenericControl.controlCanonical i r _ (layout.map pc)
    control address outer inner (layout.controlCanonical pc within)
  have normal := GenericControl.nextNormalizes pc _ _ i r word branch virtualPC
    (layout.normalizes pc within)
  simp only [Reactive.legalEntry, Reactive.both, Expr.eval,
    bounds, canonical, branches, controls, normal]
  rfl

end Pinwheel.Hardware.Buffered.Refinement
