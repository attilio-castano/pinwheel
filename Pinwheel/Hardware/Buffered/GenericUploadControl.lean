import Pinwheel.Hardware.Buffered.GenericUploadInstalled
import Pinwheel.Hardware.Buffered.SerialUploadTransaction

/-! Program-independent loader admission. Static Layout bounds establish the
actual COMMIT count/span validators; no hardware admission premise is supplied. -/
namespace Pinwheel.Hardware.Buffered.GenericUpload.Serial
open Pinwheel.Hardware Pinwheel.Program
variable {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

structure Table (image : Image p layout) (i : Values Reactive.Input) (k : BitVec 4) : Prop where
  cold : i .initialize = 0
  command : i .command = 6
  address : i .address = 0#2 ++ k
  branch : i .branch = image.dictionary k

structure Row (image : Image p layout) (i : Values Reactive.Input) (k : BitVec 6) : Prop where
  cold : i .initialize = 0
  command : i .command = 1
  address : i .address = k
  word : i .word = image.word k
  control : i .control = image.control k
  branch : i .branch = 0#52 ++ image.branchIndex k

structure Commit (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (i : Values Reactive.Input) : Prop where
  cold : i .initialize = 0
  command : i .command = 2
  count : i .count = BitVec.ofNat 7 layout.count.val
  span : i .virtualSpan = BitVec.ofNat 11 p.code.span
  levels : i .idleLevels = p.idle.levels
  enabled : i .idleEnabled = p.idle.enabled

private theorem band_one : ∀ a b : BitVec 1, a &&& b = 1 ↔ a = 1 ∧ b = 1 := by
  decide +kernel

private theorem foldl_one (xs : List α) (f : α → Reactive.E 1) (acc : Reactive.E 1)
    (i : Values Reactive.Input) (s : Values Reactive.Register) :
    (xs.foldl (fun a k => Reactive.both a (f k)) acc).eval i s = 1 ↔
      acc.eval i s = 1 ∧ ∀ k ∈ xs, (f k).eval i s = 1 := by
  induction xs generalizing acc with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldl_cons,ih]
    simp only [Reactive.both,Expr.eval,band_one,List.mem_cons,forall_eq_or_imp,and_assoc]

theorem covered_prefix (i : Values Reactive.Input) (r : Values Reactive.Register)
    (count : i .count = BitVec.ofNat 7 layout.count.val)
    (covered : ∀ k : Fin 64, k.val < layout.count.val → (r .written).getLsbD k.val = true) :
    Reactive.covered.eval i r = 1 := by
  unfold Reactive.covered
  rw [foldl_one]
  refine ⟨rfl,?_⟩
  intro k _
  have wide : (BitVec.ofNat 7 k.val).toNat = k.val := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    have bound := k.isLt
    omega
  have countMod : layout.count.val % 128 = layout.count.val := Nat.mod_eq_of_lt (by
    have bound := layout.count.isLt
    omega)
  by_cases live : k.val < layout.count.val
  · have bit := covered k live
    have slice : (r .written).extractLsb' k.val 1 = 1#1 := by
      apply eq_of_beq
      exact (BitVec.getLsbD_eq_extractLsb' _ _).symm.trans bit
    simp [Reactive.either,Expr.eval,count,wide,slice]
  · simp [Reactive.either,Expr.eval,count,wide,countMod,live]

theorem span_toNat (p : Program.Buffered.Program) :
    (BitVec.ofNat 11 p.code.span).toNat = p.code.span := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
  have bound := p.fits
  omega

theorem geometry_valid (input : Commit p layout i) (r : Values Reactive.Register) :
    Reactive.countValid.eval i r = 1 ∧ Reactive.spanValid.eval i r = 1 := by
  have countPositive := layout.positive
  have countBound := layout.count.isLt
  have spanPositive := GenericLayout.span_positive p.code
  have spanBound := p.fits
  have countNotZero : BitVec.ofNat 7 layout.count.val ≠ 0 := by
    intro equal
    have zero := congrArg BitVec.toNat equal
    rw [count_toNat] at zero
    change layout.count.val = 0 at zero
    omega
  have spanNotZero : BitVec.ofNat 11 p.code.span ≠ 0 := by
    intro equal
    have zero := congrArg BitVec.toNat equal
    rw [span_toNat] at zero
    change p.code.span = 0 at zero
    omega
  simp [Reactive.countValid,Reactive.spanValid,Reactive.both,Expr.eval,input.count,input.span]
  exact ⟨⟨countNotZero,by omega⟩,spanNotZero,by omega⟩

theorem commit_accepted (s : SramState.State) (i : Values Reactive.Input) (input : Commit p layout i)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0)
    (pending : s.core .pending = 1) (space : s.core .generation ≠ 65535)
    (covered : ∀ k : Fin 64, k.val < layout.count.val → (s.core .written).getLsbD k.val = true)
    (dictionary : s.registers .branchWritten = 65535) :
    Sram.committing.eval (s.inputs i) s.registers = 1 := by
  rw [Lifecycle.committing_effective]
  have command : Lifecycle.effectiveInputs s i .command = 2#3 := by
    simp [Lifecycle.effectiveInputs,SharedBranches.mappedInput,SharedBranches.inputExpr,
      SharedBranches.cmd,SharedBranches.tableCovered,SharedBranches.both,Expr.eval,
      SramExecution.selectedShared,Sram.registerExpr,input.command,dictionary]
  have free : Reactive.free.eval (Lifecycle.effectiveInputs s i) (Lifecycle.effectiveState s i) = 1 := by
    simp [Reactive.free,Reactive.resetting,Reactive.cold,Reactive.warm,Reactive.cmd,
      Reactive.busy,Reactive.both,Reactive.either,Expr.eval,command,
      show Lifecycle.effectiveInputs s i .initialize = 0 from input.cold,
      show Lifecycle.effectiveState s i .phase = 0 from phase,
      show Lifecycle.effectiveState s i .retained = 0 from retained]
  have coverage := covered_prefix (Lifecycle.effectiveInputs s i) (Lifecycle.effectiveState s i) input.count covered
  have geometry := geometry_valid input (Lifecycle.effectiveState s i)
  have countValid : Reactive.countValid.eval (Lifecycle.effectiveInputs s i) (Lifecycle.effectiveState s i) = 1 := geometry.1
  have spanValid : Reactive.spanValid.eval (Lifecycle.effectiveInputs s i) (Lifecycle.effectiveState s i) = 1 := geometry.2
  simp [Reactive.committing,Reactive.space,Reactive.both,Reactive.cmd,Expr.eval,free,command,
    coverage,countValid,spanValid,
    show Lifecycle.effectiveState s i .pending = 1 from pending,
    show Lifecycle.effectiveState s i .generation ≠ 65535#16 from space]

end Pinwheel.Hardware.Buffered.GenericUpload.Serial
