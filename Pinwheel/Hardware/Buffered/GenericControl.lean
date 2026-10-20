import Pinwheel.Hardware.Buffered.GenericLayoutCircuit

/-! Static control-coordinate checks transported to the actual combinational
entry validators. No clock-step or source/circuit simulation is assumed. -/
namespace Pinwheel.Hardware.Buffered.GenericControl
open Pinwheel.Hardware Pinwheel.Program GenericLayout GenericCertificate

private def zero (x : BitVec w) : BitVec 1 := BitVec.ofBool (decide (x = 0))
private def equal (x y : BitVec w) : BitVec 1 := BitVec.ofBool (decide (x = y))
private def ult (x y : BitVec w) : BitVec 1 := BitVec.ofBool (decide (x.toNat < y.toNat))
private def either (x y : BitVec w) : BitVec w := ~~~(~~~x &&& ~~~y)
private def mux (condition : BitVec 1) (yes no : BitVec w) : BitVec w :=
  if condition = 1 then yes else no

private def controlValue (control : BitVec 24) (q : Coordinates) : BitVec 1 :=
  let depth := control.extractLsb' 0 2
  let common := zero (control.extractLsb' 22 2) &&&
    ((~~~ult (q.row.extractLsb' 0 6) (control.extractLsb' 2 6)) &&&
      (~~~ult (control.extractLsb' 8 3) q.outer))
  mux (zero depth) (zero control &&& (zero q.outer &&& zero q.inner))
    (mux (equal depth 1)
      (common &&& (zero (control.extractLsb' 11 9) &&&
        (zero (control.extractLsb' 21 1) &&& zero q.inner)))
      (mux (equal depth 2)
        (common &&& ((~~~ult (q.row.extractLsb' 0 6) (control.extractLsb' 11 6)) &&&
          ((~~~ult (control.extractLsb' 11 6) (control.extractLsb' 2 6)) &&&
            ((~~~ult (control.extractLsb' 17 3) q.inner) &&&
              either (~~~(control.extractLsb' 20 1)) (control.extractLsb' 21 1))))) 0))

private theorem controlCanonical_eval (i : Values Reactive.Input) (r : Values Reactive.Register) :
    Reactive.controlCanonical.eval i r = controlValue (Reactive.entryControl.eval i r)
      ⟨Reactive.entryPC.eval i r, Reactive.entryOuter.eval i r, Reactive.entryInner.eval i r⟩ := by
  simp only [Reactive.controlCanonical, Reactive.controlDepth, Reactive.outerStart,
    Reactive.innerStart, Reactive.outerBound, Reactive.innerBound, Reactive.outerEnd,
    Reactive.innerEnd, Reactive.both, Reactive.either, Expr.eval,
    controlValue, zero, equal, ult, either, mux]
  rfl

private theorem ofBool_zero (b : Bool) : decide (BitVec.ofBool b = 0) = !b := by
  cases b <;> rfl

private theorem ofBool_one (b : Bool) : BitVec.ofBool b = (1 : BitVec 1) ↔ b = true := by
  cases b <;> decide +kernel

private theorem ofBool_ite (condition yes no : Bool) :
    (if condition = true then BitVec.ofBool yes else BitVec.ofBool no) =
      BitVec.ofBool (if condition = true then yes else no) := by
  cases condition <;> rfl

private theorem controlValue_bool (control : BitVec 24) (q : Coordinates) :
    controlValue control q = BitVec.ofBool (controlValid control q) := by
  simp only [controlValue, zero, equal, ult, either, mux, controlValid,
    Decode.extract_bit control 20 (by decide),
    Decode.extract_bit control 21 (by decide), ofBool_zero,
    BitVec.not_ofBool, BitVec.ofBool_and_ofBool, Bool.beq_eq_decide_eq,
    ← Nat.not_lt, decide_not]
  simp only [ofBool_one, show (0 : BitVec 1) = BitVec.ofBool false from rfl,
    ofBool_ite, Bool.and_assoc, Bool.not_and, Bool.not_not]
  done

theorem controlCanonical (i : Values Reactive.Input) (r : Values Reactive.Register)
    (control : BitVec 24) (q : Coordinates)
    (entryControl : Reactive.entryControl.eval i r = control)
    (entryPC : Reactive.entryPC.eval i r = q.row)
    (entryOuter : Reactive.entryOuter.eval i r = q.outer)
    (entryInner : Reactive.entryInner.eval i r = q.inner)
    (valid : controlValid control q = true) :
    Reactive.controlCanonical.eval i r = 1 := by
  rw [controlCanonical_eval, entryControl, entryPC, entryOuter, entryInner, controlValue_bool, valid]
  rfl

theorem inBounds {p : Program.Buffered.Program} (layout : Layout p)
    (target : Program.Buffered.PC) (within : target.val < p.code.span)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (entryPC : Reactive.entryPC.eval i r = (layout.map target).row)
    (entryVirtual : Reactive.entryVirtual.eval i r = BitVec.ofNat 11 target.val)
    (count : r .count = BitVec.ofNat 7 layout.count.val)
    (span : r .virtualSpan = BitVec.ofNat 11 p.code.span) :
    Reactive.inBounds.eval i r = 1 := by
  simp only [Reactive.inBounds, Reactive.entryCount, Reactive.both, Expr.eval,
    entryPC, entryVirtual, count, span]
  have countBound : layout.count.val < 2^7 := Nat.lt_trans layout.count.isLt (by decide)
  have spanBound : p.code.span < 2^11 := Nat.lt_of_le_of_lt p.fits (by decide)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound, Nat.mod_eq_of_lt spanBound,
    Nat.mod_eq_of_lt (Nat.lt_trans within spanBound), layout.rowBound target within, within,
    decide_true]
  rfl

private theorem pc_literal (pc : Program.Buffered.PC) :
    (BitVec.ofNat 11 pc.val = (1023 : BitVec 11)) ↔ pc.val = 1023 := by
  constructor
  · intro h
    have hnat := congrArg BitVec.toNat h
    change pc.val % 2048 = 1023 at hnat
    simpa only [Nat.mod_eq_of_lt (Nat.lt_trans pc.isLt (by decide : 1024 < 2048))] using hnat
  · intro h
    rw [h]
    rfl

theorem nextNormalizes (pc : Program.Buffered.PC) (word : BitVec 64) (branch : BitVec 56)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (entryWord : Reactive.entryWord.eval i r = word)
    (entryBranch : Reactive.entryBranch.eval i r = branch)
    (entryVirtual : Reactive.entryVirtual.eval i r = BitVec.ofNat 11 pc.val)
    (valid : GenericCertificate.nextNormalizes pc word branch = true) :
    Reactive.nextNormalizes.eval i r = 1 := by
  simp only [Reactive.nextNormalizes, Reactive.isKind, Reactive.kind, Reactive.both,
    Reactive.either, Expr.eval, entryWord, entryBranch, entryVirtual]
  simp only [pc_literal, Decode.extract_bit branch 6 (by decide),
    Decode.extract_bit branch 30 (by decide), BitVec.not_ofBool,
    BitVec.ofBool_and_ofBool]
  refine Eq.trans ?_ (show BitVec.ofBool true = (1 : BitVec 1) from rfl)
  simpa only [GenericCertificate.nextNormalizes, Bool.beq_eq_decide_eq,
    Bool.and_assoc, Bool.not_and, Bool.not_not] using congrArg BitVec.ofBool valid

end Pinwheel.Hardware.Buffered.GenericControl
