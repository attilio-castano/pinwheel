import Pinwheel.Hardware.Buffered.SpiCoordinates
import Pinwheel.Hardware.Buffered.SpiWord

/-! Entry-control legality for the compact SPI image. The finite certificate is
bound to the actual Reactive control expression by `controlCanonical_eval`. -/
namespace Pinwheel.Hardware.Buffered.SpiEntry
open Pinwheel.Hardware SpiCoordinates

theorem physicalPC_lt_four (c : SpiSource.Config) (target : Nat)
    (within : target ≤ bitSpan c + 1) : physicalPC c target < 4 := by
  simp only [physicalPC]
  split <;> omega
  done

private def zero (x : BitVec w) : BitVec 1 := BitVec.ofBool (decide (x = 0))
private def equal (x y : BitVec w) : BitVec 1 := BitVec.ofBool (decide (x = y))
private def ult (x y : BitVec w) : BitVec 1 := BitVec.ofBool (decide (x.toNat < y.toNat))
private def either (x y : BitVec w) : BitVec w := ~~~(~~~x &&& ~~~y)
private def mux (condition : BitVec 1) (yes no : BitVec w) : BitVec w :=
  if condition = 1 then yes else no

private def controlCheck (control : BitVec 24) (pc : BitVec 7) (outer inner : BitVec 3) : BitVec 1 :=
  let depth := control.extractLsb' 0 2
  let common := zero (control.extractLsb' 22 2) &&&
    ((~~~ult (pc.extractLsb' 0 6) (control.extractLsb' 2 6)) &&&
      (~~~ult (control.extractLsb' 8 3) outer))
  mux (zero depth) (zero control &&& (zero outer &&& zero inner))
    (mux (equal depth 1)
      (common &&& (zero (control.extractLsb' 11 9) &&&
        (zero (control.extractLsb' 21 1) &&& zero inner)))
      (mux (equal depth 2)
        (common &&& ((~~~ult (pc.extractLsb' 0 6) (control.extractLsb' 11 6)) &&&
          ((~~~ult (control.extractLsb' 11 6) (control.extractLsb' 2 6)) &&&
            ((~~~ult (control.extractLsb' 17 3) inner) &&&
              either (~~~(control.extractLsb' 20 1)) (control.extractLsb' 21 1))))) 0))

private theorem controlCanonical_eval (i : Values Reactive.Input) (r : Values Reactive.Register) :
    Reactive.controlCanonical.eval i r = controlCheck (Reactive.entryControl.eval i r)
      (Reactive.entryPC.eval i r) (Reactive.entryOuter.eval i r) (Reactive.entryInner.eval i r) := by
  simp only [Reactive.controlCanonical, Reactive.controlDepth, Reactive.outerStart,
    Reactive.innerStart, Reactive.outerBound, Reactive.innerBound, Reactive.outerEnd,
    Reactive.innerEnd, Reactive.both, Reactive.either, Expr.eval,
    controlCheck, zero, equal, ult, either, mux]
  rfl

private abbrev loopConfig (bytes : Fin 4) : SpiSource.Config := ⟨bytes, 2, by decide⟩

private theorem control_certificate : ∀ bytes : Fin 4, ∀ target : Fin 66,
    target.val ≤ bitSpan (loopConfig bytes) + 1 →
    (ult (BitVec.ofNat 7 (physicalPC (loopConfig bytes) target.val)) 4 &&&
      ult (BitVec.ofNat 11 target.val) (BitVec.ofNat 11 (bitSpan (loopConfig bytes) + 2))) = 1 ∧
    controlCheck (SpiSource.control (loopConfig bytes)
        (BitVec.ofNat 6 (physicalPC (loopConfig bytes) target.val)))
      (BitVec.ofNat 7 (physicalPC (loopConfig bytes) target.val))
      (BitVec.ofNat 3 (outer (loopConfig bytes) target.val))
      (BitVec.ofNat 3 (inner (loopConfig bytes) target.val)) = 1 := by
  decide +kernel

/-- Explicit entry coordinates suffice for both bounds and nested-loop control
legality. This applies to initial START at zero and to every later dispatch.
-/
theorem control_legal (c : SpiSource.Config) (target : Nat)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (within : target ≤ bitSpan c + 1)
    (pc : Reactive.entryPC.eval i r = BitVec.ofNat 7 (physicalPC c target))
    (virtualPC : Reactive.entryVirtual.eval i r = BitVec.ofNat 11 target)
    (outerIndex : Reactive.entryOuter.eval i r = BitVec.ofNat 3 (outer c target))
    (innerIndex : Reactive.entryInner.eval i r = BitVec.ofNat 3 (inner c target))
    (control : Reactive.entryControl.eval i r =
      SpiSource.control c (BitVec.ofNat 6 (physicalPC c target)))
    (count : r .count = 4) (span : r .virtualSpan = BitVec.ofNat 11 (bitSpan c + 2)) :
    Reactive.inBounds.eval i r = 1 ∧ Reactive.controlCanonical.eval i r = 1 := by
  have certificate := control_certificate c.bytesMinusOne
    ⟨target, by have bound := (bitSpan_bounds c).2; omega⟩ within
  simp only [Reactive.inBounds, Reactive.entryCount, Reactive.both, Expr.eval,
    controlCanonical_eval, pc, virtualPC, outerIndex, innerIndex, control, count, span]
  simpa only [ult, SpiSource.control] using certificate
  done

theorem dispatch_control (c : SpiSource.Config) (virtual : Nat)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (initialized : i .initialize = 0) (command : i .command = 0)
    (h : At c virtual r) (within : virtual ≤ bitSpan c) (remaining : r .remaining = 0) :
    Reactive.inBounds.eval i r = 1 ∧ Reactive.controlCanonical.eval i r = 1 := by
  have next := next_coordinates c virtual i r initialized command h within
  have fields := entry_fields c virtual i r initialized command h within remaining
  exact control_legal c (virtual + 1) i r (by omega) next.1 next.2.1
    next.2.2.1 next.2.2.2 fields.2.1 h.count h.virtualSpan
  done

theorem dispatch_legal (c : SpiSource.Config) (virtual : Nat)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (initialized : i .initialize = 0) (command : i .command = 0)
    (h : At c virtual r) (within : virtual ≤ bitSpan c) (remaining : r .remaining = 0) :
    Reactive.legalEntry.eval i r = 1 := by
  have fields := entry_fields c virtual i r initialized command h within remaining
  let leaf : Fin 4 := ⟨physicalPC c (virtual + 1), physicalPC_lt_four c (virtual + 1) (by omega)⟩
  have canonical := SpiWord.canonical c leaf i r fields.1
  have branches := SpiWord.branches c leaf i r fields.1 fields.2.2
  have control := dispatch_control c virtual i r initialized command h within remaining
  simp [Reactive.legalEntry, Reactive.both, Expr.eval, control.1, control.2,
    canonical, branches.1, branches.2]
  done

end Pinwheel.Hardware.Buffered.SpiEntry
