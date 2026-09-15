import Pinwheel.Hardware.Reactive.Scheduler

namespace Pinwheel.Hardware.Reactive

private theorem bit_mux (b : BitVec 1) (x : BitVec 2) :
    (if b = 1 then x.extractLsb' 1 1 else x.extractLsb' 0 1) = BitVec.ofBool (x.getLsbD b.toNat) := by
  revert b x
  decide +kernel
  done

private theorem low_bit (b : BitVec 6) : b.extractLsb' 0 1 = BitVec.ofBool b[0] := by
  revert b
  decide +kernel
  done

@[simp] theorem bool_one (b : Bool) : BitVec.ofBool b = (1 : BitVec 1) ↔ b = true := by
  cases b <;> decide +kernel

@[simp] theorem slot_eq (b : BitVec 4) (k : Fin 16) : b = BitVec.ofFin k ↔ b.toFin = k := by
  cases b <;> simp
  done

theorem inputBit_correct (selector : E 1) (i : Inputs) (s : State) :
    (inputBit selector).eval i.values s.values =
      BitVec.ofBool (i.incoming.getLsbD (selector.eval i.values s.values).toNat) := by
  simp only [inputBit, Expr.eval, Inputs.values]
  exact bit_mux _ _
  done

theorem captureSlots_correct (bits : E 6) (slots : Slots) (values : Samples)
    (i : Inputs) (s : State) (hs : ∀ k, (slots k).eval i.values s.values = BitVec.ofBool values[k.val])
    (k : Fin 16) :
    (captureSlots bits slots k).eval i.values s.values =
      BitVec.ofBool (Engine.Reactive.capture values (Execution.getCapture (bits.eval i.values s.values)) i.incoming)[k.val] := by
  simp only [captureSlots, Expr.eval, inputBit_correct, hs]
  by_cases h : (bits.eval i.values s.values)[0] = true <;>
    by_cases hd : ((bits.eval i.values s.values).extractLsb' 2 4).toFin = k <;>
    simp_all [low_bit, Execution.getCapture, Engine.Reactive.capture, Engine.capture, ← BitVec.getLsbD_eq_getElem]
  done

end Pinwheel.Hardware.Reactive
