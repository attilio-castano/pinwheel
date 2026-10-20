import Pinwheel.Hardware.Buffered.SpiCircuit
import Pinwheel.Program.Buffered
import Pinwheel.Hardware.Buffered.GenericEncoding

/-! Bitwise interpretation of the actual reactive scratch bank and cached
input predicates. The source sample vector remains arbitrary. -/
namespace Pinwheel.Hardware.Buffered.GenericPhase
open Pinwheel.Hardware Pinwheel.Engine.Reactive
set_option maxRecDepth 4096

def Scratch (word : BitVec 16) (slots : Vector Bool 16) : Prop :=
  ∀ k : Fin 16, word.getLsbD k.val = slots[k.val]

def CaptureFields (bits : BitVec 6) : Option (Capture 15) → Prop
  | none => bits.extractLsb' 0 1 = 0
  | some c => bits.extractLsb' 0 1 = 1 ∧
      bits.extractLsb' 1 1 = BitVec.ofNat 1 c.input.val ∧
      bits.extractLsb' 2 4 = BitVec.ofNat 4 c.destination.val

theorem capture_fields (c : Option (Capture 15)) : CaptureFields (GenericEncoding.capture c) c := by
  cases c
  all_goals simp only [CaptureFields, GenericEncoding.capture]
  case none => rfl
  case some c =>
    generalize BitVec.ofNat 4 c.destination.val = destination
    generalize BitVec.ofNat 1 c.input.val = input
    bv_decide
    done
  all_goals done

theorem inputBit_matches (selector : Reactive.E 1) (input : Fin 2)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (selection : selector.eval i r = BitVec.ofNat 1 input.val) :
    (Reactive.inputBit selector).eval i r = BitVec.ofBool ((r .stage2)[input.val]) := by
  rcases input with ⟨_|(_|input), bound⟩
  all_goals first | omega | simp [Reactive.inputBit, Expr.eval, selection]
  all_goals apply (BitVec.eq_of_getLsbD_eq_iff).2
  all_goals intro index valid
  all_goals simp [show index = 0 by omega, ← BitVec.getLsbD_eq_getElem]
  all_goals done

theorem capture_matches (bits : Reactive.E 6) (old : Reactive.E 16)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (slots : Vector Bool 16) (c : Option (Capture 15))
    (fields : CaptureFields (bits.eval i r) c)
    (scratch : Scratch (old.eval i r) slots) :
    Scratch ((Reactive.captureBits bits old).eval i r) (capture slots c (r .stage2)) := by
  intro k
  rw [Reactive.capture_bit_at bits old i r k]
  cases c
  case none => simpa [Reactive.both, Expr.eval, capture,
      show (bits.eval i r).extractLsb' 0 1 = 0 from fields,
      ← BitVec.getLsbD_eq_getElem] using scratch k
  case some c =>
    have selected := inputBit_matches (.slice 1 1 (by decide) bits) c.input i r
      (by simpa only [Expr.eval] using fields.2.1)
    simp [Reactive.both, Expr.eval, fields.1, fields.2.2, selected,
      capture, Pinwheel.Engine.capture, ← BitVec.getLsbD_eq_getElem]
    by_cases same : c.destination = k <;>
      simp [same, -BitVec.getLsbD_eq_getElem, scratch k]
    done

theorem exitScratch_matches (i : Values Reactive.Input) (r : Values Reactive.Register)
    (slots : Vector Bool 16) (c : Option (Capture 15))
    (fields : CaptureFields (r .cachedTerminal) c)
    (scratch : Scratch (r .scratch) slots)
    (terminal : Reactive.terminalEdge.eval i r = 1) :
    Scratch (Reactive.exitScratch.eval i r) (capture slots c (r .stage2)) := by
  simpa [Reactive.exitScratch, Expr.eval, terminal] using
    capture_matches (.reg .cachedTerminal) (.reg .scratch) i r slots c fields scratch

theorem checkedReady_matches (i : Values Reactive.Input) (r : Values Reactive.Register)
    (guard : Check) (cache : r .cachedCheck = guard.value ++ guard.mask) :
    Reactive.checkedReady.eval i r = BitVec.ofBool (guard.ready (r .stage2)) := by
  have low : (r .cachedCheck).extractLsb' 0 2 = guard.mask := by
    simpa only [cache] using
      (BitVec.extractLsb'_append_eq_right (a := guard.value) (b := guard.mask))
  have high : (r .cachedCheck).extractLsb' 2 2 = guard.value := by
    simpa only [cache] using
      (BitVec.extractLsb'_append_eq_left (a := guard.value) (b := guard.mask))
  simp [Reactive.checkedReady, Expr.eval, low, high, Check.ready]
  congr 1
  done

theorem waitReady_matches (i : Values Reactive.Input) (r : Values Reactive.Register)
    (condition : Condition)
    (cache : r .cachedWait = BitVec.ofBool condition.level ++ BitVec.ofNat 1 condition.input.val) :
    Reactive.waitReady.eval i r = BitVec.ofBool (condition.ready (r .stage2)) := by
  have low : (r .cachedWait).extractLsb' 0 1 = BitVec.ofNat 1 condition.input.val := by
    simpa only [cache] using
      (BitVec.extractLsb'_append_eq_right
        (a := BitVec.ofBool condition.level) (b := BitVec.ofNat 1 condition.input.val))
  have high : (r .cachedWait).extractLsb' 1 1 = BitVec.ofBool condition.level := by
    simpa only [cache] using
      (BitVec.extractLsb'_append_eq_left
        (a := BitVec.ofBool condition.level) (b := BitVec.ofNat 1 condition.input.val))
  have selected := inputBit_matches (.slice 0 1 (by decide) (.reg .cachedWait))
    condition.input i r (by simpa only [Expr.eval] using low)
  simp [Reactive.waitReady, Expr.eval, selected, high, Condition.ready]
  simp only [BitVec.ofBool_eq_iff_eq]
  congr 1
  done

theorem branchBit_matches (i : Values Reactive.Input) (r : Values Reactive.Register)
    (slots : Vector Bool 16) (sample : Fin 16)
    (selection : Reactive.branchSample.eval i r = BitVec.ofNat 4 sample.val)
    (scratch : Scratch (Reactive.exitScratch.eval i r) slots) :
    Reactive.branchBit.eval i r = BitVec.ofBool slots[sample.val] := by
  rw [Reactive.terminal_capture_forwarding]
  simp only [Execution.readTree_correct, Expr.eval, selection, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt sample.isLt]
  apply (BitVec.eq_of_getLsbD_eq_iff).2
  intro index valid
  simp [show index = 0 by omega, -BitVec.getLsbD_eq_getElem, scratch sample]
  done

/-- The actual branch selector observes a capture made on this same terminal
edge. No equality of the successor or complete execution is assumed. -/
theorem terminal_branch_matches (i : Values Reactive.Input) (r : Values Reactive.Register)
    (slots : Vector Bool 16) (c : Option (Capture 15)) (sample : Fin 16)
    (cache : r .cachedTerminal = GenericEncoding.capture c)
    (selection : Reactive.branchSample.eval i r = BitVec.ofNat 4 sample.val)
    (scratch : Scratch (r .scratch) slots)
    (terminal : Reactive.terminalEdge.eval i r = 1) :
    Reactive.branchBit.eval i r = BitVec.ofBool (capture slots c (r .stage2))[sample.val] := by
  exact branchBit_matches i r _ sample selection
    (exitScratch_matches i r slots c (cache ▸ capture_fields c) scratch terminal)

end Pinwheel.Hardware.Buffered.GenericPhase
