import Pinwheel.Hardware.CoreProofs

namespace Pinwheel.Hardware.Core

theorem entry_refines (p : Raw.Program) (s : Engine.State) (address : BitVec 5)
    (clear : Bool) (i : Inputs) :
    entryValue address clear i (embed p s) =
      embed p (Raw.enter p address.toFin
        (if clear then Vector.replicate 8 false else s.samples) i.sample) := by
  simp only [entryValue, enterValue, embed, Decode.value_correct, Raw.enter, BitVec.toNat]
  cases h : Encoding.decode p.memory[address.toFin.val] with
  | none => rfl
  | some inst => cases inst <;> rfl
  done

theorem successor (pc : Fin 32) (h : pc.val + 1 < 32) :
    BitVec.ofFin pc - 31#5 = BitVec.ofFin (⟨pc.val + 1, h⟩ : Fin 32) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub]
  omega
  done

theorem advance_refines (p : Raw.Program) (pc : Fin 32) (remaining : Fin 256)
    (levels : Engine.Levels) (slots : Engine.Samples) (i : Inputs) :
    advanceValue i (embed p ⟨.active pc remaining, levels, slots⟩) =
      embed p (Raw.advance p ⟨.active pc remaining, levels, slots⟩ i.sample) := by
  simp only [advanceValue, Raw.advance]
  simp only [entry_refines, Bool.false_eq_true, ↓reduceIte]
  by_cases hr : 0 < remaining.val <;>
    simp [embed, stoppedValue, BitVec.toNat_eq, hr, Raw.next,
      Countdown.tick, Countdown.circuit, Circuit.step, Expr.eval, Countdown.progressing,
      Countdown.nonzero, Countdown.Inputs.values, Countdown.State.values]
  all_goals simp only [Fin.ext_iff, Fin.val_zero]
  all_goals simp_all
  case pos =>
    have hn : remaining ≠ 0 := by omega
    simp [hn, State.mk.injEq, Countdown.State.mk.injEq, BitVec.toNat_eq]
    omega
    done
  case neg =>
    by_cases hp : pc.val + 1 < 32
    · have hs : pc - 31 = (⟨pc.val + 1, hp⟩ : Fin 32) := congrArg BitVec.toFin (successor pc hp)
      simp [hp, hs, show pc.val ≠ 31 by omega]
      done
    · simp [show pc.val = 31 by omega]
    done
  done

/-- Exact edge correspondence for execution after a committed image, including reset/start. -/
theorem tick_refines (p : Raw.Program) (s : Engine.State) (rst start sample : Bool) :
    tick {reset := rst, start := start, sample := sample} (embed p s) =
      embed p (Raw.step p s rst start sample) := by
  rw [tick_eq_stepValue]
  rcases s with ⟨control, levels, slots⟩
  cases control <;> simp only [stepValue, Raw.step, Engine.busy, Bool.false_eq_true, ↓reduceIte]
  all_goals simp only [entry_refines, advance_refines]
  case stopped reason => cases reason <;> cases rst <;> cases start <;> rfl
  case active pc remaining => cases rst <;> rfl
  done

theorem initialize_priority (i : Inputs) (s : State) (h : i.init = true) :
    tick i s = coldValue s := by
  simp [tick_eq_stepValue, stepValue, h]

theorem commit_stopped (i : Inputs) (s : State) (hi : i.init = false) (hr : i.reset = false)
    (hb : s.status ≠ 1#2) (hc : i.commit = true) :
    tick i s = embed i.image (Raw.reset i.image) := by
  simp [tick_eq_stepValue, stepValue, hi, hr, hb, hc, commitValue, stoppedValue, embed, Raw.reset]

theorem busy_ignores_commit (p : Raw.Program) (pc : Fin 32) (remaining : Fin 256)
    (levels : Engine.Levels) (slots : Engine.Samples) (i : Inputs)
    (hi : i.init = false) (hr : i.reset = false) :
    tick i (embed p ⟨.active pc remaining, levels, slots⟩) =
      embed p (Raw.advance p ⟨.active pc remaining, levels, slots⟩ i.sample) := by
  rw [tick_eq_stepValue]
  simp only [stepValue, hi, hr, Bool.false_eq_true, ↓reduceIte]
  exact advance_refines p pc remaining levels slots i
  done

def run (s : State) (incoming : Nat → Bool) : Nat → State
  | 0 => s
  | n + 1 => tick {sample := incoming (n + 1)} (run s incoming n)

theorem run_refines (p : Raw.Program) (s : Engine.State) (incoming : Nat → Bool) (n : Nat) :
    run (embed p s) incoming n = embed p (Raw.run p s incoming n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run, ih, tick_refines]
    cases h : (Raw.run p s incoming n).control <;> simp [Raw.step, Raw.run, Engine.busy, Raw.advance, h]
    done

/-- Arbitrary encoded programs and input histories inherit the engine's exact trace. -/
theorem run_encoded (p : Engine.Program) (s : Engine.State) (incoming : Nat → Bool) (n : Nat) :
    view (run (embed (Raw.encodeProgram p) s) incoming n) = Engine.run p s incoming n := by
  rw [run_refines, Raw.run_encoded, view_embed]

theorem start_encoded (p : Engine.Program) (s : Engine.State) (sample : Bool) :
    tick {start := true, sample := sample} (embed (Raw.encodeProgram p) s) =
      embed (Raw.encodeProgram p) (Engine.step p s false true sample) := by
  rw [tick_refines, Raw.step_encoded]

theorem invalid_start_ignored (i : Inputs) (s : State) (hi : i.init = false)
    (hr : i.reset = false) (hc : i.commit = false) (hv : s.valid = false) (hs : s.status = 0#2) :
    tick i s = s := by
  simp [tick_eq_stepValue, stepValue, hi, hr, hc, hv, hs]

end Pinwheel.Hardware.Core
