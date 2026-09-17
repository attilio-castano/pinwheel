import Pinwheel.UART.Rx

namespace Pinwheel.UART.Rx

theorem duration_bounds (cfg : Config) (symbol : Fin 10) :
    0 < duration cfg symbol ∧ duration cfg symbol ≤ 6656 := by
  rcases cfg with ⟨cycles, minimum, maximum, input⟩
  simp only [duration, Config.half]
  split <;> omega
  done

theorem wellFormed_advance (cfg : Config) (s : State) (input : Bool)
    (h : WellFormed cfg s) : WellFormed cfg (advance cfg s input) := by
  grind [WellFormed, advance, finishSymbol, enterSymbol, observe, duration_bounds]
  done

theorem wellFormed_run (cfg : Config) (s : State) (incoming : Nat → Bool)
    (h : WellFormed cfg s) (n : Nat) : WellFormed cfg (run cfg s incoming n) :=
  Nat.recOn n h (fun n ih => wellFormed_advance cfg _ (incoming (n + 1)) ih)

theorem reset_priority (cfg : Config) (s : State) (startRequested input : Bool) :
    step cfg s true startRequested input = reset := rfl

theorem stopped_retains (cfg : Config) (s : State) (input : Bool) (h : busy s = false) :
    step cfg s false false input = s := by
  simp [step, h]
  done

theorem busy_ignores_start (cfg : Config) (s : State) (input : Bool) (h : busy s = true) :
    step cfg s false true input = advance cfg s input := by
  simp [step, h]
  done

theorem run_add (cfg : Config) (s : State) (incoming : Nat → Bool) (a b : Nat) :
    run cfg s incoming (a + b) =
      run cfg (run cfg s incoming a) (fun t => incoming (a + t)) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [Nat.add_succ, run, run, ← ih]
    simp only [Nat.add_assoc]
    done
  done

theorem countdown (cfg : Config) (symbol : Fin 10) (remaining : Fin 6656)
    (slots : Vector Bool 16) (incoming : Nat → Bool) (n : Nat) (h : n ≤ remaining.val) :
    run cfg ⟨.timed symbol, remaining, slots⟩ incoming n =
      ⟨.timed symbol, ⟨remaining.val - n, by omega⟩, slots⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih (by omega), advance, show 0 < remaining.val - n by omega, ↓reduceDIte]
    simp only [Nat.sub_sub]
    done
  done

theorem countdown_boundary (cfg : Config) (symbol : Fin 10) (remaining : Fin 6656)
    (slots : Vector Bool 16) (incoming : Nat → Bool) :
    run cfg ⟨.timed symbol, remaining, slots⟩ incoming (remaining.val + 1) =
      finishSymbol cfg ⟨.timed symbol, 0, slots⟩ symbol (incoming (remaining.val + 1)) := by
  rw [run, countdown cfg symbol remaining slots incoming remaining.val (Nat.le_refl _)]
  simp [advance, Nat.sub_self]
  done

theorem symbol_boundary (cfg : Config) (symbol : Fin 10) (slots : Vector Bool 16)
    (incoming : Nat → Bool) :
    run cfg (enterSymbol cfg ⟨.ready, 0, slots⟩ symbol) incoming (duration cfg symbol) =
      finishSymbol cfg ⟨.timed symbol, 0, slots⟩ symbol (incoming (duration cfg symbol)) := by
  simpa only [enterSymbol, show duration cfg symbol - 1 + 1 = duration cfg symbol from
    Nat.sub_add_cancel (duration_bounds cfg symbol).1] using
    countdown_boundary cfg symbol (enterSymbol cfg ⟨.ready, 0, slots⟩ symbol).remaining slots incoming
  done

theorem bit_boundary (cfg : Config) (symbol : Fin 10) (slots : Vector Bool 16)
    (incoming : Nat → Bool) (h : symbol.val ≠ 0) :
    run cfg (enterSymbol cfg ⟨.ready, 0, slots⟩ symbol) incoming cfg.bitCycles =
      finishSymbol cfg ⟨.timed symbol, 0, slots⟩ symbol (incoming cfg.bitCycles) := by
  simpa only [duration, h, ↓reduceIte] using symbol_boundary cfg symbol slots incoming
  done

theorem sampleSlot_suffix (count : Nat) (h : count < 9) :
    sampleSlot ⟨10 - (count + 1), by omega⟩ = suffixSlot count := by
  grind [sampleSlot, suffixSlot, Fin.ext_iff, Fin.val_ofNat]
  done

/-- A suffix is decoded from its event times, independently of whole-symbol countdown state. -/
theorem receive_suffix (cfg : Config) (count : Nat) (hp : 0 < count) (hb : count ≤ 9)
    (slots : Vector Bool 16) (incoming : Nat → Bool) (elapsed : Nat) :
    run cfg (enterSymbol cfg ⟨.ready, 0, slots⟩ ⟨10 - count, by omega⟩)
      (fun t => incoming (elapsed + t)) (count * cfg.bitCycles) =
      ⟨.finished, 0, collect cfg count elapsed slots incoming⟩ := by
  induction count generalizing slots elapsed with
  | zero => omega
  | succ count ih =>
    rw [(Nat.succ_mul count cfg.bitCycles).trans (Nat.add_comm _ _), run_add,
      bit_boundary cfg ⟨10 - (count + 1), by omega⟩ slots _ (by change 10 - (count + 1) ≠ 0; omega)]
    by_cases hz : count = 0
    case neg =>
      simpa only [finishSymbol, show 10 - (count + 1) ≠ 0 by omega, false_and, ↓reduceIte,
        show 10 - count < 10 by omega, ↓reduceDIte,
        sampleSlot_suffix count (by omega), observe, enterSymbol, collect, ← Nat.add_assoc,
        show 10 - (count + 1) + 1 = 10 - count by omega] using
        ih (by omega) (by omega) (slots.set (suffixSlot count) (incoming (elapsed + cfg.bitCycles)))
          (elapsed + cfg.bitCycles)
    case pos =>
      simp [hz, run, finishSymbol, sampleSlot, observe, collect, suffixSlot]
    done
  done

theorem collected_byte (cfg : Config) (elapsed : Nat) (slots : Vector Bool 16) (incoming : Nat → Bool) :
    received (collect cfg 9 elapsed slots incoming) = expectedByte cfg elapsed incoming := by
  ext i hi
  unfold received expectedByte
  rw [BitVec.getElem_ofBoolListBE, BitVec.getElem_ofBoolListBE]
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases cases with hi | hi | hi | hi | hi | hi | hi | hi
  all_goals simp +decide [hi, collect, suffixSlot, Vector.getElem_set]
  all_goals congr 1 <;> omega
  done

theorem collected_stop (cfg : Config) (elapsed : Nat) (slots : Vector Bool 16) (incoming : Nat → Bool) :
    (collect cfg 9 elapsed slots incoming)[9] = incoming (elapsed + 9 * cfg.bitCycles) := by
  simp +decide [collect, suffixSlot, Vector.getElem_set]
  congr 1
  omega
  done

theorem expected_bit (cfg : Config) (elapsed : Nat) (incoming : Nat → Bool) (bit : Fin 8) :
    (expectedByte cfg elapsed incoming)[bit.val] = incoming (elapsed + (bit.val + 1) * cfg.bitCycles) := by
  unfold expectedByte
  rw [BitVec.getElem_ofBoolListBE]
  have cases : bit.val = 0 ∨ bit.val = 1 ∨ bit.val = 2 ∨ bit.val = 3 ∨ bit.val = 4 ∨
    bit.val = 5 ∨ bit.val = 6 ∨ bit.val = 7 := by omega
  rcases cases with h | h | h | h | h | h | h | h
  all_goals simp [h]
  done

theorem expected_byte_correct (cfg : Config) (elapsed : Nat) (incoming : Nat → Bool)
    (byte : BitVec 8)
    (h : ∀ bit : Fin 8, incoming (elapsed + (bit.val + 1) * cfg.bitCycles) = byte.getLsbD bit.val) :
    expectedByte cfg elapsed incoming = byte := by
  ext i hi
  exact (expected_bit cfg elapsed incoming ⟨i, hi⟩).trans ((h ⟨i, hi⟩).trans (BitVec.getLsbD_eq_getElem hi))
  done

theorem start_confirmation (cfg : Config) (slots : Vector Bool 16) (incoming : Nat → Bool)
    (detected : Nat) :
    run cfg (enterSymbol cfg ⟨.ready, 0, slots⟩ 0) (fun t => incoming (detected + t)) cfg.half =
      if incoming (detected + cfg.half) then
        ⟨.idle, 0, slots.set 8 true⟩
      else enterSymbol cfg ⟨.ready, 0, slots.set 8 false⟩ 1 := by
  cases hi : incoming (detected + cfg.half)
  all_goals simpa [duration, finishSymbol, sampleSlot, observe, enterSymbol, hi,
    show (8 : Fin 16).val = 8 from rfl] using
    symbol_boundary cfg 0 slots (fun t => incoming (detected + t))
  done

theorem receive_after_start (cfg : Config) (slots : Vector Bool 16) (incoming : Nat → Bool)
    (detected : Nat) (startLow : incoming (detected + cfg.half) = false) :
    run cfg (enterSymbol cfg ⟨.ready, 0, slots⟩ 0) (fun t => incoming (detected + t))
      (cfg.half + 9 * cfg.bitCycles) =
      ⟨.finished, 0, collect cfg 9 (detected + cfg.half) (slots.set 8 false) incoming⟩ := by
  rw [run_add, start_confirmation, startLow]
  simpa only [Bool.false_eq_true, ↓reduceIte, Nat.add_assoc,
    show (⟨10 - 9, by decide⟩ : Fin 10) = 1 from rfl] using
    receive_suffix cfg 9 (by decide) (by decide) (slots.set 8 false) incoming (detected + cfg.half)
  done

theorem receive_result (cfg : Config) (slots : Vector Bool 16) (incoming : Nat → Bool)
    (detected : Nat) (startLow : incoming (detected + cfg.half) = false) :
    result (run cfg (enterSymbol cfg ⟨.ready, 0, slots⟩ 0) (fun t => incoming (detected + t))
      (cfg.half + 9 * cfg.bitCycles)) =
      some (if incoming (sampleTime cfg detected 9) then
        .byte (expectedByte cfg (detected + cfg.half) incoming)
      else .framingError (expectedByte cfg (detected + cfg.half) incoming)) := by
  simp [receive_after_start cfg slots incoming detected startLow, result, outcome,
    collected_byte, collected_stop, sampleTime, show (9 : Fin 10).val = 9 from rfl]
  done

/-- Byte recovery assumes the validated start and the explicit data/stop sample contract. -/
theorem frame_correct (cfg : Config) (slots : Vector Bool 16) (incoming : Nat → Bool)
    (detected : Nat) (byte : BitVec 8) (startLow : incoming (detected + cfg.half) = false)
    (frame : SamplesFrame cfg detected incoming byte) :
    result (run cfg (enterSymbol cfg ⟨.ready, 0, slots⟩ 0) (fun t => incoming (detected + t))
      (cfg.half + 9 * cfg.bitCycles)) = some (.byte byte) := by
  rw [receive_result cfg slots incoming detected startLow, frame.2]
  simp only [↓reduceIte, expected_byte_correct cfg (detected + cfg.half) incoming byte (fun bit => frame.1 bit)]
  done

theorem waiting_high (cfg : Config) (incoming : Nat → Bool) (n : Nat)
    (high : ∀ t, 1 ≤ t → t ≤ n + 1 → incoming t = true) :
    run cfg initial incoming (n + 1) =
      ⟨.falling, 0, (Vector.replicate 16 false).set 8 true⟩ := by
  induction n with
  | zero => simp +decide [run, initial, advance, observe, high 1 (by omega) (by omega)]
  | succ n ih =>
    rw [run, ih (fun t ht hb => high t ht (by omega))]
    simp +decide [advance, observe, high (n + 1 + 1) (by omega) (by omega)]
  done

theorem detect_start (cfg : Config) (incoming : Nat → Bool) (detected : Nat)
    (later : 2 ≤ detected) (high : ∀ t, 1 ≤ t → t < detected → incoming t = true)
    (low : incoming detected = false) :
    run cfg initial incoming detected =
      enterSymbol cfg ⟨.ready, 0, Vector.replicate 16 false⟩ 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show detected ≠ 0 by omega)
  rw [run, show run cfg initial incoming n =
      ⟨.falling, 0, (Vector.replicate 16 false).set 8 true⟩ from by
    simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega)] using
      waiting_high cfg incoming (n - 1) (fun t ht hb => high t ht (by omega))]
  simp [advance, observe, low, enterSymbol, show (8 : Fin 16).val = 8 from rfl]
  done

/-- Complete byte recovery from the armed interface with an observed idle prefix. -/
theorem armed_frame_correct (cfg : Config) (incoming : Nat → Bool) (detected : Nat)
    (byte : BitVec 8) (later : 2 ≤ detected)
    (high : ∀ t, 1 ≤ t → t < detected → incoming t = true)
    (low : incoming detected = false) (startLow : incoming (detected + cfg.half) = false)
    (frame : SamplesFrame cfg detected incoming byte) :
    result (run cfg initial incoming (detected + (cfg.half + 9 * cfg.bitCycles))) = some (.byte byte) := by
  rw [run_add, detect_start cfg incoming detected later high low]
  exact frame_correct cfg _ incoming detected byte startLow frame
  done

end Pinwheel.UART.Rx
