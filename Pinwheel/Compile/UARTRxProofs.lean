import Pinwheel.Compile.UARTRx

namespace Pinwheel.Compile.UARTRx
open Engine.Reactive
open UART.Rx (Config)

def chunkOffset (cfg : Config) (symbol : Fin 10) (remaining : Nat) : Nat :=
  (UART.Rx.duration cfg symbol - 1) / 256 - remaining / 256

def timedPC (cfg : Config) (symbol : Fin 10) (remaining : Nat) : Nat :=
  base cfg symbol + chunkOffset cfg symbol remaining

def liftControl (cfg : Config) (s : UART.Rx.State) : Control 255 :=
  match s.phase with
  | .ready => .stopped .ready
  | .finished => .stopped .completed
  | .idle => .checked 0 0
  | .falling => .checked 1 0
  | .timed symbol =>
    if s.remaining.val < 256 then
      .checked (address (timedPC cfg symbol s.remaining.val)) (Fin.ofNat 256 s.remaining.val)
    else .active (address (timedPC cfg symbol s.remaining.val)) (Fin.ofNat 256 s.remaining.val)

def lift (cfg : Config) (s : UART.Rx.State) : RxState :=
  ⟨liftControl cfg s, {}, s.samples⟩

theorem layout_bounds (cfg : Config) :
    1 ≤ halfChunks cfg ∧ 1 ≤ bitChunks cfg ∧ haltPC cfg < 256 := by
  rcases cfg with ⟨cycles, minimum, maximum, input⟩
  simp only [halfChunks, bitChunks, haltPC, chunks, UART.Rx.Config.half]
  omega
  done

theorem symbol_bounds (cfg : Config) (symbol : Fin 10) :
    2 ≤ base cfg symbol ∧
      base cfg symbol + chunks (UART.Rx.duration cfg symbol) ≤ haltPC cfg := by
  have hm := Nat.mul_le_mul_right (bitChunks cfg) (show symbol.val - 1 ≤ 8 by omega)
  simp only [base, UART.Rx.duration, haltPC]
  split <;> simp_all [halfChunks, bitChunks]
  omega
  done

theorem address_val (n : Nat) (h : n < 256) : (address n).val = n := by
  simp [address, Fin.val_ofNat, Nat.mod_eq_of_lt h]
  done

theorem fetch_idle (cfg : Config) : (program cfg).fetch 0 = poll cfg 1 0 := by
  simp [program, Program.fetch, instruction]
  done

theorem fetch_falling (cfg : Config) : (program cfg).fetch 1 = poll cfg 1 2 := by
  simp [program, Program.fetch, instruction]
  done

theorem fetch_timed (cfg : Config) (symbol : Fin 10) (offset : Nat)
    (h : offset < chunks (UART.Rx.duration cfg symbol)) :
    (program cfg).fetch (address (base cfg symbol + offset)) = timedInstruction cfg symbol offset := by
  have bounds := symbol_bounds cfg symbol
  have capacity := layout_bounds cfg
  simp only [program, Program.fetch, Vector.getElem_ofFn, instruction,
    address_val (base cfg symbol + offset) (by omega), show base cfg symbol + offset ≠ 0 by omega,
    show base cfg symbol + offset ≠ 1 by omega,
    show base cfg symbol + offset < haltPC cfg by omega, ↓reduceIte]
  by_cases hs : symbol.val = 0
  all_goals simp only [base, UART.Rx.duration, hs, ↓reduceIte] at h ⊢
  case neg =>
    simp only [show ¬(2 + halfChunks cfg + (symbol.val - 1) * bitChunks cfg + offset <
      2 + halfChunks cfg) by omega, ↓reduceIte,
      show 2 + halfChunks cfg + (symbol.val - 1) * bitChunks cfg + offset -
        (2 + halfChunks cfg) = offset + (symbol.val - 1) * bitChunks cfg by omega]
    simp only [Nat.add_mul_div_right _ _ (show 0 < bitChunks cfg by omega),
      Nat.div_eq_of_lt (show offset < bitChunks cfg from h), Nat.zero_add,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (show offset < bitChunks cfg from h),
      show symbol.val - 1 + 1 = symbol.val by omega, Fin.ofNat_val_eq_self]
    done
  case pos =>
    simp [show symbol = 0 from Fin.ext hs, halfChunks] at h ⊢
    omega
    done
  done

theorem chunk_bounds (cfg : Config) (symbol : Fin 10) (remaining : Nat)
    (h : remaining < UART.Rx.duration cfg symbol) :
    chunkOffset cfg symbol remaining < chunks (UART.Rx.duration cfg symbol) := by
  simp only [chunkOffset, chunks]
  omega
  done

theorem final_chunk (cfg : Config) (symbol : Fin 10) (remaining : Nat)
    (h : remaining < UART.Rx.duration cfg symbol) :
    (chunkOffset cfg symbol remaining + 1 < chunks (UART.Rx.duration cfg symbol)) ↔
      ¬remaining < 256 := by
  simp only [chunkOffset, chunks]
  omega
  done

theorem entry_timer (cfg : Config) (symbol : Fin 10) (remaining : Nat)
    (h : remaining < UART.Rx.duration cfg symbol)
    (entry : remaining = UART.Rx.duration cfg symbol - 1 ∨ remaining % 256 = 255) :
    (if chunkOffset cfg symbol remaining = 0 then
      Fin.ofNat 256 (UART.Rx.duration cfg symbol - 1) else 255) = Fin.ofNat 256 remaining := by
  apply Fin.ext
  split <;> simp_all only [chunkOffset, Fin.val_ofNat, Fin.isValue]
  all_goals omega
  done

theorem enter_chunk (cfg : Config) (symbol : Fin 10) (remaining : Fin 6656)
    (slots : Vector Bool 16) (inputs : Inputs)
    (h : remaining.val < UART.Rx.duration cfg symbol)
    (entry : remaining.val = UART.Rx.duration cfg symbol - 1 ∨ remaining.val % 256 = 255) :
    enter (program cfg) (address (timedPC cfg symbol remaining.val)) slots inputs =
      lift cfg ⟨.timed symbol, remaining, slots⟩ := by
  simp only [timedPC, enter, fetch_timed cfg symbol _ (chunk_bounds cfg symbol remaining.val h),
    timedInstruction, final_chunk cfg symbol remaining.val h, entry_timer cfg symbol remaining.val h entry,
    lift, liftControl]
  by_cases hr : remaining.val < 256 <;> simp_all [capture]
  done

theorem enter_symbol (cfg : Config) (s : UART.Rx.State) (symbol : Fin 10) (inputs : Inputs) :
    enter (program cfg) (address (base cfg symbol)) s.samples inputs =
      lift cfg (UART.Rx.enterSymbol cfg s symbol) := by
  simpa [UART.Rx.enterSymbol, timedPC, chunkOffset] using
    enter_chunk cfg symbol (UART.Rx.enterSymbol cfg s symbol).remaining s.samples inputs
      (by have := UART.Rx.duration_bounds cfg symbol; simp [UART.Rx.enterSymbol]; omega)
      (Or.inl rfl)
  done

theorem fetch_halt (cfg : Config) : (program cfg).fetch (address (haltPC cfg)) = .halt := by
  have h := layout_bounds cfg
  simp only [program, Program.fetch, Vector.getElem_ofFn, instruction,
    address_val (haltPC cfg) h.2.2]
  simp [haltPC, show 2 + halfChunks cfg + 9 * bitChunks cfg ≠ 1 by omega,
    show ¬(2 + halfChunks cfg + 9 * bitChunks cfg < 2 + halfChunks cfg) by omega]
  done

theorem enter_idle (cfg : Config) (slots : Vector Bool 16) (inputs : Inputs) :
    enter (program cfg) 0 slots inputs = lift cfg ⟨.idle, 0, slots⟩ := by
  simp [enter, fetch_idle, poll, lift, liftControl, capture]
  done

theorem enter_falling (cfg : Config) (slots : Vector Bool 16) (inputs : Inputs) :
    enter (program cfg) 1 slots inputs = lift cfg ⟨.falling, 0, slots⟩ := by
  simp [enter, fetch_falling, poll, lift, liftControl, capture]
  done

theorem enter_halt (cfg : Config) (slots : Vector Bool 16) (inputs : Inputs) :
    enter (program cfg) (address (haltPC cfg)) slots inputs = lift cfg ⟨.finished, 0, slots⟩ := by
  simp only [enter, fetch_halt, lift, liftControl, stop]
  rfl
  done

theorem capture_correct (cfg : Config) (slots : Vector Bool 16) (slot : Fin 16) (inputs : Inputs) :
    capture slots (some (captureAt cfg slot)) inputs = slots.set slot inputs[cfg.input.val] := by
  ext i hi
  simp [capture, captureAt, Engine.capture, Fin.ext_iff, Vector.getElem_set]
  done

theorem last_val (cfg : Config) : (program cfg).last.val = haltPC cfg :=
  address_val _ (layout_bounds cfg).2.2

theorem jump_eq (cfg : Config) (pc : Nat) (slots : Vector Bool 16) (inputs : Inputs)
    (h : pc ≤ haltPC cfg) :
    jump (program cfg) (address pc) slots inputs = enter (program cfg) (address pc) slots inputs := by
  simp [jump, last_val, address_val pc (Nat.lt_of_le_of_lt h (layout_bounds cfg).2.2), h]
  done

theorem next_eq (cfg : Config) (pc : Nat) (slots : Vector Bool 16) (inputs : Inputs)
    (h : pc < haltPC cfg) :
    next (program cfg) (address pc) slots inputs = enter (program cfg) (address (pc + 1)) slots inputs := by
  simp only [next, last_val, address_val pc (Nat.lt_trans h (layout_bounds cfg).2.2), dif_pos h]
  congr 1
  exact Fin.ext (address_val (pc + 1) (Nat.lt_of_le_of_lt h (layout_bounds cfg).2.2)).symm
  done

theorem unguarded (inputs : Inputs) : (Check.mk 0 0).ready inputs = true := by
  simp [Check.ready]
  done

theorem two_le_halt (cfg : Config) : 2 ≤ haltPC cfg :=
  Nat.le_trans (Nat.le_add_right 2 (halfChunks cfg))
    (Nat.le_add_right (2 + halfChunks cfg) (9 * bitChunks cfg))

theorem advance_falling (cfg : Config) (slots : Vector Bool 16) (inputs : Inputs) :
    advance (program cfg) (lift cfg ⟨.falling, 0, slots⟩) inputs =
      lift cfg (UART.Rx.advance cfg ⟨.falling, 0, slots⟩ inputs[cfg.input.val]) := by
  change advance (program cfg) ⟨.checked 1 0, {}, slots⟩ inputs = _
  simp [advance, fetch_falling, poll, Check.ready, dispatch, capture_correct, UART.Rx.advance]
  cases hi : inputs[cfg.input.val] <;> simp only [Bool.false_eq_true, ↓reduceIte]
  case false =>
    exact (jump_eq cfg 2 _ inputs (two_le_halt cfg)).trans
      (enter_symbol cfg (UART.Rx.observe ⟨.falling, 0, slots⟩ 8 false) 0 inputs)
  case true =>
    exact (jump_eq cfg 1 _ inputs (Nat.le_trans (by decide) (two_le_halt cfg))).trans
      (enter_falling cfg _ inputs)
  done

theorem advance_idle (cfg : Config) (slots : Vector Bool 16) (inputs : Inputs) :
    advance (program cfg) (lift cfg ⟨.idle, 0, slots⟩) inputs =
      lift cfg (UART.Rx.advance cfg ⟨.idle, 0, slots⟩ inputs[cfg.input.val]) := by
  change advance (program cfg) ⟨.checked 0 0, {}, slots⟩ inputs = _
  simp [advance, fetch_idle, poll, Check.ready, dispatch, capture_correct, UART.Rx.advance]
  cases hi : inputs[cfg.input.val] <;> simp only [Bool.false_eq_true, ↓reduceIte]
  case false =>
    exact (jump_eq cfg 0 _ inputs (Nat.zero_le _)).trans (enter_idle cfg _ inputs)
  case true =>
    exact (jump_eq cfg 1 _ inputs (Nat.le_trans (by decide) (two_le_halt cfg))).trans
      (enter_falling cfg _ inputs)
  done

theorem countdown_arithmetic (duration remaining : Nat) (h : remaining < duration)
    (hp : 0 < remaining % 256) :
    (duration - 1) / 256 - remaining / 256 = (duration - 1) / 256 - (remaining - 1) / 256 ∧
    (remaining - 1) % 256 = remaining % 256 - 1 ∧
    (remaining < 256 ↔ remaining - 1 < 256) := by
  omega
  done

theorem timed_pc_bound (cfg : Config) (symbol : Fin 10) (remaining : Nat)
    (h : remaining < UART.Rx.duration cfg symbol) : timedPC cfg symbol remaining < haltPC cfg := by
  have hs := symbol_bounds cfg symbol
  exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (chunk_bounds cfg symbol remaining h) _) hs.2
  done

theorem advance_countdown (cfg : Config) (symbol : Fin 10) (remaining : Fin 6656)
    (slots : Vector Bool 16) (inputs : Inputs)
    (h : remaining.val < UART.Rx.duration cfg symbol) (hp : 0 < remaining.val % 256) :
    advance (program cfg) (lift cfg ⟨.timed symbol, remaining, slots⟩) inputs =
      lift cfg ⟨.timed symbol, ⟨remaining.val - 1, by omega⟩, slots⟩ := by
  have arithmetic := countdown_arithmetic (UART.Rx.duration cfg symbol) remaining.val h hp
  by_cases small : remaining.val < 256
  all_goals simp only [lift, liftControl, ← arithmetic.2.2, small, ↓reduceIte,
    advance, timedPC, fetch_timed cfg symbol _ (chunk_bounds cfg symbol remaining.val h),
    timedInstruction, final_chunk cfg symbol remaining.val h, Fin.val_ofNat, hp, ↓reduceDIte]
  all_goals try simp only [not_true_eq_false, ↓reduceIte, unguarded, Bool.not_true, Bool.false_eq_true]
  all_goals simp only [State.mk.injEq, Control.checked.injEq, Control.active.injEq,
    and_true, chunkOffset, ← arithmetic.1, Fin.ext_iff, Fin.val_ofNat]
  all_goals exact ⟨True.intro, arithmetic.2.1.symm⟩
  done

theorem advance_chunk (cfg : Config) (symbol : Fin 10) (remaining : Fin 6656)
    (slots : Vector Bool 16) (inputs : Inputs)
    (h : remaining.val < UART.Rx.duration cfg symbol)
    (hp : 0 < remaining.val) (hz : remaining.val % 256 = 0) :
    advance (program cfg) (lift cfg ⟨.timed symbol, remaining, slots⟩) inputs =
      lift cfg ⟨.timed symbol, ⟨remaining.val - 1, by omega⟩, slots⟩ := by
  conv => lhs; simp only [lift, liftControl, show ¬remaining.val < 256 by omega, ↓reduceIte]
  simp only [advance, Fin.val_ofNat, hz, Nat.lt_irrefl, ↓reduceDIte,
    next_eq cfg _ slots inputs (timed_pc_bound cfg symbol remaining.val h)]
  have pcStep : timedPC cfg symbol remaining.val + 1 = timedPC cfg symbol (remaining.val - 1) := by
    simp only [timedPC, chunkOffset]
    omega
    done
  simpa only [pcStep] using enter_chunk cfg symbol ⟨remaining.val - 1, by omega⟩ slots inputs
    (show remaining.val - 1 < UART.Rx.duration cfg symbol by omega)
    (Or.inr (by change (remaining.val - 1) % 256 = 255; omega))
  done

theorem base_next (cfg : Config) (symbol : Fin 10) (h : symbol.val + 1 < 10) :
    timedPC cfg symbol 0 + 1 = base cfg ⟨symbol.val + 1, h⟩ := by
  have cases : symbol.val = 0 ∨ symbol.val = 1 ∨ symbol.val = 2 ∨ symbol.val = 3 ∨
      symbol.val = 4 ∨ symbol.val = 5 ∨ symbol.val = 6 ∨ symbol.val = 7 ∨ symbol.val = 8 := by omega
  rcases cases with hs | hs | hs | hs | hs | hs | hs | hs | hs
  all_goals simp [timedPC, chunkOffset, base, UART.Rx.duration, halfChunks, bitChunks, chunks, hs]
  all_goals omega
  done

theorem base_last (cfg : Config) : timedPC cfg 9 0 + 1 = haltPC cfg := by
  simp [timedPC, chunkOffset, base, UART.Rx.duration, halfChunks, bitChunks, haltPC, chunks,
    show (9 : Fin 10).val = 9 from rfl]
  omega
  done

theorem fetch_current (cfg : Config) (symbol : Fin 10) (remaining : Nat)
    (h : remaining < UART.Rx.duration cfg symbol) :
    (program cfg).fetch (address (timedPC cfg symbol remaining)) =
      timedInstruction cfg symbol (chunkOffset cfg symbol remaining) :=
  fetch_timed cfg symbol _ (chunk_bounds cfg symbol remaining h)

theorem advance_terminal (cfg : Config) (symbol : Fin 10) (slots : Vector Bool 16) (inputs : Inputs) :
    advance (program cfg) (lift cfg ⟨.timed symbol, 0, slots⟩) inputs =
      lift cfg (UART.Rx.finishSymbol cfg ⟨.timed symbol, 0, slots⟩ symbol inputs[cfg.input.val]) := by
  change advance (program cfg) ⟨.checked (address (timedPC cfg symbol 0)) 0, {}, slots⟩ inputs = _
  simp only [advance, fetch_current cfg symbol 0 (UART.Rx.duration_bounds cfg symbol).1,
    timedInstruction, final_chunk cfg symbol 0 (UART.Rx.duration_bounds cfg symbol).1,
    show (0 < 256) from by decide, not_true_eq_false, ↓reduceIte, unguarded,
    Bool.not_true, Bool.false_eq_true, Fin.val_zero, Nat.lt_irrefl, ↓reduceDIte, capture_correct]
  by_cases hs : symbol.val = 0
  case neg =>
    simp only [hs, ↓reduceIte, dispatch, UART.Rx.finishSymbol, false_and,
      next_eq cfg _ _ inputs (timed_pc_bound cfg symbol 0 (UART.Rx.duration_bounds cfg symbol).1)]
    split
    next hn =>
      simpa only [base_next cfg symbol hn, UART.Rx.observe] using
        enter_symbol cfg (UART.Rx.observe ⟨.timed symbol, 0, slots⟩ (UART.Rx.sampleSlot symbol)
          inputs[cfg.input.val]) ⟨symbol.val + 1, hn⟩ inputs
    next hn =>
      simpa only [show symbol = 9 from Fin.ext (by omega), base_last, UART.Rx.observe] using
        enter_halt cfg (slots.set (UART.Rx.sampleSlot symbol) inputs[cfg.input.val]) inputs
    done
  case pos =>
    simp [show symbol = 0 from Fin.ext hs, dispatch, UART.Rx.finishSymbol, UART.Rx.sampleSlot]
    cases hi : inputs[cfg.input.val] <;> simp only [Bool.false_eq_true, ↓reduceIte]
    case false =>
      exact (jump_eq cfg (base cfg 1) _ inputs
        (Nat.le_trans (Nat.le_add_right _ _) (symbol_bounds cfg 1).2)).trans
        (enter_symbol cfg (UART.Rx.observe ⟨.timed 0, 0, slots⟩ 8 false) 1 inputs)
    case true =>
      exact (jump_eq cfg 0 _ inputs (Nat.zero_le _)).trans (enter_idle cfg _ inputs)
    done
  done

theorem advance_timed (cfg : Config) (symbol : Fin 10) (remaining : Fin 6656)
    (slots : Vector Bool 16) (inputs : Inputs) (h : remaining.val < UART.Rx.duration cfg symbol) :
    advance (program cfg) (lift cfg ⟨.timed symbol, remaining, slots⟩) inputs =
      lift cfg (UART.Rx.advance cfg ⟨.timed symbol, remaining, slots⟩ inputs[cfg.input.val]) := by
  by_cases hz : remaining.val = 0
  case neg =>
    by_cases hm : remaining.val % 256 = 0
    case pos =>
      simpa only [UART.Rx.advance, show 0 < remaining.val by omega, ↓reduceDIte] using
        advance_chunk cfg symbol remaining slots inputs h (by omega) hm
    case neg =>
      simpa only [UART.Rx.advance, show 0 < remaining.val by omega, ↓reduceDIte] using
        advance_countdown cfg symbol remaining slots inputs h (by omega)
    done
  case pos =>
    simpa [show remaining = 0 from Fin.ext hz, UART.Rx.advance] using
      advance_terminal cfg symbol slots inputs
  done

theorem advance_simulation (cfg : Config) (s : UART.Rx.State) (inputs : Inputs)
    (h : UART.Rx.WellFormed cfg s) :
    advance (program cfg) (lift cfg s) inputs = lift cfg (UART.Rx.advance cfg s inputs[cfg.input.val]) := by
  rcases s with ⟨phase, remaining, slots⟩
  cases phase
  case timed symbol => exact advance_timed cfg symbol remaining slots inputs h
  case ready => rfl
  case finished => rfl
  case idle => simpa only [show remaining = 0 from Fin.ext h] using advance_idle cfg slots inputs
  case falling => simpa only [show remaining = 0 from Fin.ext h] using advance_falling cfg slots inputs
  done

theorem start_simulation (cfg : Config) (inputs : Inputs) :
    start (program cfg) inputs = lift cfg UART.Rx.initial :=
  enter_idle cfg _ inputs

theorem reset_simulation (cfg : Config) : reset (program cfg) = lift cfg UART.Rx.reset := rfl

theorem run_simulation (cfg : Config) (s : UART.Rx.State) (incoming : Nat → Inputs)
    (h : UART.Rx.WellFormed cfg s) (n : Nat) :
    run (program cfg) (lift cfg s) incoming n =
      lift cfg (UART.Rx.run cfg s (fun t => (incoming t)[cfg.input.val]) n) :=
  Nat.recOn n rfl (fun n ih => by
    simpa only [run, UART.Rx.run, ih] using advance_simulation cfg
      (UART.Rx.run cfg s (fun t => (incoming t)[cfg.input.val]) n) (incoming (n + 1))
      (UART.Rx.wellFormed_run cfg s _ h n))

theorem execute_simulation (cfg : Config) (incoming : Nat → Inputs) (n : Nat) :
    execute cfg incoming n =
      lift cfg (UART.Rx.run cfg UART.Rx.initial (fun t => (incoming t)[cfg.input.val]) n) := by
  simpa only [execute, start_simulation] using run_simulation cfg UART.Rx.initial incoming rfl n
  done

theorem busy_lift (cfg : Config) (s : UART.Rx.State) : busy (lift cfg s) = UART.Rx.busy s := by
  grind [lift, liftControl, busy, UART.Rx.busy]
  done

theorem result_lift (cfg : Config) (s : UART.Rx.State) : result (lift cfg s) = UART.Rx.result s := by
  grind [lift, liftControl, result, UART.Rx.result]
  done

theorem step_simulation (cfg : Config) (s : UART.Rx.State)
    (resetRequested startRequested : Bool) (inputs : Inputs) (h : UART.Rx.WellFormed cfg s) :
    step (program cfg) (lift cfg s) resetRequested startRequested inputs =
      lift cfg (UART.Rx.step cfg s resetRequested startRequested inputs[cfg.input.val]) := by
  simp only [step, UART.Rx.step, busy_lift, reset_simulation, start_simulation,
    advance_simulation cfg s inputs h]
  split <;> (first | rfl | split <;> (first | rfl | split <;> rfl))
  done

theorem result_correct (cfg : Config) (incoming : Nat → Inputs) (n : Nat) :
    result (execute cfg incoming n) =
      UART.Rx.result (UART.Rx.run cfg UART.Rx.initial (fun t => (incoming t)[cfg.input.val]) n) := by
  rw [execute_simulation, result_lift]
  done

theorem outputs_released (cfg : Config) (incoming : Nat → Inputs) (n : Nat) :
    (execute cfg incoming n).pins = {} := by
  simp [execute_simulation, lift]
  done

theorem byte_correct (cfg : Config) (incoming : Nat → Inputs) (detected : Nat)
    (byte : BitVec 8) (later : 2 ≤ detected)
    (high : ∀ t, 1 ≤ t → t < detected → (incoming t)[cfg.input.val] = true)
    (low : (incoming detected)[cfg.input.val] = false)
    (startLow : (incoming (detected + cfg.half))[cfg.input.val] = false)
    (frame : UART.Rx.SamplesFrame cfg detected (fun t => (incoming t)[cfg.input.val]) byte) :
    result (execute cfg incoming (detected + (cfg.half + 9 * cfg.bitCycles))) = some (.byte byte) := by
  rw [result_correct]
  exact UART.Rx.armed_frame_correct cfg _ detected byte later high low startLow frame
  done

end Pinwheel.Compile.UARTRx
