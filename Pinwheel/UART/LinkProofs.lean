import Pinwheel.UART.Link
import Pinwheel.UART.LinkTiming
import Pinwheel.UART.RxProofs

namespace Pinwheel.UART.Link

theorem observe_symbol (t : Timing) (source : Nat → Bool) (byte : BitVec 8)
    (age : Nat → Nat) (cycle : Nat) (symbol : Fin 10)
    (wave : ∀ n, source n = UART.expected t.tx byte n)
    (window : t.txStart + age cycle + symbol.val * t.txBit ≤ t.edge cycle ∧
      t.edge cycle < t.txStart + age cycle + (symbol.val + 1) * t.txBit) :
    observe t source age cycle = (UART.frame byte).getD symbol.val true := by
  have afterStart : t.txStart + age cycle ≤ t.edge cycle :=
    Nat.le_trans (Nat.le_add_right _ _) window.1
  have quotient : (t.edge cycle - (t.txStart + age cycle)) / t.txBit = symbol.val :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  simp only [observe, Nat.not_lt_of_ge afterStart, ↓reduceIte, wave, UART.expected,
    Nat.div_div_eq_div_mul, show t.txTick * t.tx.cycles = t.txBit from Nat.mul_comm _ _, quotient]
  done

theorem first_low_or_high (incoming : Nat → Bool) (n : Nat) :
    (∀ i, 1 ≤ i → i ≤ n → incoming i = true) ∨
      (∃ d, 1 ≤ d ∧ d ≤ n ∧ incoming d = false ∧
        ∀ i, 1 ≤ i → i < d → incoming i = true) := by
  induction n with
  | zero => grind
  | succ n ih =>
    cases last : incoming (n + 1)
    all_goals grind

theorem before_detection_high (t : Timing) (b : Latency) (source : Nat → Bool)
    (age : Nat → Nat) (safe : Safe t b) (within : b.Contains age)
    (n : Nat) (before : n < firstEdge t b.earliest) : observe t source age n = true := by
  simp only [observe, if_pos (Nat.lt_of_lt_of_le
    (edge_before_first t b.earliest n (armed_phase t b safe) before)
    (Nat.add_le_add_left (within n).1 t.txStart))]
  done

theorem start_detection (t : Timing) (b : Latency) (source : Nat → Bool)
    (byte : BitVec 8) (age : Nat → Nat)
    (wave : ∀ n, source n = UART.expected t.tx byte n)
    (safe : Safe t b) (within : b.Contains age) :
    ∃ d, firstEdge t b.earliest ≤ d ∧ d ≤ firstEdge t b.latest ∧ 2 ≤ d ∧
      (∀ n, 1 ≤ n → n < d → observe t source age n = true) ∧ observe t source age d = false := by
  have latestLow := observe_symbol t source byte age (firstEdge t b.latest) 0 wave
    (by simpa using latest_start_window t b safe age within)
  simp [UART.frame, Array.getD] at latestLow
  have positive : 1 ≤ firstEdge t b.latest := Nat.succ_le_succ (Nat.zero_le _)
  have armedHigh : observe t source age 1 = true := if_pos
    (Nat.lt_of_lt_of_le safe.1 (Nat.add_le_add_left (within 1).1 t.txStart))
  have prefixHigh := before_detection_high t b source age safe within
  have first := first_low_or_high (observe t source age) (firstEdge t b.latest)
  grind
  done

theorem frame_data (byte : BitVec 8) (bit : Fin 8) :
    (UART.frame byte).getD (bit.val + 1) true = byte.getLsbD bit.val := by
  simpa only [UART.pin, show bit.val + 1 ≠ 0 by omega, show bit.val + 1 ≠ 9 by omega,
    ↓reduceIte, Nat.add_sub_cancel] using
    (UART.pin_symbol ⟨0⟩ byte ⟨bit.val + 1, by omega⟩ ⟨0, by decide⟩).symm
  done

theorem sampling_contract (t : Timing) (b : Latency) (source : Nat → Bool)
    (byte : BitVec 8) (age : Nat → Nat) (detected : Nat)
    (wave : ∀ n, source n = UART.expected t.tx byte n)
    (safe : Safe t b) (within : b.Contains age)
    (lo : firstEdge t b.earliest ≤ detected) (hi : detected ≤ firstEdge t b.latest) :
    observe t source age (detected + t.rx.half) = false ∧
      Rx.SamplesFrame t.rx detected (observe t source age) byte := by
  have observations (symbol : Fin 10) := observe_symbol t source byte age
    (Rx.sampleTime t.rx detected symbol) symbol wave (observation_window t b safe age within detected lo hi symbol)
  exact ⟨by simpa [Rx.sampleTime, UART.frame, Array.getD] using observations 0,
    (fun bit => (observations ⟨bit.val + 1, by omega⟩).trans (frame_data byte bit)),
    by simpa [UART.frame, Array.getD, show (9 : Fin 10).val = 9 from rfl] using observations 9⟩
  done

/-- Start detection and every sampled bit follow from waveform and numerical timing bounds. -/
theorem receive_correct (t : Timing) (b : Latency) (source : Nat → Bool)
    (byte : BitVec 8) (age : Nat → Nat)
    (wave : ∀ n, source n = UART.expected t.tx byte n)
    (safe : Safe t b) (within : b.Contains age) :
    ∃ detected, firstEdge t b.earliest ≤ detected ∧ detected ≤ firstEdge t b.latest ∧
      Rx.result (Rx.run t.rx Rx.initial (observe t source age) (completion t detected)) =
        some (.byte byte) := by
  obtain ⟨d, lo, hi, later, high, low⟩ := start_detection t b source byte age wave safe within
  exact ⟨d, lo, hi, Rx.armed_frame_correct t.rx _ d byte later high low
    (sampling_contract t b source byte age d wave safe within lo hi).1
    (sampling_contract t b source byte age d wave safe within lo hi).2⟩
  done

/-- The executable transmitter discharges the abstract waveform premise. -/
theorem transmitter_correct (t : Timing) (b : Latency) (byte : BitVec 8) (age : Nat → Nat)
    (safe : Safe t b) (within : b.Contains age) :
    ∃ detected, firstEdge t b.earliest ≤ detected ∧ detected ≤ firstEdge t b.latest ∧
      Rx.result (Rx.run t.rx Rx.initial (sampled t byte age) (completion t detected)) =
        some (.byte byte) :=
  receive_correct t b (transmitter t.tx byte) byte age (UART.waveform_correct t.tx byte) safe within

/-- With a fixed delay, the detection interval collapses to one known RX edge. -/
theorem receive_fixed (t : Timing) (source : Nat → Bool) (byte : BitVec 8) (delay : Nat)
    (wave : ∀ n, source n = UART.expected t.tx byte n) (safe : Safe t (.fixed delay)) :
    Rx.result (Rx.run t.rx Rx.initial (observe t source (fun _ => delay))
      (completion t (firstEdge t delay))) = some (.byte byte) := by
  obtain ⟨d, lo, hi, result⟩ := receive_correct t (.fixed delay) source byte (fun _ => delay)
    wave safe (fun _ => ⟨Nat.le_refl _, Nat.le_refl _⟩)
  simpa only [show d = firstEdge t delay from Nat.le_antisymm hi lo] using result
  done

theorem ideal_safe (rx : Rx.Config) (fits : rx.bitCycles ≤ 256) (start : Nat) (armed : 2 ≤ start) :
    Safe (ideal rx fits start) (.fixed 0) := by
  have minimum := rx.minimum
  simp only [Safe, ideal, Timing.edge, Timing.center, Timing.txBit, Timing.rxBit,
    Latency.fixed, Latency.spread, UART.Config.cycles, Rx.Config.half, Nat.mul_one, Nat.zero_add,
    Nat.add_zero, Nat.sub_self]
  omega
  done

theorem ideal_firstEdge (rx : Rx.Config) (fits : rx.bitCycles ≤ 256) (start : Nat)
    (armed : 2 ≤ start) : firstEdge (ideal rx fits start) 0 = start := by
  simp only [firstEdge, ideal, Nat.add_zero, Nat.sub_zero, Nat.div_one]
  omega
  done

/-- Ideal TX-to-RX roundtrip for every byte and every shared bit period (8 through 256). -/
theorem ideal_receive (rx : Rx.Config) (fits : rx.bitCycles ≤ 256) (start : Nat)
    (armed : 2 ≤ start) (byte : BitVec 8) :
    Rx.result (Rx.run rx Rx.initial (sampled (ideal rx fits start) byte (fun _ => 0))
      (start + (rx.half + 9 * rx.bitCycles))) = some (.byte byte) := by
  simpa only [ideal_firstEdge rx fits start armed, completion, sampled,
    show (ideal rx fits start).rx = rx from rfl] using
    receive_fixed (ideal rx fits start) (transmitter (ideal rx fits start).tx byte) byte 0
      (UART.waveform_correct _ byte) (ideal_safe rx fits start armed)
  done

end Pinwheel.UART.Link
