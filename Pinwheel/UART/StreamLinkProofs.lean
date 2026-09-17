import Pinwheel.UART.StreamLinkWire

namespace Pinwheel.UART.StreamLink
open Link

theorem head_frame (t : Timing) (b : Latency) (byte : BitVec 8) (rest : List (BitVec 8))
    (age : Nat → Nat) (incoming : Nat → Rx.Stream.Input)
    (safe : Safe t b) (within : b.Contains age)
    (line : ∀ n, (incoming n).line = sampled t (byte :: rest) age n)
    (quiet : ∀ n, (incoming n).reset = false) :
    ∃ d, firstEdge t b.earliest ≤ d ∧ d ≤ firstEdge t b.latest ∧
      Rx.Stream.Frame t.rx incoming d byte := by
  obtain ⟨d, lo, hi, later, high, low⟩ := Link.start_detection t b (UART.expected t.tx byte)
    byte age (fun _ => rfl) safe.1 within
  have agrees (n : Nat) (before : n ≤ completion t d + 2) :
      (incoming n).line = observe t (UART.expected t.tx byte) age n :=
    (line n).trans (head_prefix t b byte rest age within n
      (Nat.lt_of_le_of_lt (edge_monotone t n _ before) (rearm_before_next t b d safe lo hi)))
  have observations (symbol : Fin 10) :
      (incoming (Rx.sampleTime t.rx d symbol)).line = (UART.frame byte).getD symbol.val true :=
    (agrees _ (Nat.le_trans (sample_before_completion t d symbol) (Nat.le_add_right _ 2))).trans
      (observe_symbol t (UART.expected t.tx byte) byte age _ symbol (fun _ => rfl)
        (observation_window t b safe.1 age within d lo hi symbol))
  refine ⟨d, lo, hi, later,
    (fun n hn hd => (agrees n (by unfold completion; omega)).trans (high n hn hd)),
    (agrees d (by unfold completion; omega)).trans low, ?_,
    ⟨(fun bit => (observations ⟨bit.val + 1, by omega⟩).trans (frame_data byte bit)), ?_⟩,
    (fun n _ _ => quiet n)⟩
  case refine_2 => simpa [UART.frame, Array.getD, show (9 : Fin 10).val = 9 from rfl] using observations 9
  case refine_1 => simpa [Rx.sampleTime, UART.frame, Array.getD] using observations 0

theorem next_safe (t : Timing) (b : Latency) (d : Nat) (safe : Safe t b)
    (lo : firstEdge t b.earliest ≤ d) (hi : d ≤ firstEdge t b.latest) :
    Safe (next t (completion t d + 1)) b := by
  have ready := rearm_before_next t b d safe lo hi
  refine ⟨⟨?_, safe.1.2⟩, safe.2⟩
  rw [next_edge]
  exact ready

theorem tail_sampled (t : Timing) (b : Latency) (byte : BitVec 8) (rest : List (BitVec 8))
    (age : Nat → Nat) (safe : Safe t b) (within : b.Contains age) (d : Nat)
    (lo : firstEdge t b.earliest ≤ d) (hi : d ≤ firstEdge t b.latest) (n : Nat) :
    sampled t (byte :: rest) age (completion t d + 1 + n) =
      sampled (next t (completion t d + 1)) rest (fun k => age (completion t d + 1 + k)) n := by
  rw [observed_suffix t byte rest age _
    (after_stop t b d _ safe lo hi age within (by omega))]
  simp [sampled, observe, next, Timing.edge, Nat.add_mul, Nat.add_assoc]

/-- Numerical bounds alone produce the valid finite frame sequence and its timing windows. -/
theorem stream_matches (t : Timing) (b : Latency) (bytes : List (BitVec 8))
    (age : Nat → Nat) (incoming : Nat → Rx.Stream.Input)
    (safe : Safe t b) (within : b.Contains age)
    (line : ∀ n, (incoming n).line = sampled t bytes age n)
    (quiet : ∀ n, (incoming n).reset = false) :
    ∃ frames, frames.map Rx.Stream.FrameSpec.byte = bytes ∧ Windows t b frames ∧
      Rx.Stream.Matches t.rx incoming frames := by
  induction bytes generalizing t age incoming with
  | nil => exact ⟨[], rfl, trivial, trivial⟩
  | cons byte rest ih =>
    obtain ⟨d, lo, hi, frame⟩ := head_frame t b byte rest age incoming safe within line quiet
    obtain ⟨frames, payloads, windows, valid⟩ := ih (next t (completion t d + 1))
      (fun k => age (completion t d + 1 + k)) (fun k => incoming (completion t d + 1 + k))
      (next_safe t b d safe lo hi) (fun k => within _)
      (fun k => (line _).trans (tail_sampled t b byte rest age safe within d lo hi k)) (fun k => quiet _)
    exact ⟨⟨d, byte⟩ :: frames, by simp [payloads], ⟨lo, hi, windows⟩, ⟨frame, valid⟩⟩

/-- Exact completion pulses and their detection windows, with consumer behavior unrestricted. -/
theorem receive_series (t : Timing) (b : Latency) (bytes : List (BitVec 8))
    (age : Nat → Nat) (incoming : Nat → Rx.Stream.Input) (buffer : Rx.Buffer.State)
    (safe : Safe t b) (within : b.Contains age)
    (line : ∀ n, (incoming n).line = sampled t bytes age n)
    (quiet : ∀ n, (incoming n).reset = false) :
    ∃ frames, frames.map Rx.Stream.FrameSpec.byte = bytes ∧ Windows t b frames ∧
      ∀ n, n ≤ Rx.Stream.horizon t.rx frames →
        Rx.Stream.arrival (Rx.Stream.run t.rx ⟨Rx.initial, buffer⟩ incoming n) =
          Rx.Stream.expected t.rx frames n := by
  obtain ⟨frames, payloads, windows, valid⟩ := stream_matches t b bytes age incoming safe within line quiet
  exact ⟨frames, payloads, windows, fun n hn => Rx.Stream.series_correct t.rx frames buffer incoming valid n hn⟩

/-- The stronger bound retains the entire ideal shared-period domain. -/
theorem ideal_safe (rx : Rx.Config) (fits : rx.bitCycles ≤ 256) (start : Nat) (armed : 2 ≤ start) :
    Safe (ideal rx fits start) (.fixed 0) := by
  refine ⟨Link.ideal_safe rx fits start armed, ?_⟩
  have minimum := rx.minimum
  simp only [ideal, Timing.center, Timing.rxBit, Timing.txBit, UART.Config.cycles, Rx.Config.half,
    Latency.fixed, Latency.spread, Nat.mul_one, Nat.sub_self, Nat.add_zero]
  omega

end Pinwheel.UART.StreamLink
