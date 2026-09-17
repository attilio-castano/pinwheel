import Pinwheel.UART.RxStream
import Pinwheel.UART.RxProgress
import Pinwheel.UART.RxBufferProofs
import Pinwheel.UART.LinkProofs

namespace Pinwheel.UART.Rx.Stream

theorem receiver_step (cfg : Config) (s : State) (input : Input) :
    (step cfg s input).state.receiver = Rx.step cfg s.receiver input.reset true input.line := rfl

/-- Consumer controls and buffer occupancy cannot alter the receive machine's timing. -/
theorem receiver_independent (cfg : Config) (a b : State) (same : a.receiver = b.receiver)
    (left right : Nat → Input) (line : ∀ n, (left n).line = (right n).line)
    (reset : ∀ n, (left n).reset = (right n).reset) (n : Nat) :
    (run cfg a left n).receiver = (run cfg b right n).receiver := by
  induction n with
  | zero => exact same
  | succ n ih => simp only [run, receiver_step, ih, line, reset]

theorem receiver_run (cfg : Config) (s : State) (incoming : Nat → Input) (n : Nat)
    (active : ∀ k, k < n → Rx.busy (Rx.run cfg s.receiver (fun j => (incoming j).line) k) = true)
    (quiet : ∀ k, 1 ≤ k → k ≤ n → (incoming k).reset = false) :
    (run cfg s incoming n).receiver = Rx.run cfg s.receiver (fun j => (incoming j).line) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, receiver_step, Rx.run,
      ih (fun k hk => active k (by omega)) (fun k hk hb => quiet k hk (by omega)),
      Rx.step, quiet (n + 1) (by omega) (by omega), active n (by omega),
      Bool.false_eq_true, ↓reduceIte]

theorem receiver_frame (cfg : Config) (buffer : Buffer.State) (incoming : Nat → Input)
    (detected n : Nat) (byte : BitVec 8) (frame : Frame cfg incoming detected byte)
    (before : n ≤ completion cfg detected) :
    (run cfg ⟨Rx.initial, buffer⟩ incoming n).receiver =
      Rx.run cfg Rx.initial (fun k => (incoming k).line) n := by
  exact receiver_run cfg _ incoming n
    (fun k hk => Rx.armed_busy_before cfg _ detected k frame.later frame.high frame.low
      (by unfold completion at before; omega))
    (fun k hk hb => frame.quiet k hk (by omega))

theorem frame_complete (cfg : Config) (buffer : Buffer.State) (incoming : Nat → Input)
    (detected : Nat) (byte : BitVec 8) (frame : Frame cfg incoming detected byte) :
    arrival (run cfg ⟨Rx.initial, buffer⟩ incoming (completion cfg detected)) = some (.byte byte) := by
  rw [arrival, receiver_frame cfg buffer incoming detected _ byte frame (Nat.le_refl _)]
  exact Rx.armed_frame_correct cfg _ detected byte frame.later frame.high frame.low frame.startLow frame.samples

theorem frame_silent (cfg : Config) (buffer : Buffer.State) (incoming : Nat → Input)
    (detected n : Nat) (byte : BitVec 8) (frame : Frame cfg incoming detected byte)
    (before : n < completion cfg detected) :
    arrival (run cfg ⟨Rx.initial, buffer⟩ incoming n) = none := by
  rw [arrival, receiver_frame cfg buffer incoming detected n byte frame (Nat.le_of_lt before)]
  exact Rx.result_none_of_busy _ (Rx.armed_busy_before cfg _ detected n frame.later frame.high frame.low before)

theorem after_arrival (cfg : Config) (s : State) (input : Input) (value : Outcome)
    (arrived : arrival s = some value) :
    (step cfg s input).state.receiver = if input.reset then Rx.reset else Rx.initial := by
  change Rx.step cfg s.receiver input.reset true input.line = _
  cases h : s.receiver.phase <;> simp_all [arrival, Rx.result, Rx.step, Rx.busy]

theorem no_repeated_arrival (cfg : Config) (s : State) (input : Input) (value : Outcome)
    (arrived : arrival s = some value) : arrival (step cfg s input).state = none := by
  simp [arrival, after_arrival cfg s input value arrived, Rx.result, Rx.reset, Rx.initial]
  split <;> decide

theorem frame_rearm (cfg : Config) (buffer : Buffer.State) (incoming : Nat → Input)
    (detected : Nat) (byte : BitVec 8) (frame : Frame cfg incoming detected byte) :
    (run cfg ⟨Rx.initial, buffer⟩ incoming (completion cfg detected + 1)).receiver = Rx.initial := by
  rw [run, after_arrival cfg _ _ (.byte byte) (frame_complete cfg buffer incoming detected byte frame),
    frame.quiet _ (by omega) (Nat.le_refl _)]
  rfl

theorem wellFormed_step (cfg : Config) (s : State) (input : Input)
    (valid : Rx.WellFormed cfg s.receiver) : Rx.WellFormed cfg (step cfg s input).state.receiver := by
  simp only [receiver_step]
  grind [Rx.step, Rx.wellFormed_advance, Rx.WellFormed, Rx.reset, Rx.initial]

theorem wellFormed_run (cfg : Config) (s : State) (incoming : Nat → Input)
    (valid : Rx.WellFormed cfg s.receiver) (n : Nat) :
    Rx.WellFormed cfg (run cfg s incoming n).receiver :=
  Nat.recOn n valid (fun n ih => wellFormed_step cfg _ (incoming (n + 1)) ih)

theorem run_add (cfg : Config) (s : State) (incoming : Nat → Input) (a b : Nat) :
    run cfg s incoming (a + b) = run cfg (run cfg s incoming a) (fun k => incoming (a + k)) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [Nat.add_succ, run, run, ← ih]
    simp only [Nat.add_assoc]

theorem buffer_trace (cfg : Config) (s : State) (incoming : Nat → Input) (n : Nat) :
    (Buffer.run s.buffer (commands cfg s incoming n)).state = (run cfg s incoming n).buffer := by
  induction n with
  | zero => rfl
  | succ n ih => rw [commands, Buffer.run_append_state, ih]
                 rfl

/-- Numerical one-frame link bounds discharge the wire premise of one stream segment.
Repeating segments still requires the arming interval in `Matches`. -/
theorem link_frame (t : UART.Link.Timing) (b : UART.Link.Latency) (source : Nat → Bool)
    (byte : BitVec 8) (age : Nat → Nat) (incoming : Nat → Input)
    (wave : ∀ n, source n = UART.expected t.tx byte n)
    (line : ∀ n, (incoming n).line = UART.Link.observe t source age n)
    (quiet : ∀ n, (incoming n).reset = false)
    (safe : UART.Link.Safe t b) (within : b.Contains age) :
    ∃ detected, UART.Link.firstEdge t b.earliest ≤ detected ∧
      detected ≤ UART.Link.firstEdge t b.latest ∧ Frame t.rx incoming detected byte := by
  obtain ⟨d, lo, hi, later, high, low⟩ := UART.Link.start_detection t b source byte age wave safe within
  have samples := UART.Link.sampling_contract t b source byte age d wave safe within lo hi
  exact ⟨d, lo, hi, later, (fun k hk hd => (line k).trans (high k hk hd)),
    (line d).trans low, (line _).trans samples.1,
    by simpa only [line] using samples.2, (fun k _ _ => quiet k)⟩

end Pinwheel.UART.Rx.Stream
