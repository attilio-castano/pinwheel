import Pinwheel.Hardware.Buffered.SerialCorrespondenceFrames

/-! Universal receipt serialization and retry retention for the sampled
frontend. The observed stream consists of actual MISO values on sampled rising
SCK edges. Low/high durations and unrelated raw/status samples are arbitrary. -/
namespace Pinwheel.Hardware.Buffered.Serial.Read
open Pinwheel.Hardware Serial.Frames

structure Reading (s : State) : Prop where
  active : s.active = true
  reading : s.reading = true
  dispatch : s.dispatch = false
  capture : s.capture = false
  ready : s.ready = true
  csnPrev : s.csnPrev = false

theorem Reading.update (h : Reading s) (prev : Bool) (count : BitVec 9) :
    Reading {s with sckPrev := prev, count} :=
  ⟨h.active, h.reading, h.dispatch, h.capture, h.ready, h.csnPrev⟩

theorem Reading.step_selected (h : Reading s) (i : Inputs)
    (cold : i.cold = false) (selected : i.csn = false) : Reading (s.step i) := by
  rcases h with ⟨active, reading, dispatch, capture, ready, csnPrev⟩
  constructor <;> simp [State.step, cold, selected, active, reading, dispatch, capture, ready, csnPrev]
  done

theorem start_read (s : State) (i : Inputs) (h : ReceiptReady s) (low : Low i) :
    Reading (s.step i) ∧ (s.step i).count = 0 ∧ (s.step i).response = s.response := by
  rcases h with ⟨active, dispatch, capture, ready, csnPrev⟩
  obtain ⟨cold, csn, sck⟩ := low
  constructor
  · constructor <;> simp [State.step, cold, csn, sck, active, dispatch, capture, ready, csnPrev]
  · simp [State.step, cold, csn, sck, active, dispatch, capture, ready, csnPrev]
  done

theorem step_low (s : State) (i : Inputs) (h : Reading s) (hi : Low i) :
    s.step i = {s with sckPrev := false} := by
  obtain ⟨cold, csn, sck⟩ := hi
  rcases h with ⟨active, reading, dispatch, capture, ready, csnPrev⟩
  simp [State.step, cold, csn, sck, active, reading, dispatch, capture, ready, csnPrev]
  done

theorem step_high (s : State) (i : Inputs) (h : Reading s) (hi : High i)
    (prev : s.sckPrev = true) : s.step i = s := by
  obtain ⟨cold, csn, sck⟩ := hi
  rcases h with ⟨active, reading, dispatch, capture, ready, csnPrev⟩
  simp [State.step, cold, csn, sck, active, reading, dispatch, capture, ready, csnPrev, prev]
  cases s
  simp_all
  done

theorem step_rise (s : State) (i : Inputs) (h : Reading s) (hi : High i)
    (prev : s.sckPrev = false) :
    s.step i = {s with sckPrev := true, count := countTick s.count} := by
  obtain ⟨cold, csn, sck⟩ := hi
  rcases h with ⟨active, reading, dispatch, capture, ready, csnPrev⟩
  simp [State.step, cold, csn, sck, active, reading, dispatch, capture, ready, csnPrev, prev, countTick]
  done

def rising (s : State) (i : Inputs) : Bool :=
  !i.cold && s.active && s.reading && !i.csn && i.sck && !s.sckPrev

def observed (s : State) : List Inputs → List Bool
  | [] => []
  | i :: rest => if rising s i then (s.miso i == 1) :: observed (s.step i) rest
    else observed (s.step i) rest

theorem observed_append (s : State) (a b : List Inputs) :
    observed s (a ++ b) = observed s a ++ observed (s.run a) b := by
  induction a generalizing s with
  | nil => rfl
  | cons i rest ih => simp only [observed, List.cons_append, ih, State.run, List.foldl_cons]; split <;> rfl
  done

theorem run_lows (s : State) (samples : List Inputs) (h : Reading s)
    (low : ∀ i ∈ samples, Low i) (nonempty : samples ≠ []) :
    s.run samples = {s with sckPrev := false} := by
  induction samples generalizing s with
  | nil => exact False.elim (nonempty rfl)
  | cons i rest ih =>
    have hi := low i (List.mem_cons_self ..)
    change (s.step i).run rest = _
    rw [step_low s i h hi]
    by_cases empty : rest = []
    · subst rest
      rfl
    · have ht := ih {s with sckPrev := false}
        (h.update false s.count) (fun j hj => low j (List.mem_cons_of_mem i hj)) empty
      simpa using ht
  done

theorem run_highs (s : State) (samples : List Inputs) (h : Reading s)
    (high : ∀ i ∈ samples, High i) (prev : s.sckPrev = true) : s.run samples = s := by
  induction samples generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have hi := high i (List.mem_cons_self ..)
    change (s.step i).run rest = _
    rw [step_high s i h hi prev]
    exact ih s h (fun j hj => high j (List.mem_cons_of_mem i hj)) prev
  done

theorem observed_lows (s : State) (samples : List Inputs) (h : Reading s)
    (low : ∀ i ∈ samples, Low i) : observed s samples = [] := by
  induction samples generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have hi := low i (List.mem_cons_self ..)
    simp only [observed]
    have silent : rising s i = false := by simp [rising, hi.2.2]
    rw [silent]
    exact ih (s.step i) (h.step_selected i hi.1 hi.2.1)
      (fun j hj => low j (List.mem_cons_of_mem i hj))
  done

theorem observed_highs (s : State) (samples : List Inputs) (h : Reading s)
    (high : ∀ i ∈ samples, High i) (prev : s.sckPrev = true) : observed s samples = [] := by
  induction samples generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have hi := high i (List.mem_cons_self ..)
    simp only [observed]
    have silent : rising s i = false := by simp [rising, prev]
    rw [silent]
    rw [step_high s i h hi prev]
    exact ih s h (fun j hj => high j (List.mem_cons_of_mem i hj)) prev
  done

def expectedBits (response : BitVec 192) (count : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => (if count < 192 then response.getLsbD (191-count) else false) ::
    expectedBits response (min 193 (count+1)) n

theorem run_bit (s : State) (samples : List Inputs) (h : Reading s)
    (bit : IsBit b samples) :
    s.run samples = {s with sckPrev := true, count := countTick s.count} := by
  obtain ⟨lows, first, highs, rfl, nonempty, low, high, _, held⟩ := bit.split
  rw [Serial.Frames.run_append, run_lows s lows h low nonempty]
  change (({s with sckPrev := false} : State).step first).run highs = _
  rw [step_rise _ first (h.update false s.count) high rfl]
  change ({s with sckPrev := true, count := countTick s.count} : State).run highs = _
  exact run_highs _ highs (h.update true (countTick s.count)) held rfl
  done

private theorem ofBool_one (bit : Bool) : (BitVec.ofBool bit == 1#1) = bit := by
  cases bit <;> rfl
  done

theorem miso_bit (s : State) (i : Inputs) (h : Reading s) (cold : i.cold = false) :
    (s.miso i == 1) = if s.count.toNat < 192 then s.response.getLsbD (191-s.count.toNat) else false := by
  by_cases inside : s.count.toNat < 192
  all_goals simp [State.miso, cold, h.active, h.reading, inside, ofBool_one]
  done

theorem observed_bit (s : State) (samples : List Inputs) (h : Reading s)
    (bit : IsBit b samples) :
    observed s samples =
      [if s.count.toNat < 192 then s.response.getLsbD (191-s.count.toNat) else false] := by
  obtain ⟨lows, first, highs, rfl, nonempty, low, high, _, held⟩ := bit.split
  rw [observed_append, observed_lows s lows h low, run_lows s lows h low nonempty]
  simp only [List.nil_append, observed]
  have edge : rising {s with sckPrev := false} first = true := by
    simp [rising, high.1, high.2.1, high.2.2, h.active, h.reading]
  rw [edge]
  rw [step_rise _ first (h.update false s.count) high rfl]
  simp only [ite_true]
  change (({s with sckPrev := false} : State).miso first == 1) ::
    observed ({s with sckPrev := true, count := countTick s.count} : State) highs = _
  rw [observed_highs _ highs (h.update true (countTick s.count)) held rfl]
  rw [miso_bit _ first (h.update false s.count) high.1]
  done

theorem run_bits (wire : IsBits bits samples) (s : State) (h : Reading s) :
    Reading (s.run samples) ∧
    (s.run samples).count = countRun s.count bits.length ∧
    (s.run samples).response = s.response := by
  induction wire generalizing s with
  | nil => exact ⟨h, rfl, rfl⟩
  | @cons bit part bits tail head rest ih =>
    rw [Serial.Frames.run_append, run_bit s part h head]
    exact ih _ (h.update true (countTick s.count))
  done

theorem observed_bits (wire : IsBits bits samples) (s : State) (h : Reading s)
    (bound : s.count.toNat ≤ 193) :
    observed s samples = expectedBits s.response s.count.toNat bits.length := by
  induction wire generalizing s with
  | nil => rfl
  | @cons bit part bits tail head rest ih =>
    have hc := countTick_toNat s.count bound
    have hb : (countTick s.count).toNat ≤ 193 := by rw [hc]; exact Nat.min_le_left ..
    rw [observed_append, observed_bit s part h head, run_bit s part h head]
    change _ :: observed ({s with sckPrev := true, count := countTick s.count} : State) tail =
      _ :: expectedBits s.response (min 193 (s.count.toNat+1)) bits.length
    rw [ih _ (h.update true (countTick s.count)) hb]
    simp only [hc]
  done

theorem fed_selected_quiet (s : State) (samples : List Inputs) (h : Reading s)
    (selected : ∀ i ∈ samples, i.cold = false ∧ i.csn = false) :
    ∀ input ∈ fed s samples, Quiet input := by
  induction samples generalizing s with
  | nil => simp [fed]
  | cons i rest ih =>
    obtain ⟨cold, csn⟩ := selected i (List.mem_cons_self ..)
    intro input member
    simp only [fed, List.mem_cons] at member
    rcases member with eq | member
    · subst input
      exact fed_quiet s i cold h.dispatch
    · exact ih (s.step i) (h.step_selected i cold csn)
        (fun j hj => selected j (List.mem_cons_of_mem i hj)) input member
  done

theorem expectedBits_bounded (response : BitVec 192) (count n : Nat) (bound : count+n ≤ 192) :
    expectedBits response count n =
      (List.range n).map (fun k => response.getLsbD (191-(count+k))) := by
  induction n generalizing count with
  | zero => rfl
  | succ n ih =>
    have before : count < 192 := by omega
    have next : count+1 ≤ 193 := by omega
    simp only [expectedBits, if_pos before, Nat.min_eq_right next]
    rw [ih (count+1) (by omega)]
    rw [List.range_succ_eq_map]
    simp [Nat.add_comm, Nat.add_left_comm]
  done

theorem close_exact (s : State) (i : Inputs) (h : Reading s) (idle : Idle i)
    (count : s.count = 192) : Available (s.step i) ∧ (s.step i).response = s.response := by
  obtain ⟨cold, csn⟩ := idle
  rcases h with ⟨active, reading, dispatch, capture, ready, csnPrev⟩
  constructor
  · constructor <;> simp [State.step, cold, csn, active, reading, dispatch, capture, ready, csnPrev]
    exact count
  · simp [State.step, cold, csn, active, reading, dispatch, capture, ready, csnPrev]
  done

theorem close_retry (s : State) (i : Inputs) (h : Reading s) (idle : Idle i)
    (count : s.count ≠ 192) : ReceiptReady (s.step i) ∧ (s.step i).response = s.response := by
  obtain ⟨cold, csn⟩ := idle
  rcases h with ⟨active, reading, dispatch, capture, ready, csnPrev⟩
  constructor
  · constructor <;> simp [State.step, cold, csn, active, reading, dispatch, capture, ready, csnPrev]
    exact count
  · simp [State.step, cold, csn, active, reading, dispatch, capture, ready, csnPrev]
  done

theorem transaction_state (s : State) (assert close : Inputs) (bits : List Bool)
    (samples : List Inputs) (ready : ReceiptReady s) (low : Low assert)
    (wire : IsBits bits samples) (idle : Idle close) :
    (s.run (assert :: (samples ++ [close]))).response = s.response ∧
    (if bits.length = 192 then Available (s.run (assert :: (samples ++ [close])))
      else ReceiptReady (s.run (assert :: (samples ++ [close])))) := by
  have start := start_read s assert ready low
  have read := run_bits wire (s.step assert) start.1
  have count : (((s.step assert).run samples).count).toNat = min 193 bits.length := by
    rw [read.2.1, countRun_toNat _ (by rw [start.2.1]; decide), start.2.1]
    simp
  have response : ((s.step assert).run samples).response = s.response := read.2.2.trans start.2.2
  change ((s.step assert).run (samples ++ [close])).response = s.response ∧
    (if bits.length = 192 then Available ((s.step assert).run (samples ++ [close]))
      else ReceiptReady ((s.step assert).run (samples ++ [close])))
  rw [Serial.Frames.run_append]
  change (((s.step assert).run samples).step close).response = s.response ∧
    (if bits.length = 192 then Available (((s.step assert).run samples).step close)
      else ReceiptReady (((s.step assert).run samples).step close))
  by_cases exact : bits.length = 192
  · have hc : ((s.step assert).run samples).count = 192 := by
      apply BitVec.eq_of_toNat_eq
      rw [count, exact]
      rfl
    have result := close_exact _ close read.1 idle hc
    exact ⟨result.2.trans response, by simpa [exact] using result.1⟩
  · have hc : ((s.step assert).run samples).count ≠ 192 := by
      intro eq
      have hh := congrArg BitVec.toNat eq
      rw [count] at hh
      change min 193 bits.length = 192 at hh
      omega
    have result := close_retry _ close read.1 idle hc
    exact ⟨result.2.trans response, by simpa [exact] using result.1⟩
  done

theorem transaction_observed (s : State) (assert close : Inputs) (bits : List Bool)
    (samples : List Inputs) (ready : ReceiptReady s) (low : Low assert)
    (wire : IsBits bits samples) (idle : Idle close) :
    observed s (assert :: (samples ++ [close])) = expectedBits s.response 0 bits.length := by
  have start := start_read s assert ready low
  have first : rising s assert = false := by simp [rising, ready.active]
  simp only [observed, first, Bool.false_eq_true, ↓reduceIte]
  rw [observed_append]
  have last : rising ((s.step assert).run samples) close = false := by simp [rising, idle.2]
  simp only [observed, last, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  rw [observed_bits wire _ start.1 (by rw [start.2.1]; decide), start.2.1, start.2.2]
  rfl
  done

theorem transaction_quiet (s : State) (assert close : Inputs) (bits : List Bool)
    (samples : List Inputs) (ready : ReceiptReady s) (low : Low assert)
    (wire : IsBits bits samples) (idle : Idle close) :
    ∀ input ∈ fed s (assert :: (samples ++ [close])), Quiet input := by
  have start := start_read s assert ready low
  have read := run_bits wire (s.step assert) start.1
  have during := fed_selected_quiet (s.step assert) samples start.1 wire.selected
  intro input member
  simp only [fed, List.mem_cons] at member
  rcases member with eq | member
  · subst input
    exact fed_quiet s assert low.1 ready.dispatch
  · rw [fed_append] at member
    rcases List.mem_append.mp member with member | member
    · exact during input member
    · simp only [fed, List.mem_cons, List.not_mem_nil, or_false] at member
      subst input
      exact fed_quiet _ close idle.1 read.1.dispatch
  done

/-- An exact 192-bit read returns the held response MSB first and releases only
the frontend receipt. Every engine edge is quiet, including assertion/closure. -/
theorem exact_read (s : State) (assert close : Inputs) (bits : List Bool)
    (samples : List Inputs) (ready : ReceiptReady s) (low : Low assert)
    (wire : IsBits bits samples) (idle : Idle close) (length : bits.length = 192) :
    Available (s.run (assert :: (samples ++ [close]))) ∧
    (s.run (assert :: (samples ++ [close]))).response = s.response ∧
    observed s (assert :: (samples ++ [close])) =
      (List.range 192).map (fun k => s.response.getLsbD (191-k)) := by
  have result := transaction_state s assert close bits samples ready low wire idle
  refine ⟨by simpa [length] using result.2, result.1, ?_⟩
  rw [transaction_observed s assert close bits samples ready low wire idle, length,
    expectedBits_bounded s.response 0 192 (by decide)]
  rfl
  done

/-- All other read lengths retain the identical response for another read. -/
theorem retry_read (s : State) (assert close : Inputs) (bits : List Bool)
    (samples : List Inputs) (ready : ReceiptReady s) (low : Low assert)
    (wire : IsBits bits samples) (idle : Idle close) (length : bits.length ≠ 192) :
    ReceiptReady (s.run (assert :: (samples ++ [close]))) ∧
    (s.run (assert :: (samples ++ [close]))).response = s.response := by
  have result := transaction_state s assert close bits samples ready low wire idle
  exact ⟨by simpa [length] using result.2, result.1⟩
  done

end Pinwheel.Hardware.Buffered.Serial.Read
