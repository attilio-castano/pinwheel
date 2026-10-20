import Pinwheel.Hardware.Buffered.SerialCorrespondence

/-! Delivery derived from sampled 160-bit frontend traffic. Clock-low/high
blocks may have arbitrary positive durations; raw protocol inputs and status
may change on every sample. MOSI is constrained only on each first high edge.
No delivered command trace is a premise. -/
namespace Pinwheel.Hardware.Buffered.Serial.Frames
open Pinwheel.Hardware

def Low (i : Inputs) : Prop := i.cold = false ∧ i.csn = false ∧ i.sck = false
def High (i : Inputs) : Prop := i.cold = false ∧ i.csn = false ∧ i.sck = true
def Idle (i : Inputs) : Prop := i.cold = false ∧ i.csn = true

structure Receiving (s : State) : Prop where
  active : s.active = true
  reading : s.reading = false
  dispatch : s.dispatch = false
  capture : s.capture = false
  ready : s.ready = false
  csnPrev : s.csnPrev = false

def Quiet (input : Values Reactive.Input) : Prop := input .initialize = 0 ∧ input .command = 0

def fed (s : State) : List Inputs → List (Values Reactive.Input)
  | [] => []
  | i :: rest => (fun {w} (p : Reactive.Input w) => s.coreInput i p) :: fed (s.step i) rest

theorem run_append (s : State) (a b : List Inputs) :
    s.run (a ++ b) = (s.run a).run b := List.foldl_append

theorem fed_append (s : State) (a b : List Inputs) :
    fed s (a ++ b) = fed s a ++ fed (s.run a) b := by
  induction a generalizing s with
  | nil => rfl
  | cons i rest ih => simp only [fed, State.run, List.foldl_cons, List.cons_append, ih]
  done

theorem fed_quiet (s : State) (i : Inputs) (cold : i.cold = false)
    (dispatch : s.dispatch = false) : Quiet (s.coreInput i) := by
  simp [Quiet, State.coreInput, deliver, cold, dispatch]
  done

theorem step_low (s : State) (i : Inputs) (h : Receiving s) (hi : Low i) :
    s.step i = {s with sckPrev := false} := by
  obtain ⟨cold, csn, sck⟩ := hi
  rcases h with ⟨active, reading, dispatch, capture, ready, csnPrev⟩
  simp [State.step, cold, csn, sck, active, reading, dispatch, capture, ready, csnPrev]
  done

theorem step_high (s : State) (i : Inputs) (h : Receiving s) (hi : High i)
    (prev : s.sckPrev = true) : s.step i = s := by
  obtain ⟨cold, csn, sck⟩ := hi
  rcases h with ⟨active, reading, dispatch, capture, ready, csnPrev⟩
  simp [State.step, cold, csn, sck, active, reading, dispatch, capture, ready, csnPrev, prev]
  cases s
  simp_all
  done

theorem step_rise (s : State) (i : Inputs) (h : Receiving s) (hi : High i)
    (prev : s.sckPrev = false) :
    s.step i = {s with
      sckPrev := true
      count := if s.count.toNat < 193 then s.count + 1 else s.count
      request := BitVec.ofNat 160 (2*s.request.toNat + i.mosi.toNat)} := by
  obtain ⟨cold, csn, sck⟩ := hi
  rcases h with ⟨active, reading, dispatch, capture, ready, csnPrev⟩
  simp [State.step, cold, csn, sck, active, reading, dispatch, capture, ready, csnPrev, prev]
  done

theorem Receiving.update (h : Receiving s) (prev : Bool) (count : BitVec 9)
    (request : BitVec 160) : Receiving {s with sckPrev := prev, count, request} :=
  ⟨h.active, h.reading, h.dispatch, h.capture, h.ready, h.csnPrev⟩

theorem Receiving.step_selected (h : Receiving s) (i : Inputs)
    (cold : i.cold = false) (selected : i.csn = false) : Receiving (s.step i) := by
  rcases h with ⟨active, reading, dispatch, capture, ready, csnPrev⟩
  constructor <;> simp [State.step, cold, selected, active, reading, dispatch, capture, ready, csnPrev]
  done

theorem fed_selected_quiet (s : State) (samples : List Inputs) (h : Receiving s)
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

theorem run_lows (s : State) (samples : List Inputs) (h : Receiving s)
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
        (h.update false s.count s.request) (fun j hj => low j (List.mem_cons_of_mem i hj)) empty
      simpa using ht
  done

theorem run_highs (s : State) (samples : List Inputs) (h : Receiving s)
    (high : ∀ i ∈ samples, High i) (prev : s.sckPrev = true) : s.run samples = s := by
  induction samples generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have hi := high i (List.mem_cons_self ..)
    change (s.step i).run rest = _
    rw [step_high s i h hi prev]
    exact ih s h (fun j hj => high j (List.mem_cons_of_mem i hj)) prev
  done

structure IsBit (bit : Bool) (samples : List Inputs) : Prop where
  split : ∃ lows first highs, samples = lows ++ first :: highs ∧ lows ≠ [] ∧
    (∀ i ∈ lows, Low i) ∧ High first ∧ first.mosi = bit ∧ (∀ i ∈ highs, High i)

theorem IsBit.selected (h : IsBit b samples) :
    ∀ i ∈ samples, i.cold = false ∧ i.csn = false := by
  obtain ⟨lows, first, highs, rfl, _, low, high, _, held⟩ := h.split
  intro i member
  simp only [List.mem_append, List.mem_cons] at member
  rcases member with member | eq | member
  · exact ⟨(low i member).1, (low i member).2.1⟩
  · subst i
    exact ⟨high.1, high.2.1⟩
  · exact ⟨(held i member).1, (held i member).2.1⟩
  done

def countTick (count : BitVec 9) : BitVec 9 :=
  if count.toNat < 193 then count + 1 else count

def shiftIn (word : BitVec 160) (bit : Bool) : BitVec 160 :=
  BitVec.ofNat 160 (2*word.toNat + bit.toNat)

theorem run_bit (s : State) (samples : List Inputs) (h : Receiving s)
    (bit : IsBit b samples) :
    s.run samples = {s with
      sckPrev := true
      count := countTick s.count
      request := shiftIn s.request b} := by
  obtain ⟨lows, first, highs, rfl, nonempty, low, high, mosi, held⟩ := bit.split
  rw [run_append, run_lows s lows h low nonempty]
  change (({s with sckPrev := false} : State).step first).run highs = _
  rw [step_rise _ first (h.update false s.count s.request) high rfl]
  change ({s with
    sckPrev := true
    count := countTick s.count
    request := shiftIn s.request first.mosi} : State).run highs = _
  rw [run_highs _ highs (h.update true (countTick s.count) (shiftIn s.request first.mosi)) held rfl]
  simp [countTick, shiftIn, mosi]
  done

inductive IsBits : List Bool → List Inputs → Prop where
  | nil : IsBits [] []
  | cons (bit : IsBit b samples) (rest : IsBits bits tail) :
      IsBits (b :: bits) (samples ++ tail)

theorem IsBits.selected (h : IsBits bits samples) :
    ∀ i ∈ samples, i.cold = false ∧ i.csn = false := by
  induction h with
  | nil => simp
  | cons bit rest ih =>
    intro i member
    rcases List.mem_append.mp member with member | member
    · exact bit.selected i member
    · exact ih i member
  done

def countRun (count : BitVec 9) : Nat → BitVec 9
  | 0 => count
  | n + 1 => countRun (countTick count) n

def shiftBits (word : BitVec 160) : List Bool → BitVec 160
  | [] => word
  | bit :: rest => shiftBits (shiftIn word bit) rest

theorem run_bits (h : IsBits bits samples) (s : State) (hr : Receiving s) :
    Receiving (s.run samples) ∧
    (s.run samples).count = countRun s.count bits.length ∧
    (s.run samples).request = shiftBits s.request bits := by
  induction h generalizing s with
  | nil => exact ⟨hr, rfl, rfl⟩
  | @cons bit part bits tail head rest ih =>
    rw [run_append, run_bit s part hr head]
    exact ih _ (hr.update true (countTick s.count) (shiftIn s.request bit))
  done

theorem countTick_toNat (count : BitVec 9) (bound : count.toNat ≤ 193) :
    (countTick count).toNat = min 193 (count.toNat + 1) := by
  simp only [countTick]
  split
  · change (count.toNat + 1) % 512 = min 193 (count.toNat + 1)
    omega
  · omega
  done

theorem countRun_toNat (count : BitVec 9) (bound : count.toNat ≤ 193) (n : Nat) :
    (countRun count n).toNat = min 193 (count.toNat + n) := by
  induction n generalizing count with
  | zero => simp [countRun, Nat.min_eq_right bound]
  | succ n ih =>
    have hc := countTick_toNat count bound
    have hb : (countTick count).toNat ≤ 193 := by rw [hc]; exact Nat.min_le_left ..
    rw [countRun, ih _ hb, hc]
    omega
  done

theorem shiftIn_getLsbD (word : BitVec 160) (bit : Bool) (i : Nat) :
    (shiftIn word bit).getLsbD i =
      if i = 0 then bit else (decide (i < 160) && word.getLsbD (i-1)) := by
  unfold shiftIn
  rw [← Serial.request_shift]
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool]
  by_cases zero : i = 0
  · subst i
    simp
  · have one : ¬i < 1 := by omega
    have bound : (i-1 < 159) ↔ i < 160 := by omega
    simp [zero, one, bound]
  done

theorem shiftBits_append (word : BitVec 160) (a b : List Bool) :
    shiftBits word (a ++ b) = shiftBits (shiftBits word a) b := by
  induction a generalizing word with
  | nil => rfl
  | cons bit rest ih => exact ih (shiftIn word bit)
  done

private theorem reverse_induction {p : List α → Prop} (nil : p [])
    (snoc : ∀ xs x, p xs → p (xs ++ [x])) (xs : List α) : p xs := by
  have backwards (ys : List α) : p ys.reverse := by
    induction ys with
    | nil => exact nil
    | cons y ys ih => simpa using snoc ys.reverse y ih
  simpa using backwards xs.reverse
  done

theorem shiftBits_getLsbD (word : BitVec 160) (bits : List Bool) (i : Nat)
    (inside : i < bits.length) (width : i < 160) :
    (shiftBits word bits).getLsbD i = bits.getD (bits.length-1-i) false := by
  induction bits using reverse_induction generalizing i with
  | nil => simp at inside
  | snoc bits bit ih =>
    rw [shiftBits_append]
    change (shiftIn (shiftBits word bits) bit).getLsbD i = _
    rw [shiftIn_getLsbD]
    by_cases zero : i = 0
    · subst i
      simp
    · have less : i-1 < bits.length := by simp only [List.length_append, List.length_singleton] at inside; omega
      rw [if_neg zero, ih (i-1) less (by omega)]
      simp [width]
      have eq : bits.length - 1 - (i-1) = bits.length - i := by omega
      have bound : bits.length - i < bits.length := by omega
      simp [eq, List.getElem?_append, bound]
    done
  done

def wordBits (word : BitVec 160) : List Bool :=
  (List.range 160).map (fun k => word.getLsbD (159-k))

theorem wordBits_length (word : BitVec 160) : (wordBits word).length = 160 := by
  simp [wordBits]
  done

theorem shiftBits_wordBits (initial word : BitVec 160) :
    shiftBits initial (wordBits word) = word := by
  apply BitVec.eq_of_getLsbD_eq
  intro i bound
  rw [shiftBits_getLsbD initial (wordBits word) i (by simpa [wordBits] using bound) bound]
  have index : 159-i < 160 := by omega
  have reflected : 159-(159-i) = i := by omega
  simp [wordBits, List.getD_eq_getElem?_getD, index, reflected]
  done

structure Available (s : State) : Prop where
  active : s.active = false
  dispatch : s.dispatch = false
  capture : s.capture = false
  ready : s.ready = false
  csnPrev : s.csnPrev = true

theorem assert_receiving (s : State) (i : Inputs) (h : Available s) (low : Low i) :
    Receiving (s.step i) ∧ (s.step i).count = 0 ∧ (s.step i).request = 0 := by
  rcases h with ⟨active, dispatch, capture, ready, csnPrev⟩
  obtain ⟨cold, csn, sck⟩ := low
  constructor
  · constructor <;> simp [State.step, cold, csn, sck, active, dispatch, capture, ready, csnPrev]
  · simp [State.step, cold, csn, sck, active, dispatch, capture, ready, csnPrev]
  done

def codeOf (word : BitVec 160) : BitVec 4 := requestCode {count := 160, request := word}

structure Closed (word : BitVec 160) (s : State) : Prop where
  active : s.active = false
  dispatch : s.dispatch = true
  capture : s.capture = false
  ready : s.ready = false
  csnPrev : s.csnPrev = true
  request : s.request = word
  count : s.count = 160
  code : s.code = codeOf word
  sequence : s.sequence = word.extractLsb' 128 16

theorem close_request (s : State) (i : Inputs) (h : Receiving s) (idle : Idle i)
    (count : s.count = 160) (word : s.request = request) : Closed request (s.step i) := by
  rcases h with ⟨active, reading, dispatch, capture, ready, csnPrev⟩
  obtain ⟨cold, csn⟩ := idle
  constructor <;> simp [State.step, cold, csn, active, reading, dispatch, capture,
    ready, csnPrev, count, word, codeOf, requestCode, requestOpcode, requestField_eq]
  done

/-- Every sampled bit is used; initialization, delivery, image validity and
source execution are not premises of this framing theorem. -/
theorem frame_closed (s : State) (word : BitVec 160) (assert close : Inputs)
    (samples : List Inputs) (available : Available s) (low : Low assert)
    (bits : IsBits (wordBits word) samples) (idle : Idle close) :
    Closed word (s.run (assert :: (samples ++ [close]))) := by
  have start := assert_receiving s assert available low
  have uploaded := run_bits bits (s.step assert) start.1
  have count : ((s.step assert).run samples).count = 160 := by
    apply BitVec.eq_of_toNat_eq
    rw [uploaded.2.1, countRun_toNat _ (by rw [start.2.1]; decide), start.2.1, wordBits_length]
    rfl
  have request : ((s.step assert).run samples).request = word := by
    rw [uploaded.2.2, shiftBits_wordBits]
  change Closed word ((s.step assert).run (samples ++ [close]))
  rw [run_append]
  exact close_request _ close uploaded.1 idle count request
  done

theorem frame_quiet (s : State) (word : BitVec 160) (assert close : Inputs)
    (samples : List Inputs) (available : Available s) (low : Low assert)
    (bits : IsBits (wordBits word) samples) (idle : Idle close) :
    ∀ input ∈ fed s (assert :: (samples ++ [close])), Quiet input := by
  have start := assert_receiving s assert available low
  have uploaded := run_bits bits (s.step assert) start.1
  have during := fed_selected_quiet (s.step assert) samples start.1 bits.selected
  intro input member
  simp only [fed, List.mem_cons] at member
  rcases member with eq | member
  · subst input
    exact fed_quiet s assert low.1 available.dispatch
  · rw [fed_append] at member
    rcases List.mem_append.mp member with member | member
    · exact during input member
    · simp only [fed, List.mem_cons, List.not_mem_nil, or_false] at member
      subst input
      exact fed_quiet _ close idle.1 uploaded.1.dispatch
  done

theorem frame_bad_length (s : State) (assert close : Inputs) (bits : List Bool)
    (samples : List Inputs) (available : Available s) (low : Low assert)
    (wire : IsBits bits samples) (idle : Idle close) (length : bits.length ≠ 160) :
    (s.run (assert :: (samples ++ [close]))).code = 1 := by
  have start := assert_receiving s assert available low
  have uploaded := run_bits wire (s.step assert) start.1
  have count : (((s.step assert).run samples).count).toNat = min 193 bits.length := by
    rw [uploaded.2.1, countRun_toNat _ (by rw [start.2.1]; decide), start.2.1]
    simp
  have wrong : (((s.step assert).run samples).count).toNat ≠ 160 := by rw [count]; omega
  change (((s.step assert).run (samples ++ [close])).code) = _
  rw [run_append]
  change (((s.step assert).run samples).step close).code = _
  generalize hs : (s.step assert).run samples = after at *
  obtain ⟨active, reading, dispatch, capture, ready, csnPrev⟩ := uploaded.1
  obtain ⟨cold, csn⟩ := idle
  simp [State.step, cold, csn, active, reading, dispatch, capture, ready, csnPrev,
    requestCode, wrong]
  done

theorem Closed.delivers (h : Closed word s) (i : Inputs) (cold : i.cold = false) :
    deliver i s = (codeOf word == 0) := by
  simp [deliver, cold, h.dispatch, h.code]
  done

theorem Closed.coreInputs (h : Closed word s) (i : Inputs) :
    @State.coreInput s i = @State.coreInput
      {count := 160, request := word, dispatch := true, code := codeOf word} i := by
  funext w p
  cases p <;> simp [State.coreInput, deliver, h.request, h.dispatch, h.code,
    requestOpcode, requestField]
  done

structure Capturing (word : BitVec 160) (rejection : Bool) (s : State) : Prop where
  active : s.active = false
  dispatch : s.dispatch = false
  capture : s.capture = true
  ready : s.ready = false
  csnPrev : s.csnPrev = true
  request : s.request = word
  code : s.code = codeOf word
  sequence : s.sequence = word.extractLsb' 128 16
  rejected : s.rejected = rejection

theorem Closed.step_dispatch (h : Closed word s) (i : Inputs) (idle : Idle i) :
    Capturing word ((codeOf word == 0) && (i.status .rejected == 1)) (s.step i) := by
  obtain ⟨cold, csn⟩ := idle
  rcases h with ⟨active, dispatch, capture, ready, csnPrev, request, count, code, sequence⟩
  constructor <;> simp [State.step, deliver, cold, csn, active, dispatch, capture,
    ready, csnPrev, request, count, code, sequence]
  done

structure ReceiptReady (s : State) : Prop where
  active : s.active = false
  dispatch : s.dispatch = false
  capture : s.capture = false
  ready : s.ready = true
  csnPrev : s.csnPrev = true

theorem Capturing.step_capture (h : Capturing word rejection s) (i : Inputs) (idle : Idle i) :
    ReceiptReady (s.step i) ∧ (s.step i).response = s.capturedResponse i := by
  obtain ⟨cold, csn⟩ := idle
  rcases h with ⟨active, dispatch, capture, ready, csnPrev, request, code, sequence, rejected⟩
  constructor
  · constructor <;> simp [State.step, cold, csn, active, dispatch, capture, ready, csnPrev]
  · simp [State.step, cold, csn, active, dispatch, capture, ready, csnPrev]
  done

/-- Closure itself is quiet, the next idle edge delivers at most one decoded
command, and the following idle edge freezes its complete receipt. -/
theorem closed_pipeline (h : Closed word s) (dispatch capture : Inputs)
    (first : Idle dispatch) (second : Idle capture) :
    deliver dispatch s = (codeOf word == 0) ∧
    Quiet ((s.step dispatch).coreInput capture) ∧
    ReceiptReady ((s.step dispatch).step capture) ∧
    ((s.step dispatch).step capture).response = (s.step dispatch).capturedResponse capture := by
  have pending := h.step_dispatch dispatch first
  have result := pending.step_capture capture second
  exact ⟨h.delivers dispatch first.1,
    fed_quiet _ capture second.1 pending.dispatch, result.1, result.2⟩
  done

end Pinwheel.Hardware.Buffered.Serial.Frames
