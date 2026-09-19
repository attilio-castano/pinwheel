import Pinwheel.Hardware.Serial.Receiver
import Pinwheel.Hardware.Loader.Delivery

/-! What the serial loader delivers.

A host *session* is any sample history made of idle samples (`csn` high) and
frames. A frame is 72 bits; a bit is the clock seen low at least once and then
high at least twice, with `mosi` carrying the bit at the first high sample — and
nothing else is asked: durations may differ from bit to bit, the protocol pins
may do anything, and `mosi` is free everywhere but at that one sample.

`session_delivers`: on any session, the core consumes exactly the session's
commands, in order, each on one edge with its word, and sees no command, no
reset and no init on every other edge. -/
namespace Pinwheel.Hardware.Serial
open Loader

/-! ### Running the receiver -/

def run (s : State) : List Inputs → State
  | [] => s
  | i :: rest => run (next i s) rest

/-- What the core consumes, edge by edge. -/
def fed (s : State) : List Inputs → List Machine.Inputs
  | [] => []
  | i :: rest => feed i s :: fed (next i s) rest

theorem run_append (s : State) (a b : List Inputs) : run s (a ++ b) = run (run s a) b := by
  induction a generalizing s with
  | nil => rfl
  | cons i rest ih => exact ih _

theorem fed_append (s : State) (a b : List Inputs) : fed s (a ++ b) = fed s a ++ fed (run s a) b := by
  induction a generalizing s with
  | nil => rfl
  | cons i rest ih => simp only [List.cons_append, fed, run, ih]

/-- The consumed inputs are the first components of the feeder's history. -/
theorem fed_history (s : State) (samples : List Inputs) :
    (model.history s (samples.map fun i => (i, i))).map Prod.fst = fed s samples := by
  induction samples generalizing s with
  | nil => rfl
  | cons i rest ih => simp only [List.map, Feeder.Model.history, fed, ih]; rfl

/-! ### What the core can be shown

`Quiet`, `Carries` and `Delivers` are the loader machine's
(`Loader/Delivery.lean`): an edge that tells the core nothing, an edge that
carries one command and its word, and a history that is a list of commands among
quiet edges. -/

open Machine (Quiet Carries Delivers)

theorem feed_quiet (i : Inputs) (s : State) (hi : i.init = false) (hf : s.fire = false) :
    Quiet (feed i s) := by
  refine ⟨hi, ?_, ?_⟩ <;> simp [feed, hf]

theorem feed_carries (i : Inputs) (s : State) (hi : i.init = false) (hf : s.fire = true) :
    Carries (feed i s) s.command s.shift := by
  refine ⟨hi, ?_, ?_, rfl⟩ <;> simp [feed, hf]

/-! ### Samples -/

/-- Selected, clock low. -/
def Low (i : Inputs) : Prop := i.init = false ∧ i.csn = false ∧ i.sck = false
/-- Selected, clock high. -/
def High (i : Inputs) : Prop := i.init = false ∧ i.csn = false ∧ i.sck = true
/-- Not selected. -/
def Idle (i : Inputs) : Prop := i.init = false ∧ i.csn = true

theorem next_low (i : Inputs) (s : State) (h : Low i) :
    next i s = {s with sckPrev := false, fire := false} := by
  obtain ⟨hi, hc, hk⟩ := h
  simp [next, taking, hi, hc, hk]

theorem next_rise (i : Inputs) (s : State) (h : High i) (hp : s.sckPrev = false) :
    next i s =
      { sckPrev := true
        count := if s.count == 71 then 0 else s.count + 1
        shift := shiftIn s.shift i.mosi
        command := if s.count == 7 then s.shift.extractLsb' 0 2 ++ BitVec.ofBool i.mosi else s.command
        fire := s.count == 71 } := by
  obtain ⟨hi, hc, hk⟩ := h
  simp [next, taking, hi, hc, hk, hp]

theorem next_high (i : Inputs) (s : State) (h : High i) (hp : s.sckPrev = true) :
    next i s = {s with sckPrev := true, fire := false} := by
  obtain ⟨hi, hc, hk⟩ := h
  simp [next, taking, hi, hc, hk, hp]

theorem next_idle (i : Inputs) (s : State) (h : Idle i) :
    next i s = {s with sckPrev := i.sck, count := 0, fire := false} := by
  obtain ⟨hi, hc⟩ := h
  simp [next, taking, hi, hc]

/-- Low samples move nothing and deliver nothing. -/
theorem run_lows (lows : List Inputs) (s : State) (hl : ∀ i ∈ lows, Low i) (hne : lows ≠ [])
    (hf : s.fire = false) :
    run s lows = {s with sckPrev := false, fire := false} ∧ Delivers (fed s lows) [] := by
  induction lows generalizing s with
  | nil => exact absurd rfl hne
  | cons i rest ih =>
    have hi := hl i (List.mem_cons_self ..)
    have hq : Quiet (feed i s) := feed_quiet i s hi.1 hf
    by_cases hrest : rest = []
    · subst hrest
      exact ⟨by simp only [run, next_low i s hi], .quiet hq .nil⟩
    · have hnext := next_low i s hi
      have := ih (next i s) (fun j hj => hl j (List.mem_cons_of_mem i hj)) hrest (by rw [hnext])
      refine ⟨?_, .quiet hq this.2⟩
      show run (next i s) rest = _
      rw [this.1, hnext]

/-- High samples after the first deliver a pending frame on their first edge and
nothing after it. -/
theorem run_highs (highs : List Inputs) (s : State) (hh : ∀ i ∈ highs, High i) (hne : highs ≠ [])
    (hp : s.sckPrev = true) :
    run s highs = {s with sckPrev := true, fire := false} ∧
      Delivers (fed s highs) (if s.fire then [(s.command, s.shift)] else []) := by
  induction highs generalizing s with
  | nil => exact absurd rfl hne
  | cons i rest ih =>
    have hi := hh i (List.mem_cons_self ..)
    have hnext : next i s = {s with sckPrev := true, fire := false} := next_high i s hi hp
    have htail : run (next i s) rest = {s with sckPrev := true, fire := false} ∧
        Delivers (fed (next i s) rest) [] := by
      by_cases hrest : rest = []
      · subst hrest
        exact ⟨by simp only [run, hnext], .nil⟩
      · have := ih (next i s) (fun j hj => hh j (List.mem_cons_of_mem i hj)) hrest (by rw [hnext])
        rw [hnext] at this ⊢
        exact ⟨this.1, by simpa using this.2⟩
    refine ⟨by simp only [run, htail.1], ?_⟩
    cases hf : s.fire
    · exact .quiet (feed_quiet i s hi.1 hf) htail.2
    · exact .command (feed_carries i s hi.1 hf) htail.2

/-- One bit on the wire. -/
structure IsBit (b : Bool) (samples : List Inputs) : Prop where
  split : ∃ lows first highs, samples = lows ++ first :: highs ∧ lows ≠ [] ∧ highs ≠ [] ∧
    (∀ i ∈ lows, Low i) ∧ High first ∧ first.mosi = b ∧ (∀ i ∈ highs, High i)

/-- A bit advances the receiver by exactly one shift, and delivers the frame if
it was the 72nd. -/
theorem run_bit (b : Bool) (samples : List Inputs) (s : State) (h : IsBit b samples)
    (hf : s.fire = false) :
    run s samples =
      { sckPrev := true
        count := if s.count == 71 then 0 else s.count + 1
        shift := shiftIn s.shift b
        command := if s.count == 7 then s.shift.extractLsb' 0 2 ++ BitVec.ofBool b else s.command
        fire := false } ∧
      Delivers (fed s samples)
        (if s.count == 71 then [(s.command, shiftIn s.shift b)] else []) := by
  obtain ⟨lows, first, highs, rfl, hlne, hhne, hl, hfirst, hb, hh⟩ := h.split
  obtain ⟨hrunL, hfedL⟩ := run_lows lows s hl hlne hf
  have hrise := next_rise first (run s lows) hfirst (by rw [hrunL])
  have hq : Quiet (feed first (run s lows)) := feed_quiet first _ hfirst.1 (by rw [hrunL])
  obtain ⟨hrunH, hfedH⟩ := run_highs highs (next first (run s lows)) hh hhne (by rw [hrise])
  constructor
  · rw [run_append]
    simp only [run]
    rw [hrunH, hrise, hrunL, hb]
  · rw [fed_append]
    simp only [fed]
    have hcmds : (if (next first (run s lows)).fire
          then [((next first (run s lows)).command, (next first (run s lows)).shift)] else []) =
        (if s.count == 71 then [(s.command, shiftIn s.shift b)] else []) := by
      rw [hrise, hrunL, hb]
      cases h71 : (s.count == 71)
      · simp
      · have h : s.count = 71 := by simpa using h71
        simp [h]
    have := hfedL.append (Delivers.quiet hq hfedH)
    rw [hcmds] at this
    exact this

/-! ### Frames -/

theorem shiftIn_getLsbD (x : BitVec 64) (b : Bool) (i : Nat) :
    (shiftIn x b).getLsbD i = if i = 0 then b else (decide (i < 64) && x.getLsbD (i - 1)) := by
  simp only [shiftIn, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool]
  by_cases h0 : i = 0
  · subst h0
    simp
  · have h1 : ¬ i < 1 := by omega
    have h63 : (i - 1 < 63) ↔ (i < 64) := by omega
    simp [h0, h1, h63]

/-- The `k`-th bit on the wire: the command byte, then the word, most significant first. -/
def frameBit (c : BitVec 8) (d : BitVec 64) (k : Nat) : Bool := (c ++ d).getLsbD (71 - k)

/-- Bits `k`, `k+1`, …, `k+n-1`, each with its own samples. -/
def bitsFrom (segments : Nat → List Inputs) : Nat → Nat → List Inputs
  | _, 0 => []
  | k, n + 1 => segments k ++ bitsFrom segments (k + 1) n

theorem bitsFrom_succ (segments : Nat → List Inputs) (k n : Nat) :
    bitsFrom segments k (n + 1) = bitsFrom segments k n ++ segments (k + n) := by
  induction n generalizing k with
  | zero => simp [bitsFrom]
  | succ n ih =>
    rw [bitsFrom, ih (k + 1), bitsFrom, List.append_assoc]
    congr 3
    omega

/-- A frame on the wire: 72 bits, each however long. -/
structure IsFrame (c : BitVec 8) (d : BitVec 64) (samples : List Inputs) : Prop where
  split : ∃ segments : Nat → List Inputs, samples = bitsFrom segments 0 72 ∧
    ∀ k, k < 72 → IsBit (frameBit c d k) (segments k)

/-- The receiver after `k` bits of the frame: the low bits of the shift register
are the frame's top bits, and the command is latched once its byte is complete. -/
structure Partial (c : BitVec 8) (d : BitVec 64) (k : Nat) (s : State) : Prop where
  count : s.count.toNat = k
  fire : s.fire = false
  shift : ∀ i, i < k → i < 64 → s.shift.getLsbD i = (c ++ d).getLsbD (i + (72 - k))
  command : 8 ≤ k → s.command = c.extractLsb' 0 3

theorem partial_start (c : BitVec 8) (d : BitVec 64) (s : State) (hc : s.count = 0)
    (hf : s.fire = false) : Partial c d 0 s :=
  ⟨by rw [hc]; rfl, hf, fun i hi => absurd hi (Nat.not_lt_zero i), fun h => absurd h (by decide)⟩

private theorem count_ne (s : State) (k n : Nat) (hk : s.count.toNat = k) (hn : k ≠ n) (h : n < 128) :
    (s.count == BitVec.ofNat 7 n) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro he
  apply hn
  rw [← hk, he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The three bits latched after the first byte are the command. -/
private theorem latched (c : BitVec 8) (d : BitVec 64) (x : BitVec 64)
    (hx : ∀ i, i < 7 → i < 64 → x.getLsbD i = (c ++ d).getLsbD (i + (72 - 7))) :
    x.extractLsb' 0 2 ++ BitVec.ofBool (frameBit c d 7) = c.extractLsb' 0 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h0 := hx 0 (by decide) (by decide)
  have h1 := hx 1 (by decide) (by decide)
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool, frameBit] at h0 h1 ⊢
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hcases with rfl | rfl | rfl <;> simp_all

/-- One more bit of the frame, short of the last. -/
theorem partial_bit (c : BitVec 8) (d : BitVec 64) (k : Nat) (s : State) (samples : List Inputs)
    (hp : Partial c d k s) (hk : k < 71) (hb : IsBit (frameBit c d k) samples) :
    Partial c d (k + 1) (run s samples) ∧ Delivers (fed s samples) [] := by
  obtain ⟨hrun, hfed⟩ := run_bit _ samples s hb hp.fire
  have h71 : (s.count == 71) = false := count_ne s k 71 hp.count (by omega) (by decide)
  rw [h71] at hrun hfed
  refine ⟨?_, by simpa using hfed⟩
  rw [hrun]
  refine ⟨?_, rfl, ?_, ?_⟩
  · show (s.count + 1).toNat = k + 1
    have hlt := s.count.isLt
    rw [BitVec.toNat_add, hp.count]
    show (k + 1) % 2 ^ 7 = k + 1
    exact Nat.mod_eq_of_lt (by omega)
  · intro i hi h64
    show (shiftIn s.shift (frameBit c d k)).getLsbD i = _
    rw [shiftIn_getLsbD]
    by_cases h0 : i = 0
    · subst h0
      simp only [frameBit, if_true]
      congr 1
      omega
    · rw [if_neg h0, hp.shift (i - 1) (by omega) (by omega)]
      have : i - 1 + (72 - k) = i + (72 - (k + 1)) := by omega
      simp [h64, this]
  · intro h8
    by_cases h7 : k = 7
    · subst h7
      have hc7 : (s.count == 7) = true := by
        apply beq_iff_eq.mpr
        apply BitVec.eq_of_toNat_eq
        rw [hp.count]
        rfl
      show (if (s.count == 7) = true then _ else _) = _
      rw [if_pos hc7]
      exact latched c d s.shift hp.shift
    · have hc7 : (s.count == 7) = false := count_ne s k 7 hp.count h7 (by decide)
      show (if (s.count == 7) = true then _ else _) = _
      rw [hc7]
      exact hp.command (by omega)

/-- Any run of bits short of the last delivers nothing. -/
theorem partial_bits (c : BitVec 8) (d : BitVec 64) (segments : Nat → List Inputs) (n k : Nat)
    (s : State) (hp : Partial c d k s) (hk : k + n ≤ 71)
    (hb : ∀ j, j < 72 → IsBit (frameBit c d j) (segments j)) :
    Partial c d (k + n) (run s (bitsFrom segments k n)) ∧ Delivers (fed s (bitsFrom segments k n)) [] := by
  induction n generalizing k s with
  | zero => exact ⟨hp, .nil⟩
  | succ n ih =>
    obtain ⟨hp', hfed⟩ := partial_bit c d k s (segments k) hp (by omega) (hb k (by omega))
    obtain ⟨hp'', hfed'⟩ := ih (k + 1) (run s (segments k)) hp' (by omega)
    rw [bitsFrom, run_append, fed_append]
    refine ⟨?_, by simpa using hfed.append hfed'⟩
    have : k + 1 + n = k + (n + 1) := by omega
    rw [← this]
    exact hp''

/-- **A frame delivers its command and its word, once**, and leaves the receiver
ready for the next frame. -/
theorem frame_delivers (c : BitVec 8) (d : BitVec 64) (samples : List Inputs) (s : State)
    (h : IsFrame c d samples) (hc : s.count = 0) (hf : s.fire = false) :
    (run s samples).count = 0 ∧ (run s samples).fire = false ∧
      Delivers (fed s samples) [(c.extractLsb' 0 3, d)] := by
  obtain ⟨segments, rfl, hb⟩ := h.split
  obtain ⟨hp, hfed⟩ := partial_bits c d segments 71 0 s (partial_start c d s hc hf) (by decide) hb
  simp only [Nat.zero_add] at hp
  obtain ⟨hrun, hlast⟩ := run_bit _ (segments 71) (run s (bitsFrom segments 0 71)) (hb 71 (by decide)) hp.fire
  have h71 : ((run s (bitsFrom segments 0 71)).count == 71) = true := by
    apply beq_iff_eq.mpr
    apply BitVec.eq_of_toNat_eq
    rw [hp.count]
    rfl
  rw [h71] at hrun hlast
  have hword : shiftIn (run s (bitsFrom segments 0 71)).shift (frameBit c d 71) = d := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [shiftIn_getLsbD]
    by_cases h0 : i = 0
    · subst h0
      rw [if_pos rfl]
      show (c ++ d).getLsbD (71 - 71) = d.getLsbD 0
      rw [BitVec.getLsbD_append, if_pos (by decide)]
    · have : i - 1 + (72 - 71) = i := by omega
      rw [if_neg h0, hp.shift (i - 1) (by omega) (by omega), this, BitVec.getLsbD_append, if_pos hi]
      simp [hi]
  rw [show bitsFrom segments 0 72 = bitsFrom segments 0 71 ++ segments (0 + 71) from bitsFrom_succ segments 0 71,
    Nat.zero_add, run_append, fed_append, hrun]
  refine ⟨rfl, rfl, ?_⟩
  have := hfed.append hlast
  rw [hword, hp.command (by decide)] at this
  simpa using this

/-! ### Sessions -/

theorem idle_quiet (i : Inputs) (s : State) (h : Idle i) (hf : s.fire = false) :
    (next i s).count = 0 ∧ (next i s).fire = false ∧ Quiet (feed i s) := by
  rw [next_idle i s h]
  exact ⟨rfl, rfl, feed_quiet i s h.1 hf⟩

/-- What a host may do: stay idle, or send a frame. -/
inductive Session : List Inputs → List (BitVec 3 × BitVec 64) → Prop where
  | nil : Session [] []
  | idle {i rest cs} : Idle i → Session rest cs → Session (i :: rest) cs
  | frame {c d samples rest cs} : IsFrame c d samples → Session rest cs →
      Session (samples ++ rest) ((c.extractLsb' 0 3, d) :: cs)

/-- **On any session the core consumes exactly the session's commands**, in
order, each on one edge with its word; every other edge is quiet. -/
theorem session_delivers {samples : List Inputs} {cs : List (BitVec 3 × BitVec 64)}
    (h : Session samples cs) (s : State) (hc : s.count = 0) (hf : s.fire = false) :
    Delivers (fed s samples) cs ∧ (run s samples).count = 0 ∧ (run s samples).fire = false := by
  induction h generalizing s with
  | nil => exact ⟨.nil, hc, hf⟩
  | idle hi _ ih =>
    obtain ⟨hc', hf', hq⟩ := idle_quiet _ s hi hf
    obtain ⟨hd, hrest⟩ := ih (next _ s) hc' hf'
    exact ⟨.quiet hq hd, hrest⟩
  | frame hframe _ ih =>
    obtain ⟨hc', hf', hd⟩ := frame_delivers _ _ _ s hframe hc hf
    obtain ⟨hd', hrest⟩ := ih (run s _) hc' hf'
    rw [fed_append, run_append]
    exact ⟨hd.append hd', hrest⟩

/-- `init` leaves the receiver ready, whatever it held. -/
theorem init_ready (i : Inputs) (s : State) (hi : i.init = true) :
    (next i s).count = 0 ∧ (next i s).fire = false := by
  simp [next, taking, hi]

end Pinwheel.Hardware.Serial
