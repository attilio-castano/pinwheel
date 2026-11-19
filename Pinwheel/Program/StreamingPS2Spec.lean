import Std

/-! A keyboard-to-host frame at the modeled 4 MHz core clock. The peer owns
both wires. Each high and low half-period before the last fall can vary
independently over 120 through 200 clocks (30 through 50 microseconds). -/
namespace Pinwheel.Program.StreamingPS2

def clockAt (raw : List (BitVec 2)) (k : Nat) : Bool := (raw[k]?.getD 0)[0]

def dataAt (raw : List (BitVec 2)) (k : Nat) : Bool := (raw[k]?.getD 0)[1]

/-- Exact digital clock levels between successive falling edges. After the
last low half-period the clock stays released until the receive program ends. -/
inductive Clocking (raw : List (BitVec 2)) : Nat → List Nat → Prop where
  | last {fall rise : Nat}
      (lowMin : fall + 120 ≤ rise) (lowMax : rise ≤ fall + 200)
      (low : ∀ k, fall ≤ k → k < rise → clockAt raw k = false)
      (high : ∀ k, rise ≤ k → k < raw.length → clockAt raw k = true)
      (length : raw.length = fall + 221) : Clocking raw fall []
  | next {fall rise nextFall : Nat} {later : List Nat}
      (lowMin : fall + 120 ≤ rise) (lowMax : rise ≤ fall + 200)
      (highMin : rise + 120 ≤ nextFall) (highMax : nextFall ≤ rise + 200)
      (low : ∀ k, fall ≤ k → k < rise → clockAt raw k = false)
      (high : ∀ k, rise ≤ k → k < nextFall → clockAt raw k = true)
      (laterClock : Clocking raw nextFall later) : Clocking raw fall (nextFall :: later)

theorem Clocking.fits (clocking : Clocking raw fall later) : fall + 221 ≤ raw.length := by
  induction clocking with
  | last _ _ _ _ length => omega
  | next lowMin _ highMin _ _ _ _ laterFits => omega

private theorem Clocking.bounds (clocking : Clocking raw fall later) (member : k ∈ fall :: later) :
    fall ≤ k ∧ k + 221 ≤ raw.length := by
  induction clocking with
  | last _ _ _ _ length =>
    simp only [List.mem_singleton] at member
    omega
  | next lowMin _ highMin _ _ _ laterClock ih =>
    rcases List.mem_cons.mp member with rfl | later
    · have fits := laterClock.fits
      omega
    · have inside := ih later
      omega

private theorem no_fall_inside (low : ∀ k, fall ≤ k → k < rise → clockAt raw k = false)
    (high : ∀ k, rise ≤ k → k < stop → clockAt raw k = true)
    (after : fall < k) (before : k < stop) :
    ¬ (clockAt raw (k-1) = true ∧ clockAt raw k = false) := by
  intro ⟨wasHigh,nowLow⟩
  by_cases stillLow : k < rise
  · rw [low _ (by omega) (by omega)] at wasHigh
    contradiction
  · rw [high _ (by omega) before] at nowLow
    contradiction

private theorem Clocking.cut_iff (clocking : Clocking raw fall later)
    (prior : clockAt raw (fall-1) = true) (after : fall ≤ k) (inside : k < raw.length) :
    (clockAt raw (k-1) = true ∧ clockAt raw k = false) ↔ k ∈ fall :: later := by
  induction clocking with
  | @last fall rise lowMin _ low high _ =>
    by_cases atFall : k = fall
    · subst k
      simp [prior,low _ (Nat.le_refl _) (by omega)]
    · simp only [List.mem_singleton,atFall,iff_false]
      exact no_fall_inside low high (by omega) inside
  | @next fall rise nextFall _ lowMin _ highMin _ low high laterClock ih =>
    by_cases inLater : nextFall ≤ k
    · rw [ih (high _ (by omega) (by omega)) inLater]
      simp [show k ≠ fall by omega]
    · have noLater : k ∉ nextFall :: _ := fun member => inLater (laterClock.bounds member).1
      by_cases atFall : k = fall
      · subst k
        simp [prior,low _ (Nat.le_refl _) (by omega)]
      · simp only [List.mem_cons,atFall,noLater,or_false,iff_false]
        exact no_fall_inside low high (by omega) (by omega)

/-- The waveform is specified solely by the peer's raw line samples. Its
data field gives the bit present at each externally generated falling edge. -/
structure PeerFrame (raw : List (BitVec 2)) (symbols : List Bool) where
  firstFall : Nat
  laterFalls : List Nat
  laterCount : laterFalls.length = 10
  start : 3 ≤ firstFall
  idle : ∀ k, k < firstFall → clockAt raw k = true
  clocking : Clocking raw firstFall laterFalls
  data : (firstFall :: laterFalls).map (dataAt raw) = symbols

def PeerFrame.falls (peer : PeerFrame raw symbols) : List Nat := peer.firstFall :: peer.laterFalls

@[simp] theorem PeerFrame.falls_length (peer : PeerFrame raw symbols) : peer.falls.length = 11 := by
  simp [PeerFrame.falls,peer.laterCount]

/-- The schedule lists exactly the high-to-low raw clock transitions. -/
theorem PeerFrame.falling_iff (peer : PeerFrame raw symbols) (k : Nat) :
    (0 < k ∧ k < raw.length ∧ clockAt raw (k-1) = true ∧ clockAt raw k = false) ↔
      k ∈ peer.falls := by
  have first := peer.start
  by_cases after : peer.firstFall ≤ k
  · have prior : clockAt raw (peer.firstFall-1) = true := peer.idle _ (by omega)
    constructor
    · intro edge
      exact (peer.clocking.cut_iff prior after edge.2.1).mp edge.2.2
    · intro member
      have within := (peer.clocking.bounds member).2
      exact ⟨by omega,by omega,(peer.clocking.cut_iff prior after (by omega)).mpr member⟩
  · constructor
    · intro edge
      have low := edge.2.2.2
      rw [peer.idle _ (by omega)] at low
      contradiction
    · intro member
      exact False.elim (after (peer.clocking.bounds member).1)

def byteBits (value : BitVec 8) : List Bool :=
  List.ofFn fun bit : Fin 8 => value.getLsbD bit.val

/-- The parity symbol makes the total number of set data and parity bits odd. -/
def oddParity (bits : List Bool) : Bool := !(bits.foldl Bool.xor false)

def frameBits (value : BitVec 8) : List Bool :=
  false :: byteBits value ++ [oddParity (byteBits value),true]

def badStartBits (value : BitVec 8) : List Bool :=
  true :: byteBits value ++ [oddParity (byteBits value),true]

def badParityBits (value : BitVec 8) : List Bool :=
  false :: byteBits value ++ [!oddParity (byteBits value),true]

def badStopBits (value : BitVec 8) : List Bool :=
  false :: byteBits value ++ [oddParity (byteBits value),false]

def decodeByte (bits : List Bool) : BitVec 8 := (BitVec.ofBoolListLE bits).setWidth 8

/-- Check the complete frame after transfer from the receive FIFO. -/
def decodeFrame (bits : List Bool) : Option (BitVec 8) :=
  match bits with
  | false :: body =>
    let data := body.take 8
    match body.drop 8 with
    | [receivedParity,true] =>
      if receivedParity = oddParity data then some (decodeByte data) else none
    | _ => none
  | _ => none

@[simp] theorem byteBits_length (value : BitVec 8) : (byteBits value).length = 8 := by
  simp [byteBits]

@[simp] theorem frameBits_length (value : BitVec 8) : (frameBits value).length = 11 := by
  simp [frameBits]

@[simp] theorem badStartBits_length (value : BitVec 8) : (badStartBits value).length = 11 := by
  simp [badStartBits]

@[simp] theorem badParityBits_length (value : BitVec 8) : (badParityBits value).length = 11 := by
  simp [badParityBits]

@[simp] theorem badStopBits_length (value : BitVec 8) : (badStopBits value).length = 11 := by
  simp [badStopBits]

private theorem decode_byteBits (value : BitVec 8) : decodeByte (byteBits value) = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit valid
  simp only [decodeByte,BitVec.getLsbD_setWidth,valid,decide_true,Bool.true_and,
    BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,byteBits,List.getElem?_ofFn,
    dif_pos True.intro,Option.getD_some]

private theorem decode_fields (value : BitVec 8) (parity stop : Bool) :
    decodeFrame (false :: byteBits value ++ [parity,stop]) =
      if stop && (parity == oddParity (byteBits value)) then some value else none := by
  simp only [List.cons_append,decodeFrame]
  rw [List.take_append_of_le_length (by simp),List.take_of_length_le (by simp),
    show (byteBits value ++ [parity,stop]).drop 8 = [parity,stop] by
      rw [← byteBits_length value]
      exact List.drop_append_length]
  cases stop <;> simp [decode_byteBits]

theorem decode_frame (value : BitVec 8) : decodeFrame (frameBits value) = some value := by
  rw [frameBits,decode_fields]
  simp

theorem decode_badStart (value : BitVec 8) : decodeFrame (badStartBits value) = none := rfl

theorem decode_badParity (value : BitVec 8) : decodeFrame (badParityBits value) = none := by
  rw [badParityBits,decode_fields]
  cases oddParity (byteBits value) <;> rfl

theorem decode_badStop (value : BitVec 8) : decodeFrame (badStopBits value) = none := by
  rw [badStopBits,decode_fields]
  rfl

end Pinwheel.Program.StreamingPS2
