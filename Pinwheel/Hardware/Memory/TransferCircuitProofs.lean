import Pinwheel.Hardware.Memory.TransferCircuit
import Pinwheel.Hardware.Memory.StreamFlopsProofs

namespace Pinwheel.Hardware.Memory.TransferCircuit

open TransferInterface

namespace Arithmetic

theorem encoded_toNat (a k : Nat) (hk : k ≤ 2^a) : (BitVec.ofNat (a+1) k).toNat = k := by
  have hp : 0 < 2^a := Nat.pow_pos (by decide)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  rw [Nat.pow_succ]
  omega

theorem extended_toNat (base : BitVec a) : (base.setWidth (a+1)).toNat = base.toNat :=
  BitVec.toNat_setWidth_of_le (by omega)

theorem remaining_toNat (base : BitVec a) :
    (BitVec.ofNat (a+1) (2^a) - base.setWidth (a+1)).toNat = 2^a-base.toNat := by
  rw [BitVec.toNat_sub_of_le]
  · rw [encoded_toNat a _ (by omega), extended_toNat]
  · rw [BitVec.le_def, extended_toNat, encoded_toNat a _ (by omega)]
    exact Nat.le_of_lt base.isLt

theorem successor_eq (a index : Nat) :
    BitVec.ofNat (a+1) index + 1 = BitVec.ofNat (a+1) (index+1) := by
  simpa using (BitVec.ofNat_add_ofNat (n := a+1) index 1)

theorem successor_toNat (a index length : Nat) (hi : index < length) (hl : length ≤ 2^a) :
    (BitVec.ofNat (a+1) index + 1).toNat = index+1 := by
  rw [successor_eq a index, encoded_toNat a _ (by omega)]

theorem address_slice (base : BitVec a) (index : Nat) :
    (base.setWidth (a+1) + BitVec.ofNat (a+1) index).extractLsb' 0 a =
      BitVec.ofNat a (base.toNat+index) := by
  rw [← BitVec.setWidth_eq_extractLsb' (by omega), BitVec.setWidth_add _ _ (by omega)]
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq,
    BitVec.setWidth_ofNat_of_le (by omega), BitVec.ofNat_add]
  simp

theorem concat_zero_eq_extend (base : BitVec a) :
    ((0 : BitVec 1) ++ base).cast (Nat.add_comm 1 a) = base.setWidth (a+1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_append]

end Arithmetic

theorem eval_cast (h : a = b) (e : Expr I R a) (i : Values I) (s : Values R) :
    (cast (congrArg (Expr I R) h) e).eval i s = (e.eval i s).cast h := by
  cases h
  rfl

@[simp] theorem widen_eval (e : Expr I R a) (i : Values I) (s : Values R) :
    (widen e).eval i s = (e.eval i s).setWidth (a+1) := by
  rw [widen, eval_cast]
  exact Arithmetic.concat_zero_eq_extend (e.eval i s)

@[simp] theorem remaining_toNat (e : Expr (Input a wi) (Register a) a)
    (i : Values (Input a wi)) (s : Values (Register a)) :
    ((remaining e).eval i s).toNat = 2^a-(e.eval i s).toNat := by
  rw [remaining, Expr.eval, widen_eval]
  exact Arithmetic.remaining_toNat (e.eval i s)

@[simp] theorem invalidPhase_eval (i : Values (Input a wi)) (s : TransferModel.Control a) :
    invalidPhase.eval i (encode s) = 0 := by
  cases hp : s.phase <;> simp [invalidPhase, isPhase, Expr.eval, encode, phaseBits, hp]

@[simp] theorem memoryReset_eval (i : Values (Input a wi)) (s : TransferModel.Control a) :
    memoryResetExpr.eval i (encode s) = i reset := by
  simp [memoryResetExpr, Expr.eval]

@[simp] theorem indexedAddress_eval (e : Expr (Input a wi) (Register a) a)
    (i : Values (Input a wi)) (s : TransferModel.Control a) :
    (indexedAddress e).eval i (encode s) =
      BitVec.ofNat a ((e.eval i (encode s)).toNat + s.index) := by
  simp [indexedAddress, Expr.eval, encode, Arithmetic.address_slice]

def rawCommand (i : Values (Input a wi)) : TransferModel.RawCommand a :=
  ⟨i sourceBase, i destinationBase, i length⟩

abbrev fits (i : Values (Input a wi)) : Prop :=
  (i length).toNat ≤ 2^a-(i sourceBase).toNat ∧ (i length).toNat ≤ 2^a-(i destinationBase).toNat

@[simp] theorem zeroLength_eval (i : Values (Input a wi)) (s : Values (Register a)) :
    zeroLength.eval i s = BitVec.ofBool (decide ((i length).toNat = 0)) := by
  change BitVec.ofBool (decide (i length = 0#(a+1))) = _
  by_cases h : i length = 0#(a+1)
  · simp [h]
  · have hn : (i length).toNat ≠ 0 := fun hn => h (BitVec.eq_of_toNat_eq hn)
    simp [h, hn]

@[simp] theorem commandFits_eval (i : Values (Input a wi)) (s : Values (Register a)) :
    commandFits.eval i s = BitVec.ofBool (decide (fits i)) := by
  simp only [commandFits, Expr.eval, remaining_toNat]
  by_cases hs : (i length).toNat ≤ 2^a-(i sourceBase).toNat <;>
    by_cases hd : (i length).toNat ≤ 2^a-(i destinationBase).toNat <;>
    simp [fits, ← Nat.not_le, hs, hd]

@[simp] theorem nextIndex_eval (i : Values (Input a wi)) (s : TransferModel.Control a) :
    nextIndex.eval i (encode s) = BitVec.ofNat (a+1) (s.index+1) := by
  simp only [nextIndex, Hardware.Stream.eval_plus, Expr.eval, encode]
  exact Arithmetic.successor_eq a s.index

theorem more_eval (i : Values (Input a wi)) (s : TransferModel.Control a)
    (hk : s.index < s.config.length) (hl : s.config.length ≤ 2^a) :
    more.eval i (encode s) = BitVec.ofBool (decide (s.index+1 < s.config.length)) := by
  simp only [more, Expr.eval, nextIndex_eval, encode]
  rw [Arithmetic.encoded_toNat a (s.index+1) (by omega), Arithmetic.encoded_toNat a s.config.length hl]

set_option maxHeartbeats 800000 in
theorem step_eq (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi))
    (s : TransferModel.Control a) (hs : s.Valid) (r : Register a b) :
    (circuit m).step i (encode s) r = encode ((TransferInterface.spec m).step i s) r := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  · cases hp : s.phase with
    | idle =>
      rcases BitVec.eq_zero_or_eq_one (i startValid) with hstart | hstart
      · cases r <;> simp [Circuit.step, circuit, normalNext, start, isPhase, Expr.eval,
          encode, phaseBits, TransferInterface.spec, decode, TransferModel.step, hr, hp, hstart]
      · by_cases hsrc : (i length).toNat ≤ 2^a-(i sourceBase).toNat <;>
          by_cases hdst : (i length).toNat ≤ 2^a-(i destinationBase).toNat <;>
          by_cases hz : i length = 0#(a+1)
        all_goals cases r <;> simp [Circuit.step, circuit, normalNext, start, isPhase,
          Expr.eval, encode, phaseBits, TransferInterface.spec, decode, TransferModel.step,
          TransferModel.decode, TransferModel.initialControl, TransferModel.emptyConfig,
          fits, hr, hp, hstart, hsrc, hdst, hz]
        all_goals
          have hnzero : (i length).toNat ≠ 0 := by
            intro h
            apply hz
            exact BitVec.eq_of_toNat_eq h
          simp [hnzero] <;> change (0#1) = BitVec.ofBool ((i length).toNat == 0)
          all_goals exact (congrArg BitVec.ofBool (beq_eq_false_iff_ne.mpr hnzero)).symm
    | issueRead =>
      rcases BitVec.eq_zero_or_eq_one (i sourceRequestReady) with hready | hready
      all_goals cases r <;> simp [Circuit.step, circuit, normalNext, start, isPhase, Expr.eval,
        encode, phaseBits, TransferInterface.spec, decode, TransferModel.step, hr, hp, hready]
    | transfer =>
      have hl : s.config.length ≤ 2^a := by have h := s.config.sourceFits; omega
      have hk : s.index < s.config.length := by simp [TransferModel.Control.Valid, hp] at hs; omega
      have hmore := more_eval i s hk hl
      rcases BitVec.eq_zero_or_eq_one (i sourceResponseValid) with hvalid | hvalid <;>
        rcases BitVec.eq_zero_or_eq_one (i destinationRequestReady) with hready | hready <;>
        by_cases hn : s.index+1 < s.config.length
      all_goals cases r <;> simp [Circuit.step, circuit, normalNext, start, isPhase, fire, Expr.eval,
        encode, phaseBits, TransferInterface.spec, decode, TransferModel.step, hr, hp, hvalid, hready,
        hmore, hn]
      all_goals simp [← Nat.not_lt, hn]
  · cases r <;> simp [Circuit.step, circuit, Expr.eval, hr, encode, TransferInterface.spec,
      decode, TransferModel.step, TransferModel.initialControl, TransferModel.emptyConfig, phaseBits]

set_option maxHeartbeats 1000000 in
theorem output_eq (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi))
    (s : TransferModel.Control a) (o : Output a wo b) :
    (circuit m).observe i (encode s) o = (TransferInterface.spec m).observe i s o := by
  cases o with
  | «at» k =>
    match k with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ |
        ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩ | ⟨9, _⟩ | ⟨10, _⟩ =>
      rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
      all_goals cases hp : s.phase
      all_goals rcases BitVec.eq_zero_or_eq_one (i sourceResponseValid) with hv | hv
      all_goals simp [Circuit.observe, circuit, gated, destinationValid,
        isPhase, Expr.eval, encode, phaseBits, hr, hp, hv, TransferInterface.spec,
        TransferInterface.outputValues, TransferInterface.decode, TransferModel.observe,
        TransferModel.Config.sourceRange, TransferModel.Config.destinationRange, TransferRange.Range.index]
      all_goals try rfl
      all_goals rcases BitVec.eq_zero_or_eq_one (i destinationRequestReady) with hd | hd
      all_goals simp [hd]
    | ⟨k+11, h⟩ => exact False.elim (by change k+11 < 11 at h; omega)

/-- The controller refinement accepts arbitrary raw inputs. Its state invariant
is established by reset and preserved by every step. -/
def implementation (m : Hardware.Stream.Map wi wo) :
    Implementation (circuit (a := a) m) (TransferInterface.spec m) where
  Valid := TransferModel.Control.Valid
  encode := encode
  preserved i s hs := TransferModel.step_valid (decode i) s hs
  step_eq i s hs {_} r := step_eq m i s hs r
  output_eq i s _ {_} o := output_eq m i s o

/-- External reset recovers arbitrary physical bits, without decoding or
assuming a valid stored command. -/
theorem reset_eq (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi))
    (s : Values (Register a)) (hr : i reset = 1) (r : Register a b) :
    (circuit m).step i s r = encode (TransferModel.initialControl a) r := by
  cases r <;> simp [Circuit.step, circuit, Expr.eval, hr, encode,
    TransferModel.initialControl, TransferModel.emptyConfig, phaseBits]

def resetCertificate (m : Hardware.Stream.Map wi wo) : (implementation (a := a) m).Reset reset where
  initial := TransferModel.initialControl a
  initial_valid := by simp [implementation, TransferModel.Control.Valid,
    TransferModel.initialControl, TransferModel.emptyConfig]
  reset_eq i s hr {_} r := reset_eq m i s hr r

theorem trace_after_reset (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi))
    (s : Values (Register a)) (h : i reset = 1) (inputs : List (Values (Input a wi))) :
    (circuit m).component.trace ((circuit m).step i s) inputs =
      (TransferInterface.spec m).trace (TransferModel.initialControl a) inputs :=
  Implementation.Reset.trace_after_reset (implementation m) reset (resetCertificate m) i s h inputs

/-- The reserved phase code cancels transactions and reports an error on the
next edge. External reset retains priority over this recovery. -/
theorem recovery_eq (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi))
    (s : Values (Register a)) (hr : i reset = 0) (hp : s .phase = 3) (r : Register a b) :
    (circuit m).step i s r = encode { TransferModel.initialControl a with error := true } r := by
  cases r <;> simp [Circuit.step, circuit, Expr.eval, hr, hp, invalidPhase, isPhase,
    recoveryValue, encode, TransferModel.initialControl, TransferModel.emptyConfig, phaseBits]

theorem memoryReset_reset (i : Values (Input a wi)) (s : Values (Register a))
    (hr : i reset = 1) : memoryResetExpr.eval i s = 1 := by
  rcases BitVec.eq_zero_or_eq_one (invalidPhase.eval i s) with hp | hp <;>
    simp [memoryResetExpr, Expr.eval, hr, hp]

theorem memoryReset_recovery (i : Values (Input a wi)) (s : Values (Register a))
    (hp : s .phase = 3) : memoryResetExpr.eval i s = 1 := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr <;>
    simp [memoryResetExpr, invalidPhase, isPhase, Expr.eval, hp, hr]

/-- Reset and reserved-phase recovery gate every control and memory transaction
pin; the auxiliary adapter reset alone remains asserted. -/
theorem quiescent_outputs (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi))
    (s : Values (Register a)) (h : memoryResetExpr.eval i s = 1) (o : Output a wo b) :
    (circuit m).observe i s o =
      outputValues true ⟨false, false, false, false, none, false, none⟩ o := by
  cases o with
  | «at» k =>
    match k with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ |
      ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩ | ⟨9, _⟩ | ⟨10, _⟩ =>
      all_goals simp [Circuit.observe, circuit, gated, Expr.eval, outputValues, h] <;> rfl
    | ⟨k+11, hk⟩ => exact False.elim (by change k+11 < 11 at hk; omega)

theorem reset_outputs (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi))
    (s : Values (Register a)) (h : i reset = 1) (o : Output a wo b) :
    (circuit m).observe i s o =
      outputValues true ⟨false, false, false, false, none, false, none⟩ o :=
  quiescent_outputs m i s (memoryReset_reset i s h) o

theorem recovery_outputs (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi))
    (s : Values (Register a)) (h : s .phase = 3) (o : Output a wo b) :
    (circuit m).observe i s o =
      outputValues true ⟨false, false, false, false, none, false, none⟩ o :=
  quiescent_outputs m i s (memoryReset_recovery i s h) o

/-- Both adapter response slots are canceled, while their complete pre-edge
arrays and Q registers are retained. This covers reserved-phase recovery as
well as external reset and permits arbitrary initial memory bits. -/
theorem paired_memory_reset (m : Hardware.Stream.Map wi wo) (i : Values (Input a wi))
    (s : Values (Register a)) (source : Values (StreamFlops.Register a wi))
    (destination : Values (StreamFlops.Register a wo))
    (h : memoryResetExpr.eval i s = 1) :
    (fun {b} (r : StreamFlops.Register a wi b) => (StreamFlops.circuit a wi).step
      (sourceMemoryPins ((circuit m).observe i s)) source r) =
        @StreamFlops.encode a wi ⟨(StreamFlops.view source).memory, false⟩ ∧
    (fun {b} (r : StreamFlops.Register a wo b) => (StreamFlops.circuit a wo).step
      (destinationMemoryPins ((circuit m).observe i s)) destination r) =
        @StreamFlops.encode a wo ⟨(StreamFlops.view destination).memory, false⟩ := by
  constructor
  · apply StreamFlops.reset_eq
    exact h
  · apply StreamFlops.reset_eq
    exact h

end Pinwheel.Hardware.Memory.TransferCircuit
