import Pinwheel.Hardware.Uart.Circuit
import Pinwheel.Hardware.DecodedImplementation

namespace Pinwheel.Hardware.Uart.Structural
open Physical

theorem constant_toNat (d : Timing) (n : Nat) (hn : n ≤ d.frame) :
    (BitVec.ofNat (width d) n).toNat = n := by
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hn (frame_fits d))

theorem equal_constant (d : Timing) (value : BitVec (width d)) (n : Nat) (hn : n ≤ d.frame) :
    value = BitVec.ofNat (width d) n ↔ value.toNat = n := by
  rw [← BitVec.toNat_inj, constant_toNat d n hn]

theorem increment_toNat (d : Timing) (value : BitVec (width d)) (h : value.toNat < d.frame) :
    (value+1).toNat = value.toNat+1 := by
  rw [BitVec.toNat_add, show (1 : BitVec (width d)).toNat = 1 by
    simpa using constant_toNat d 1 (by have := d.frame_positive; omega)]
  exact Nat.mod_eq_of_lt (by have := frame_fits d; omega)

theorem bit_value (b : BitVec 1) : BitVec.ofBool (b == 1) = b := by
  rcases BitVec.eq_zero_or_eq_one b with h | h <;> simp [h]

theorem slice_bit (x : BitVec w) (k : Nat) : x.extractLsb' k 1 = BitVec.ofBool (x.getLsbD k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hz : j = 0 := by omega
  subst j
  simp

theorem phase_cases (value : BitVec 2) : value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3 := by
  have h := value.isLt
  have cases : value.toNat = 0 ∨ value.toNat = 1 ∨ value.toNat = 2 ∨ value.toNat = 3 := by omega
  rcases cases with h | h | h | h <;> simp_all [← BitVec.toNat_inj]

theorem ult_count_eval (d : Timing) (e : E d (width d)) (n : Nat) (hn : n ≤ d.frame)
    (i : Values Physical.Input) (s : Values (Register d)) :
    (Expr.ult e (count d n)).eval i s = BitVec.ofBool (decide ((e.eval i s).toNat < n)) := by
  simp [Expr.eval, count, constant_toNat d n hn]

theorem equal_count_eval (d : Timing) (e : E d (width d)) (n : Nat) (hn : n ≤ d.frame)
    (i : Values Physical.Input) (s : Values (Register d)) :
    (Expr.equal e (count d n)).eval i s = BitVec.ofBool (decide ((e.eval i s).toNat = n)) := by
  simp [Expr.eval, count, equal_constant d (e.eval i s) n hn]

set_option backward.isDefEq.respectTransparency false in
theorem packExpr_eval (bits : Fin 8 → E d 1) (i : Values Physical.Input) (s : Values (Register d)) :
    (packExpr bits).eval i s = Uart.pack (fun k => (bits k).eval i s == 1) := by
  simp only [packExpr, Uart.pack, Expr.eval, bit_value]

theorem rxUpdated_eval (d : Timing) (i : Values Physical.Input) (s : Values (Register d)) :
    (rxUpdated d).eval i s = Uart.rxUpdate d ((s .rxCount).toNat+1) (i rx == 1) (s .rxByte) := by
  rw [rxUpdated, packExpr_eval]
  unfold Uart.rxUpdate
  congr 1
  funext k
  have hp := d.sample_positive k
  have hb := d.sample_before_stop k
  have hf := stop_before_frame d
  have he : (s .rxCount).toNat = d.dataSample k-1 ↔ d.dataSample k = (s .rxCount).toNat+1 := by omega
  simp only [Expr.eval, count]
  simp only [equal_constant d (s .rxCount) (d.dataSample k-1) (by omega)]
  by_cases h : d.dataSample k = (s .rxCount).toNat+1
  · simp [h]
  · simp [he, h, slice_bit]
    cases (s .rxByte)[k.val] <;> rfl


theorem txSelect_eval (d : Timing) (i : Values Physical.Input) (s : Values (Register d))
    (ht : (s .txCount).toNat < d.frame) :
    (txSelect d).eval i s = BitVec.ofBool (Uart.frameBit (s .txByte) ((s .txCount).toNat/d.divisor)) := by
  have hc (k : Nat) (hk : k ≤ 10) : (BitVec.ofNat (width d) (k*d.divisor)).toNat = k*d.divisor :=
    constant_toNat d _ (by simpa only [Timing.frame] using Nat.mul_le_mul_right d.divisor hk)
  have hd : (BitVec.ofNat (width d) d.divisor).toNat = d.divisor := by simpa using hc 1 (by decide)
  have hq : (s .txCount).toNat / d.divisor < 10 :=
    (Nat.div_lt_iff_lt_mul d.positive).mpr ht
  simp only [txSelect, Expr.eval, count, hd, hc 2 (by decide), hc 3 (by decide),
    hc 4 (by decide), hc 5 (by decide), hc 6 (by decide), hc 7 (by decide), hc 8 (by decide), hc 9 (by decide)]
  have ht1 : (s .txCount).toNat < d.divisor ↔ (s .txCount).toNat/d.divisor < 1 := by
    simpa using (Nat.div_lt_iff_lt_mul (x := (s .txCount).toNat) (y := 1) d.positive).symm
  have htt (k : Nat) : (s .txCount).toNat < k*d.divisor ↔ (s .txCount).toNat/d.divisor < k :=
    (Nat.div_lt_iff_lt_mul d.positive).symm
  simp only [ht1, htt]
  have cases (q : Nat) (h : q < 10) : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨
      q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 := by omega
  rcases cases _ hq with h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, Uart.frameBit, slice_bit]


theorem txOkay_eval (d : Timing) (i : Values Physical.Input) (s : Values (Register d)) :
    (txOkay d).eval i s = BitVec.ofBool (decide ((s .txCount).toNat < d.frame)) :=
  ult_count_eval d _ _ (Nat.le_refl _) i s

theorem rxOkay_eval (d : Timing) (i : Values Physical.Input) (s : Values (Register d)) :
    (rxOkay d).eval i s = BitVec.ofBool (decide ((s .rxCount).toNat < d.stopSample)) :=
  ult_count_eval d _ _ (Nat.le_of_lt (stop_before_frame d)) i s

theorem txClosing_eval (d : Timing) (i : Values Physical.Input) (s : Values (Register d)) :
    (txClosing d).eval i s = BitVec.ofBool (decide ((s .txCount).toNat = d.frame-1)) :=
  equal_count_eval d _ _ (by omega) i s

theorem rxClosing_eval (d : Timing) (i : Values Physical.Input) (s : Values (Register d)) :
    (rxClosing d).eval i s = BitVec.ofBool (decide ((s .rxCount).toNat = d.stopSample-1)) :=
  equal_count_eval d _ _ (by have := stop_before_frame d; omega) i s

theorem badStart_eval (d : Timing) (i : Values Physical.Input) (s : Values (Register d)) :
    (badStart d).eval i s = BitVec.ofBool (decide ((s .rxCount).toNat+1 = d.half) && (i rx == 1)) := by
  have hp := d.half_positive
  have hb := d.half_lt
  have hf : d.half-1 ≤ d.frame := by unfold Timing.frame; omega
  have he : (s .rxCount).toNat = d.half-1 ↔ (s .rxCount).toNat+1 = d.half := by omega
  unfold badStart
  change (i rx &&& (Expr.equal (.reg .rxCount) (count d (d.half-1))).eval i s) = _
  rw [equal_count_eval d _ _ hf]
  rcases BitVec.eq_zero_or_eq_one (i rx) with hr | hr
  all_goals simp [Expr.eval, he, hr]
  by_cases h : (s .rxCount).toNat+1 = d.half <;> simp [h]

theorem reset_eq (d : Timing) (i : Values Physical.Input) (s : Values (Register d))
    (hr : i reset = 1#1) (r : Register d b) : (circuit d).step i s r = 0 := by
  simp [Hardware.Circuit.step, circuit, Expr.eval, hr]

theorem reset_view (d : Timing) (i : Values Physical.Input) (s : Values (Register d)) (hr : i reset = 1#1) :
    view ((circuit d).step i s) = Uart.initial := by
  simp [view, reset_eq d i s hr, Uart.initial]

theorem tx_step (d : Timing) (i : Values Physical.Input) (s : Values (Register d))
    (hr : i reset = 0#1) (hs : Valid d s) :
    (view ((circuit d).step i s)).tx = Uart.txStep d (decode i) (view s).tx := by
  rcases BitVec.eq_zero_or_eq_one (s .txActive) with ha | ha
  · rcases BitVec.eq_zero_or_eq_one (i txValid) with hv | hv
    all_goals simp [view, Hardware.Circuit.step, circuit, Expr.eval, txAccept, hr, ha, hv,
      Uart.txStep, decode]
  · have ht : (s .txCount).toNat < d.frame := hs.1 ha
    have hp := d.frame_positive
    have he : d.frame ≤ (s .txCount).toNat+1 ↔ (s .txCount).toNat = d.frame-1 := by omega
    by_cases hc : (s .txCount).toNat = d.frame-1
    all_goals simp [view, Hardware.Circuit.step, circuit, Expr.eval, txAccept, hr, ha, txOkay_eval,
      txClosing_eval, ht, hc, Uart.txStep, decode, he, WordOps.add_eval]
    · omega
    · exact Nat.mod_eq_of_lt (by have := frame_fits d; omega)


theorem rx_step (d : Timing) (i : Values Physical.Input) (s : Values (Register d))
    (hr : i reset = 0#1) (hs : Valid d s) :
    (view ((circuit d).step i s)).rx = Uart.rxStep d (decode i) (view s).rx := by
  rcases phase_cases (s .rxPhase) with hp | hp | hp | hp
  · rcases BitVec.eq_zero_or_eq_one (i rx) with hx | hx
    all_goals simp [view, Hardware.Circuit.step, circuit, Expr.eval, phase, rxDetect, rxAdvance,
      hr, hp, hx, Uart.rxStep, decode]
  · have ht : (s .rxCount).toNat < d.stopSample := hs.2.1 hp
    have hz := d.stop_positive
    have hh : d.half < d.stopSample := by have := d.positive; unfold Timing.stopSample; omega
    have hlast : d.stopSample-1 < d.stopSample := by omega
    have hfinal : d.stopSample ≤ d.stopSample-1+1 := by omega
    have hmod : ((s .rxCount).toNat+1) % 2^width d = (s .rxCount).toNat+1 :=
      Nat.mod_eq_of_lt (by have := stop_before_frame d; have := frame_fits d; omega)
    have hhmod : d.half % 2^width d = d.half :=
      Nat.mod_eq_of_lt (by have := stop_before_frame d; have := frame_fits d; omega)
    have he : d.stopSample ≤ (s .rxCount).toNat+1 ↔ (s .rxCount).toNat = d.stopSample-1 := by omega
    by_cases hb : (s .rxCount).toNat+1 = d.half
    all_goals by_cases hc : (s .rxCount).toNat = d.stopSample-1
    all_goals try omega
    all_goals rcases BitVec.eq_zero_or_eq_one (i rx) with hx | hx
    all_goals simp [view, Hardware.Circuit.step, circuit, Expr.eval, phase, rxDetect, rxAdvance,
      hr, hp, hx, Uart.rxStep, decode, rxOkay_eval, rxClosing_eval, badStart_eval, rxUpdated_eval,
      ht, hb, hc, he, hlast, hfinal, Nat.not_le.mpr hh, WordOps.add_eval, hmod, hhmod]
  · rcases BitVec.eq_zero_or_eq_one (i rx) with hx | hx
    all_goals simp [view, Hardware.Circuit.step, circuit, Expr.eval, phase, rxDetect, rxAdvance,
      hr, hp, hx, Uart.rxStep, decode]
  · exact False.elim (hs.2.2 hp)

theorem view_step (d : Timing) (i : Values Physical.Input) (s : Values (Register d)) (hs : Valid d s) :
    view ((circuit d).step i s) = (spec d).step i (view s) := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  · change Uart.State.mk _ _ = Uart.State.mk _ _
    congr 1
    · exact tx_step d i s hr hs
    · exact rx_step d i s hr hs
  · simp [reset_view d i s hr, spec, Uart.step, Uart.txStep, Uart.rxStep, decode, hr, Uart.initial]

set_option maxHeartbeats 1000000 in
theorem output_eq (d : Timing) (i : Values Physical.Input) (s : Values (Register d))
    (hs : Valid d s) (o : Physical.Output b) :
    (circuit d).observe i s o = (spec d).observe i (view s) o := by
  have tl : d.frame-1 < d.frame := by have := d.frame_positive; omega
  have rl : d.stopSample-1 < d.stopSample := by have := d.stop_positive; omega
  have te : d.frame ≤ d.frame-1+1 := by omega
  have re : d.stopSample ≤ d.stopSample-1+1 := by omega
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  · rcases BitVec.eq_zero_or_eq_one (s .txActive) with ha | ha
    all_goals rcases phase_cases (s .rxPhase) with hp | hp | hp | hp
    all_goals try exact False.elim (hs.2.2 hp)
    all_goals have ht : s .txActive = 1 → (s .txCount).toNat < d.frame := hs.1
    all_goals have hu : s .rxPhase = 1 → (s .rxCount).toNat < d.stopSample := hs.2.1
    all_goals have htx : s .txActive = 1 → (d.frame ≤ (s .txCount).toNat+1 ↔ (s .txCount).toNat = d.frame-1) := by intro h; have := ht h; omega
    all_goals have hrx : s .rxPhase = 1 → (d.stopSample ≤ (s .rxCount).toNat+1 ↔ (s .rxCount).toNat = d.stopSample-1) := by intro h; have := hu h; omega
    all_goals rcases BitVec.eq_zero_or_eq_one (i rx) with hx | hx
    all_goals by_cases hc : (s .txCount).toNat = d.frame-1
    all_goals by_cases hk : (s .rxCount).toNat = d.stopSample-1
    all_goals match o with
      | .at ⟨0, _⟩ | .at ⟨1, _⟩ | .at ⟨2, _⟩ | .at ⟨3, _⟩ | .at ⟨4, _⟩ | .at ⟨5, _⟩ =>
        simp [Hardware.Circuit.observe, circuit, spec, outputValues, Uart.observe, Uart.txLine,
          Uart.txReady, Uart.completed, Uart.arrival, Uart.framingError, view, decode, Expr.eval,
          phase, completedExpr, arrivalExpr, errorExpr, txOkay_eval, rxOkay_eval, txClosing_eval,
          rxClosing_eval, hr, ha, hp, hx, ht, hu, htx, hrx, hc, hk, tl, rl, te, re, txSelect_eval] <;> try rfl
      | .at ⟨k+6, h⟩ => change k+6 < 6 at h; omega
  · match o with
    | .at ⟨0, _⟩ | .at ⟨1, _⟩ | .at ⟨2, _⟩ | .at ⟨3, _⟩ | .at ⟨4, _⟩ | .at ⟨5, _⟩ =>
      simp [Hardware.Circuit.observe, circuit, spec, outputValues, Uart.observe, Uart.txLine,
        Uart.txReady, Uart.completed, Uart.arrival, Uart.framingError, decode, Expr.eval,
        completedExpr, arrivalExpr, errorExpr, hr] <;> rfl
    | .at ⟨k+6, h⟩ => change k+6 < 6 at h; omega

theorem tx_valid_step (d : Timing) (i : Values Physical.Input) (s : Values (Register d)) :
    (circuit d).step i s .txActive = 1 → ((circuit d).step i s .txCount).toNat < d.frame := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  · rcases BitVec.eq_zero_or_eq_one (s .txActive) with ha | ha
    · rcases BitVec.eq_zero_or_eq_one (i txValid) with hv | hv
      all_goals simp [Hardware.Circuit.step, circuit, Expr.eval, txAccept, hr, ha, hv, d.frame_positive]
    · by_cases ht : (s .txCount).toNat < d.frame
      · by_cases hc : (s .txCount).toNat = d.frame-1
        · have hl : d.frame-1 < d.frame := by have := d.frame_positive; omega
          simp [Hardware.Circuit.step, circuit, Expr.eval, txOkay_eval, txClosing_eval, hr, ha, hc, hl]
        · have hi : (s .txCount).toNat+1 < d.frame := by omega
          have hm : ((s .txCount).toNat+1) % 2^width d = (s .txCount).toNat+1 :=
            Nat.mod_eq_of_lt (Nat.lt_trans hi (frame_fits d))
          simp [Hardware.Circuit.step, circuit, Expr.eval, txAccept, txOkay_eval, txClosing_eval,
            hr, ha, ht, hc, WordOps.add_eval, hm, hi]
      · simp [Hardware.Circuit.step, circuit, Expr.eval, txOkay_eval, hr, ha, ht]
  · simp [reset_eq d i s hr]

theorem rx_valid_step (d : Timing) (i : Values Physical.Input) (s : Values (Register d)) :
    (circuit d).step i s .rxPhase = 1 → ((circuit d).step i s .rxCount).toNat < d.stopSample := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  · rcases phase_cases (s .rxPhase) with hp | hp | hp | hp
    · rcases BitVec.eq_zero_or_eq_one (i rx) with hx | hx
      all_goals simp [Hardware.Circuit.step, circuit, Expr.eval, phase, rxDetect, hr, hp, hx, d.stop_positive]
    · by_cases ht : (s .rxCount).toNat < d.stopSample
      · by_cases hc : (s .rxCount).toNat = d.stopSample-1
        · have hl : d.stopSample-1 < d.stopSample := by have := d.stop_positive; omega
          rcases BitVec.eq_zero_or_eq_one (i rx) with hx | hx
          all_goals simp [Hardware.Circuit.step, circuit, Expr.eval, phase, rxOkay_eval, rxClosing_eval, badStart_eval,
            hr, hp, hc, hl, hx]
        · have hi : (s .rxCount).toNat+1 < d.stopSample := by omega
          have hm : ((s .rxCount).toNat+1) % 2^width d = (s .rxCount).toNat+1 :=
            Nat.mod_eq_of_lt (Nat.lt_trans (Nat.lt_trans hi (stop_before_frame d)) (frame_fits d))
          rcases BitVec.eq_zero_or_eq_one ((badStart d).eval i s) with hb | hb
          all_goals simp [Hardware.Circuit.step, circuit, Expr.eval, phase, rxDetect, rxAdvance,
            rxOkay_eval, rxClosing_eval, hr, hp, ht, hc, hb, WordOps.add_eval, hm, hi]
      · simp [Hardware.Circuit.step, circuit, Expr.eval, phase, rxOkay_eval, hr, hp, ht]
    · rcases BitVec.eq_zero_or_eq_one (i rx) with hx | hx
      all_goals simp [Hardware.Circuit.step, circuit, Expr.eval, phase, hr, hp, hx]
    · simp [Hardware.Circuit.step, circuit, Expr.eval, phase, hr, hp]
  · simp [reset_eq d i s hr]

set_option backward.isDefEq.respectTransparency false in
theorem phase_valid_step (d : Timing) (i : Values Physical.Input) (s : Values (Register d)) :
    (circuit d).step i s .rxPhase ≠ 3 := by
  simp only [Hardware.Circuit.step, circuit, Expr.eval]
  intro h
  repeat first | split at h | contradiction

/-- Every raw state enters the scoped invariant in one edge; events on the
malformed pre-edge state are separately suppressed rather than reinterpreted. -/
theorem valid_step (d : Timing) (i : Values Physical.Input) (s : Values (Register d)) :
    Valid d ((circuit d).step i s) :=
  ⟨tx_valid_step d i s, rx_valid_step d i s, phase_valid_step d i s⟩

/-- Invalid TX counts recover quietly; the receiver is independent. -/
theorem tx_malformed_recovery (d : Timing) (i : Values Physical.Input) (s : Values (Register d))
    (ha : s .txActive = 1) (hc : ¬(s .txCount).toNat < d.frame) :
    (circuit d).step i s .txActive = 0 ∧
    (circuit d).observe i s tx = 1 ∧ (circuit d).observe i s Physical.txReady = 0 ∧
    (circuit d).observe i s txComplete = 0 := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  all_goals simp [Hardware.Circuit.step, Hardware.Circuit.observe, circuit, tx, Physical.txReady, txComplete,
    Expr.eval, completedExpr, txOkay_eval, hr, ha, hc]

def BadRx (d : Timing) (s : Values (Register d)) : Prop :=
  s .rxPhase = 3 ∨ (s .rxPhase = 1 ∧ ¬(s .rxCount).toNat < d.stopSample)

/-- Reserved RX phase3 and invalid active counts cannot report a byte or error. -/
theorem rx_malformed_recovery (d : Timing) (i : Values Physical.Input) (s : Values (Register d))
    (hs : BadRx d s) :
    (circuit d).step i s .rxPhase = 0 ∧
    (circuit d).observe i s rxValid = 0 ∧ (circuit d).observe i s rxData = 0 ∧
    (circuit d).observe i s Physical.framingError = 0 := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  all_goals rcases hs with hp | ⟨hp, hc⟩
  all_goals simp [Hardware.Circuit.step, Hardware.Circuit.observe, circuit, rxValid, rxData,
    Physical.framingError, Expr.eval, phase, arrivalExpr, errorExpr, rxOkay_eval, hr, hp] <;> try rfl
  all_goals simp [hc] <;> rfl

theorem tx_malformed_retained (d : Timing) (i : Values Physical.Input) (s : Values (Register d))
    (hr : i reset = 0) (ha : s .txActive = 1) (hc : ¬(s .txCount).toNat < d.frame) :
    (circuit d).step i s .txCount = s .txCount ∧ (circuit d).step i s .txByte = s .txByte := by
  simp [Hardware.Circuit.step, circuit, Expr.eval, txAccept, txOkay_eval, hr, ha, hc]

theorem rx_malformed_retained (d : Timing) (i : Values Physical.Input) (s : Values (Register d))
    (hr : i reset = 0) (hs : BadRx d s) :
    (circuit d).step i s .rxCount = s .rxCount ∧ (circuit d).step i s .rxByte = s .rxByte := by
  rcases hs with hp | ⟨hp, hc⟩
  · simp [Hardware.Circuit.step, circuit, Expr.eval, phase, rxDetect, rxAdvance, rxOkay_eval, hr, hp]
  · simp [Hardware.Circuit.step, circuit, Expr.eval, phase, rxDetect, rxAdvance, rxOkay_eval, hr, hp, hc]

theorem reset_outputs (d : Timing) (i : Values Physical.Input) (s : Values (Register d))
    (hr : i reset = 1) (o : Physical.Output b) :
    (circuit d).observe i s o = outputValues ⟨true, false, false, none, false⟩ o := by
  match o with
  | .at ⟨0, _⟩ | .at ⟨1, _⟩ | .at ⟨2, _⟩ | .at ⟨3, _⟩ | .at ⟨4, _⟩ | .at ⟨5, _⟩ =>
    simp [Hardware.Circuit.observe, circuit, outputValues, Expr.eval, completedExpr, arrivalExpr,
      errorExpr, hr] <;> rfl
  | .at ⟨k+6, h⟩ => change k+6 < 6 at h; omega

theorem view_valid (d : Timing) (s : Values (Register d)) (hs : Valid d s) : Uart.Valid d (view s) := by
  by_cases ht : s .txActive = 1
  all_goals by_cases hr : s .rxPhase = 1
  all_goals by_cases hw : s .rxPhase = 2
  all_goals simp_all [Uart.Valid, view, Valid]

theorem view_encode (d : Timing) (s : Uart.State) (hs : Uart.Valid d s) : view (encode d s) = s := by
  have ht (n : Nat) (h : n < d.frame) := constant_toNat d n (Nat.le_of_lt h)
  have hr (n : Nat) (h : n < d.stopSample) := constant_toNat d n (by have := stop_before_frame d; omega)
  rcases s with ⟨t, r⟩
  cases t <;> cases r
  all_goals simp_all [Uart.Valid, view, encode]

theorem encode_valid (d : Timing) (s : Uart.State) (hs : Uart.Valid d s) : Valid d (encode d s) := by
  have ht (n : Nat) (h : n < d.frame) := constant_toNat d n (Nat.le_of_lt h)
  have hr (n : Nat) (h : n < d.stopSample) := constant_toNat d n (by have := stop_before_frame d; omega)
  rcases s with ⟨t, r⟩
  cases t <;> cases r
  all_goals simp_all [Uart.Valid, Valid, encode]

def implementation (d : Timing) : Hardware.DecodedImplementation (circuit d) (spec d) where
  Valid := Valid d
  view := view
  preserved i s _ := valid_step d i s
  step_eq := view_step d
  output_eq := fun i s h {_} o => output_eq d i s h o

def resetCertificate (d : Timing) : (implementation d).Reset reset where
  initial _ := Uart.initial
  reset_valid i s _ := valid_step d i s
  reset_view := reset_view d

end Pinwheel.Hardware.Uart.Structural
