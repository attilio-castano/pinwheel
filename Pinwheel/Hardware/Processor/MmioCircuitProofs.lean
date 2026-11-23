import Pinwheel.Hardware.Processor.MmioCircuit
import Pinwheel.Hardware.DecodedImplementation

namespace Pinwheel.Hardware.Processor.MmioCircuit
open MmioInterface

theorem device_cases (d : BitVec 2) : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by
  have h := d.isLt
  have cases : d.toNat = 0 ∨ d.toNat = 1 ∨ d.toNat = 2 ∨ d.toNat = 3 := by omega
  rcases cases with h | h | h | h
  all_goals simp_all [← BitVec.toNat_inj]

@[simp] theorem view_encode (s : MmioModel.State) : view (encode s) = s := by
  cases s with
  | mk gpioValue timerValue tx rx overflow frame =>
    cases tx <;> cases rx <;> cases overflow <;> cases frame <;> rfl

def cpuView (i : Values Input) (s : Values Register) : MmioModel.State :=
  ⟨if gpioWrite.eval i s = 1 then i data else s gpio, s timer,
    if txStart.eval i s = 1 then some ((i data).extractLsb' 0 8) else (view s).tx,
    if rxConsume.eval i s = 1 then none else (view s).rx,
    (s overrun == 1) && !((clearErrors.eval i s == 1) && (i data).getLsbD 2),
    (s framing == 1) && !((clearErrors.eval i s == 1) && (i data).getLsbD 3)⟩

set_option maxHeartbeats 2000000 in
theorem cpuView_eq (i : Values Input) (s : Values Register) :
    cpuView i s = MmioModel.cpuState (decode i) (view s) := by
  rcases BitVec.eq_zero_or_eq_one (i requestValid) with hv | hv
  · simp [cpuView, MmioModel.cpuState, decode, view, gpioWrite, txStart, rxConsume,
      clearErrors, Expr.eval, hv]
  · rcases device_cases (i device) with hd | hd | hd | hd
    all_goals rcases BitVec.eq_zero_or_eq_one (i write) with hw | hw
    all_goals rcases BitVec.eq_zero_or_eq_one (s txActiveReg) with ht | ht
    all_goals rcases BitVec.eq_zero_or_eq_one (s rxValidReg) with hx | hx
    all_goals simp [cpuView, MmioModel.cpuState, decode, decodeDevice, view,
      MmioModel.access, gpioWrite, txStart, rxConsume, clearErrors, selected, Expr.eval,
      hv, hd, hw, ht, hx]
    all_goals repeat' split
    all_goals simp_all

theorem txStart_busy (i : Values Input) (s : Values Register) (h : s txActiveReg = 1#1) :
    txStart.eval i s = 0 := by simp [txStart, Expr.eval, h]

theorem rxConsume_empty (i : Values Input) (s : Values Register) (h : s rxValidReg = 0#1) :
    rxConsume.eval i s = 0 := by simp [rxConsume, Expr.eval, h]

theorem rxRoom_eval (i : Values Input) (s : Values Register) :
    rxRoom.eval i s = BitVec.ofBool (cpuView i s).rx.isNone := by
  rcases BitVec.eq_zero_or_eq_one (s rxValidReg) with hx | hx
  · simp [rxRoom, cpuView, view, Expr.eval, hx, rxConsume_empty i s hx]
  · rcases BitVec.eq_zero_or_eq_one (rxConsume.eval i s) with hc | hc <;>
      simp [rxRoom, cpuView, view, Expr.eval, hx, hc]

theorem bit_value (b : BitVec 1) : BitVec.ofBool (b == 1) = b := by
  rcases BitVec.eq_zero_or_eq_one b with h | h <;> simp [h]

theorem slice_bit (x : BitVec w) (k : Nat) : x.extractLsb' k 1 = BitVec.ofBool (x.getLsbD k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hz : j = 0 := by omega
  subst j
  simp

theorem reset_eq (i : Values Input) (s : Values Register) (hr : i reset = 1#1) (r : Register b) :
    circuit.step i s r = 0 := by
  simp [Circuit.step, circuit, Expr.eval, hr]

theorem step_gpio (i : Values Input) (s : Values Register) (hr : i reset = 0#1) :
    (view (circuit.step i s)).gpioOut =
      (MmioModel.autonomous (decode i) (view s) (cpuView i s)).gpioOut := by
  simp [view, Circuit.step, circuit, gpio, Expr.eval, hr, MmioModel.autonomous, cpuView]

theorem step_timer (i : Values Input) (s : Values Register) (hr : i reset = 0#1) :
    (view (circuit.step i s)).timer =
      (MmioModel.autonomous (decode i) (view s) (cpuView i s)).timer := by
  simp [view, Circuit.step, circuit, timer, Expr.eval, hr, MmioModel.autonomous, cpuView, WordOps.add]
  simpa [timer] using (BitVec.sub_neg (x := s timer) (y := 1#32))

theorem step_tx (i : Values Input) (s : Values Register) (hr : i reset = 0#1) :
    (view (circuit.step i s)).tx =
      (MmioModel.autonomous (decode i) (view s) (cpuView i s)).tx := by
  rcases BitVec.eq_zero_or_eq_one (s txActiveReg) with ht | ht
  · rcases BitVec.eq_zero_or_eq_one (txStart.eval i s) with hs | hs <;>
      simp [view, Circuit.step, circuit, hr, MmioModel.autonomous, cpuView,
        MmioModel.completedTx, decode, Expr.eval, ht, hs, txActiveReg, txDataReg] at *
  · have hs := txStart_busy i s ht
    rcases BitVec.eq_zero_or_eq_one (i txComplete) with hc | hc <;>
      simp [view, Circuit.step, circuit, hr, MmioModel.autonomous, cpuView,
        MmioModel.completedTx, decode, Expr.eval, ht, hs, hc, txActiveReg, txDataReg] at *

theorem step_rx (i : Values Input) (s : Values Register) (hr : i reset = 0#1) :
    (view (circuit.step i s)).rx =
      (MmioModel.autonomous (decode i) (view s) (cpuView i s)).rx := by
  rcases BitVec.eq_zero_or_eq_one (s rxValidReg) with hx | hx
  · have hc := rxConsume_empty i s hx
    rcases BitVec.eq_zero_or_eq_one (i rxValid) with hi | hi <;>
      simp [view, Circuit.step, circuit, hr, MmioModel.autonomous, cpuView,
        MmioModel.receive, decode, rxCapture, rxRoom, Expr.eval, hx, hc, hi, rxValidReg, rxDataReg] at *
  · rcases BitVec.eq_zero_or_eq_one (rxConsume.eval i s) with hc | hc <;>
      rcases BitVec.eq_zero_or_eq_one (i rxValid) with hi | hi <;>
      simp [view, Circuit.step, circuit, hr, MmioModel.autonomous, cpuView,
        MmioModel.receive, decode, rxCapture, rxRoom, Expr.eval, hx, hc, hi, rxValidReg, rxDataReg] at *

theorem autonomous_overrun (i : MmioModel.Input) (before current : MmioModel.State) :
    (MmioModel.autonomous i before current).overrun =
      (current.overrun || (i.rxArrival.isSome && current.rx.isSome)) := by
  cases ha : i.rxArrival <;> cases hx : current.rx <;> simp [MmioModel.autonomous, MmioModel.receive, ha, hx]

theorem autonomous_framing (i : MmioModel.Input) (before current : MmioModel.State) :
    (MmioModel.autonomous i before current).framing = (current.framing || i.framingError) := by
  simp [MmioModel.autonomous]

theorem cpuView_overrun (i : Values Input) (s : Values Register) :
    (cpuView i s).overrun =
      ((s overrun == 1) && !((clearErrors.eval i s == 1) && (i data).getLsbD 2)) := rfl

theorem cpuView_framing (i : Values Input) (s : Values Register) :
    (cpuView i s).framing =
      ((s framing == 1) && !((clearErrors.eval i s == 1) && (i data).getLsbD 3)) := rfl

theorem overrun_next (i : Values Input) (s : Values Register) :
    circuit.step i s overrun = if i reset = 1#1 then 0 else
      ((s overrun &&& ~~~(clearErrors.eval i s &&& (i data).extractLsb' 2 1)) ||| rxOverflow.eval i s) := by
  simp [Circuit.step, circuit, overrun, Expr.eval]

theorem framing_next (i : Values Input) (s : Values Register) :
    circuit.step i s framing = if i reset = 1#1 then 0 else
      ((s framing &&& ~~~(clearErrors.eval i s &&& (i data).extractLsb' 3 1)) ||| i framingError) := by
  simp [Circuit.step, circuit, framing, Expr.eval]

theorem step_overrun (i : Values Input) (s : Values Register) (hr : i reset = 0#1) :
    (view (circuit.step i s)).overrun =
      (MmioModel.autonomous (decode i) (view s) (cpuView i s)).overrun := by
  change (circuit.step i s overrun == 1#1) = _
  rw [overrun_next, autonomous_overrun]
  rcases BitVec.eq_zero_or_eq_one (s overrun) with ho | ho
  all_goals rcases BitVec.eq_zero_or_eq_one (clearErrors.eval i s) with hc | hc
  all_goals rcases BitVec.eq_zero_or_eq_one (i rxValid) with hi | hi
  all_goals cases hb : (i data).getLsbD 2
  all_goals cases hx : (cpuView i s).rx
  all_goals have hb' := hb
  all_goals rw [BitVec.getLsbD_eq_getElem (by decide : 2 < 32)] at hb'
  all_goals simp [hr, rxOverflow, Expr.eval, slice_bit,
    rxRoom_eval, cpuView_overrun, decode, ho, hc, hi, hb', hx]

theorem step_framing (i : Values Input) (s : Values Register) (hr : i reset = 0#1) :
    (view (circuit.step i s)).framing =
      (MmioModel.autonomous (decode i) (view s) (cpuView i s)).framing := by
  change (circuit.step i s framing == 1#1) = _
  rw [framing_next, autonomous_framing]
  rcases BitVec.eq_zero_or_eq_one (s framing) with hf | hf
  all_goals rcases BitVec.eq_zero_or_eq_one (clearErrors.eval i s) with hc | hc
  all_goals rcases BitVec.eq_zero_or_eq_one (i framingError) with hi | hi
  all_goals cases hb : (i data).getLsbD 3
  all_goals have hb' := hb
  all_goals rw [BitVec.getLsbD_eq_getElem (by decide : 3 < 32)] at hb'
  all_goals simp [hr, slice_bit, cpuView_framing,
    decode, hf, hc, hi, hb']

theorem state_ext (s t : MmioModel.State)
    (hg : s.gpioOut = t.gpioOut) (ht : s.timer = t.timer) (hxt : s.tx = t.tx)
    (hxr : s.rx = t.rx) (ho : s.overrun = t.overrun) (hf : s.framing = t.framing) : s = t := by
  cases s
  cases t
  simp_all

theorem reset_view (i : Values Input) (s : Values Register) (hr : i reset = 1#1) :
    view (circuit.step i s) = MmioModel.initial := by
  simp [view, reset_eq i s hr, MmioModel.initial]

theorem view_step (i : Values Input) (s : Values Register) :
    view (circuit.step i s) = spec.step i (view s) := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  · change view (circuit.step i s) = MmioModel.step (decode i) (view s)
    have hd : (decode i).reset = false := by simp [decode, hr]
    rw [MmioModel.step, hd]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← cpuView_eq]
    exact state_ext _ _ (step_gpio i s hr) (step_timer i s hr) (step_tx i s hr)
      (step_rx i s hr) (step_overrun i s hr) (step_framing i s hr)
  · simp [reset_view i s hr, spec, MmioModel.step, decode, hr]

section OutputProofs
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem statusExpr_eval (i : Values Input) (s : Values Register) :
    statusExpr.eval i s = MmioModel.status (view s) := by
  rcases BitVec.eq_zero_or_eq_one (s txActiveReg) with ht | ht
  all_goals rcases BitVec.eq_zero_or_eq_one (s rxValidReg) with hr | hr
  all_goals rcases BitVec.eq_zero_or_eq_one (s overrun) with ho | ho
  all_goals rcases BitVec.eq_zero_or_eq_one (s framing) with hf | hf
  all_goals simp [statusExpr, Expr.eval, MmioModel.status, view, ht, hr, ho, hf]

def rawResponse (i : Values Input) (s : Values Register) : MmioModel.Response :=
  match decodeDevice (i device) with
  | none => .fault .registerHole
  | some d => (MmioModel.access (i gpioInput) ⟨d, i word, i write == 1, i data⟩ (view s)).1

theorem response_raw (i : Values Input) (s : Values Register) :
    response i (view s) = if i reset = 1 then none else if i requestValid = 1 then some (rawResponse i s) else none := by
  rcases device_cases (i device) with hd | hd | hd | hd
  all_goals rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  all_goals rcases BitVec.eq_zero_or_eq_one (i requestValid) with hv | hv
  all_goals simp [response, invalid, hr, hv, hd, MmioModel.observe, decode, decodeDevice, rawResponse]

theorem codeExpr_eval (i : Values Input) (s : Values Register) :
    codeExpr.eval i s = code (rawResponse i s) := by
  rcases device_cases (i device) with hd | hd | hd | hd
  all_goals rcases BitVec.eq_zero_or_eq_one (i write) with hw | hw
  all_goals rcases BitVec.eq_zero_or_eq_one (s txActiveReg) with ht | ht
  all_goals rcases BitVec.eq_zero_or_eq_one (s rxValidReg) with hr | hr
  all_goals by_cases h0 : i word = 0#6
  all_goals by_cases h1 : i word = 1#6
  all_goals by_cases h2 : i word = 2#6
  all_goals by_cases h3 : i word = 3#6
  all_goals simp [codeExpr, gpioCode, timerCode, uartCode, Expr.eval,
    rawResponse, decodeDevice, MmioModel.access, view, hd, hw, ht, hr, h0, h1, h2, h3, code]

theorem rxDataExtend (byte : BitVec 8) : (0#24) ++ byte = byte.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or, BitVec.toNat_setWidth]
  have hb := byte.isLt
  omega

theorem dataExpr_eval (i : Values Input) (s : Values Register) :
    (if codeExpr.eval i s = 0 then dataExpr.eval i s else 0) = payload (rawResponse i s) := by
  rw [codeExpr_eval]
  rcases device_cases (i device) with hd | hd | hd | hd
  all_goals rcases BitVec.eq_zero_or_eq_one (i write) with hw | hw
  all_goals rcases BitVec.eq_zero_or_eq_one (s txActiveReg) with ht | ht
  all_goals rcases BitVec.eq_zero_or_eq_one (s rxValidReg) with hr | hr
  all_goals by_cases h0 : i word = 0#6
  all_goals by_cases h1 : i word = 1#6
  all_goals by_cases h2 : i word = 2#6
  all_goals by_cases h3 : i word = 3#6
  all_goals simp [dataExpr, Expr.eval, statusExpr_eval,
    rawResponse, decodeDevice, MmioModel.access, view, hd, hw, ht, hr, h0, h1, h2, h3, code, payload, rxDataExtend]

theorem output_eq (i : Values Input) (s : Values Register) (o : Output b) :
    circuit.observe i s o = spec.observe i (view s) o := by
  match o with
  | .at ⟨0, _⟩ =>
    rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
    all_goals simp [Circuit.observe, circuit, Expr.eval, spec, outputValues, hr]
  | .at ⟨1, _⟩ =>
    rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
    all_goals rcases BitVec.eq_zero_or_eq_one (i requestValid) with hv | hv
    all_goals simp [Circuit.observe, circuit, active, Expr.eval, spec, outputValues, response_raw, hr, hv]
  | .at ⟨2, _⟩ =>
    rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
    all_goals rcases BitVec.eq_zero_or_eq_one (i requestValid) with hv | hv
    all_goals simp [Circuit.observe, circuit, active, Expr.eval, spec, outputValues, response_raw, hr, hv, codeExpr_eval]
  | .at ⟨3, _⟩ =>
    change circuit.observe i s responseData = spec.observe i (view s) responseData
    rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
    all_goals rcases BitVec.eq_zero_or_eq_one (i requestValid) with hv | hv
    all_goals simp [Circuit.observe, circuit, active, Expr.eval, spec, outputValues, responseData, response_raw, hr, hv]
    all_goals try rfl
    have he := dataExpr_eval i s
    by_cases hc : codeExpr.eval i s = 0#3
    all_goals simp [hc] at he ⊢
    all_goals exact he
  | .at ⟨4, _⟩ =>
    simp [Circuit.observe, circuit, Expr.eval, spec, outputValues, view]
  | .at ⟨5, _⟩ =>
    change circuit.observe i s txActive = spec.observe i (view s) txActive
    rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
    all_goals rcases BitVec.eq_zero_or_eq_one (s txActiveReg) with ht | ht
    all_goals simp [Circuit.observe, circuit, Expr.eval, spec, outputValues, txActive, view, hr, ht]
    all_goals rfl
  | .at ⟨6, _⟩ =>
    change circuit.observe i s txData = spec.observe i (view s) txData
    rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
    all_goals rcases BitVec.eq_zero_or_eq_one (s txActiveReg) with ht | ht
    all_goals simp [Circuit.observe, circuit, Expr.eval, spec, outputValues, txData, view, hr, ht]
    all_goals rfl
  | .at ⟨k+7, h⟩ => exact False.elim (by change k+7 < 7 at h; omega)

end OutputProofs

def implementation : DecodedImplementation circuit spec where
  Valid _ := True
  view := view
  preserved _ _ _ := trivial
  step_eq i s _ := view_step i s
  output_eq i s _ _ o := output_eq i s o

def resetCertificate : implementation.Reset reset where
  initial _ := MmioModel.initial
  reset_valid _ _ _ := trivial
  reset_view i s h := reset_view i s h

theorem trace_correct (s : Values Register) (traffic : List (Values Input)) :
    circuit.component.trace s traffic = spec.trace (view s) traffic :=
  implementation.trace_eq s trivial traffic

theorem run_correct (s : Values Register) (traffic : List (Values Input)) :
    view (circuit.component.run s traffic) = spec.run (view s) traffic :=
  implementation.run_eq s trivial traffic

theorem reset_outputs (i : Values Input) (s : Values Register) (hr : i reset = 1#1) (o : Output b) :
    circuit.observe i s o = 0 := by
  rw [output_eq]
  match o with
  | .at ⟨0, _⟩ | .at ⟨1, _⟩ | .at ⟨2, _⟩ | .at ⟨3, _⟩ |
    .at ⟨4, _⟩ | .at ⟨5, _⟩ | .at ⟨6, _⟩ => simp [spec, outputValues, response, hr] <;> rfl
  | .at ⟨k+7, h⟩ => exact False.elim (by change k+7 < 7 at h; omega)

theorem invalid_iff_device3 (i : Values Input) :
    invalid i ↔ i requestValid = 1#1 ∧ i device = 3#2 := by
  rcases device_cases (i device) with hd | hd | hd | hd <;> simp [invalid, decodeDevice, hd]

def decodeResponse (code : BitVec 3) (data : BitVec 32) : Option MmioModel.Response :=
  if code = 0 then some (.read data) else if code = 1 then some .stored
  else if code = 2 then some (.fault .registerHole) else if code = 3 then some (.fault .direction)
  else if code = 4 then some (.fault .txBusy) else if code = 5 then some (.fault .rxEmpty) else none

@[simp] theorem decodeResponse_code (r : MmioModel.Response) :
    decodeResponse (code r) (payload r) = some r := by
  cases r with
  | read value => rfl
  | stored => rfl
  | fault reason => cases reason <;> rfl

/-- Decode actual physical response pins, including a malformed selector's
registerHole response. Unused physical response codes are rejected. -/
def observedResponse (i : Values Input) (s : Values Register) : Option MmioModel.Response :=
  if circuit.observe i s responseValid = 1 then
    decodeResponse (circuit.observe i s responseCode) (circuit.observe i s responseData)
  else none

theorem observedResponse_eq (i : Values Input) (s : Values Register) :
    observedResponse i s = response i (view s) := by
  simp only [observedResponse, output_eq]
  change (if BitVec.ofBool (response i (view s)).isSome = 1#1 then
    decodeResponse (((response i (view s)).map code).getD 0)
      (((response i (view s)).map payload).getD 0) else none) = _
  cases h : response i (view s) <;> simp

/-- Fixed actual-response extraction. Its transport theorem explicitly requires
Admitted: raw selector3 is covered by the wrapper, not aliased to a model request. -/
def physicalEvents (i : Values Input) (s : Values Register) : List MmioModel.Event :=
  if (decode i).reset then [.reset] else
    (decode i).operation.toList.map (fun r => .cpu r (i gpioInput)
      ((observedResponse i s).getD (.fault .registerHole))) ++
    MmioModel.autonomousEvents (decode i) (view s) (MmioModel.cpuState (decode i) (view s))

theorem physicalEvents_eq (i : Values Input) (s : Values Register) (hi : Admitted i) :
    physicalEvents i s = MmioModel.events (decode i) (view s) := by
  rw [physicalEvents, observedResponse_eq, response_admitted i (view s) hi]
  cases hr : (decode i).reset <;> cases ho : (decode i).operation <;>
    simp [MmioModel.events, MmioModel.observe, hr, ho]
  rfl

def eventRefinement : Timed.EventRefinement circuit.component MmioModel.eventSpec
    physicalEvents (fun i _ => Admitted i) where
  Rel raw logical := view raw = logical
  edge i s a related hi := by
    subst a
    refine ⟨view (circuit.step i s), ?_, rfl⟩
    rw [physicalEvents_eq i s hi, view_step]
    exact MmioModel.replay_path (MmioModel.replay_events (decode i) (view s))

theorem event_coverage : eventRefinement.InitialCoverage (fun _ => True) (fun _ => True) where
  nonempty := ⟨encode MmioModel.initial, trivial⟩
  covered s _ := ⟨view s, trivial, rfl⟩

theorem replay_of_path {s t : MmioModel.State} {es : List MmioModel.Event}
    (h : MmioModel.eventSpec.Path s es t) : MmioModel.replay s es = some t := by
  induction h with
  | nil => rfl
  | cons edge path ih => simp [MmioModel.eventSpec] at edge; simp [MmioModel.replay, edge, ih]

theorem event_replay_history (s : Values Register) (traffic : List (Values Input))
    (legal : circuit.component.Legal (fun i _ => Admitted i) s traffic) :
    MmioModel.replay (view s) (circuit.component.eventTrace physicalEvents s traffic) =
      some (view (circuit.component.run s traffic)) := by
  obtain ⟨last, path, related⟩ := eventRefinement.trace s (view s) traffic rfl legal
  have result := replay_of_path path
  change view (circuit.component.run s traffic) = last at related
  simpa [related] using result

end Pinwheel.Hardware.Processor.MmioCircuit
