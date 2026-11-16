import Pinwheel.Hardware.USB.Pins

namespace Pinwheel.Hardware.USB
open Pinwheel.Hardware Pinwheel.USBPacketFeasibility Pinwheel.USBClockFeasibility
open Pinwheel.USBOnlineFeasibility Pinwheel.USBWaveformConstruction

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- Each input is a quiet quad-host edge. The sample is the value read by the
    actual two-register sampler, before the circuit's next state. -/
inductive Transcript : CoreState → List Wire → CoreState → Prop where
  | nil (s : CoreState) : Transcript s [] s
  | cons (i : Values Input) (quiet : Quiet i) (seen : s (.base .stage2) = wireCode w)
      (tail : Transcript (circuit.step i s) ws finish) : Transcript s (w :: ws) finish

theorem Transcript.cut (front : List Wire) {back : List Wire}
    (trace : Transcript s (front ++ back) e) :
    ∃ mid : CoreState, Transcript s front mid ∧ Transcript mid back e := by
  induction front generalizing s with
  | nil => exact ⟨s,.nil _,trace⟩
  | cons w front ih =>
    cases trace with
    | cons i quiet seen tail =>
      obtain ⟨mid,checked,after⟩ := ih tail
      exact ⟨mid,.cons i quiet seen checked,after⟩

theorem Transcript.empty_end (t : Transcript s [] e) : Eq (α := CoreState) e s := by
  cases t
  rfl

theorem register_eq {s e : CoreState} (same : Eq (α := CoreState) s e) (r : Register w) :
    s r = e r := congrArg (fun state : CoreState => state r) same

theorem Transcript.single (t : Transcript s [w] e) :
    ∃ i : Values Input, Quiet i ∧ s (.base .stage2) = wireCode w ∧
      Eq (α := CoreState) e (circuit.step i s) := by
  cases t with
  | cons i q seen tail =>
    exact ⟨i,q,seen,tail.empty_end⟩

def readWire (pins : BitVec 2) : Wire :=
  if pins = 0 then .se0 else if pins = 1 then .k else if pins = 2 then .j else .se1

theorem readWire_code (pins : BitVec 2) : wireCode (readWire pins) = pins := by
  by_cases z : pins = 0#2
  · subst pins; rfl
  by_cases k : pins = 1#2
  · subst pins; rfl
  by_cases j : pins = 2#2
  · subst pins; rfl
  have e : pins = 3#2 := by
    have zNat : pins.toNat ≠ 0 := fun h => z ((isNat pins 0 (by decide)).mpr h)
    have kNat : pins.toNat ≠ 1 := fun h => k ((isNat pins 1 (by decide)).mpr h)
    have jNat : pins.toNat ≠ 2 := fun h => j ((isNat pins 2 (by decide)).mpr h)
    have width : pins.toNat < 4 := pins.isLt
    exact (isNat pins 3 (by decide)).mpr (by omega)
  subst pins
  rfl

theorem wireCode_readWire (w : Wire) : readWire (wireCode w) = w := by cases w <;> rfl

theorem raw_quiet (raw : Wire) : Quiet (idleWithRaw raw) := ⟨rfl,rfl⟩

def rawRun (s : CoreState) : List Wire → CoreState
  | [] => fun r => s r
  | sample :: rest => rawRun (circuit.step (idleWithRaw sample) s) rest

theorem physical_transcript (s : CoreState) (raw : List Wire) :
    Transcript s
      ((readWire (s (.base .stage2)) :: readWire (s (.base .stage1)) :: raw).take raw.length)
      (rawRun s raw) := by
  induction raw generalizing s with
  | nil => exact .nil s
  | cons wire raw ih =>
    let i : Values Input := idleWithRaw wire
    let n : CoreState := circuit.step i s
    have q := raw_quiet wire
    have stages := two_stage i s q
    have current1 : n (.base .stage1) = wireCode wire := stages.1
    have current2 : n (.base .stage2) = s (.base .stage1) := stages.2
    have later := ih n
    rw [current2,current1,wireCode_readWire] at later
    exact .cons i q (readWire_code _).symm later

theorem live_wait (n : Nat) (trace : Transcript s (List.replicate n .j) e)
    (h : Live s 1) (beforeTimeout : (s .age).toNat+n ≤ 127) :
    Live e 1 ∧ getCapture e = getCapture s ∧ (e .age).toNat = (s .age).toNat+n := by
  induction n generalizing s with
  | zero =>
    cases trace
    exact ⟨h,rfl,by simp⟩
  | succ n ih =>
    rw [List.replicate_succ] at trace
    cases trace with
    | @cons s _ _ _ i quiet seen tail =>
      try dsimp only at *
      obtain ⟨busy,same⟩ := waiting_idle i s quiet h seen (by omega)
      have age := eval_age_live i s quiet h.busy (h.active (by decide)) (by omega)
      obtain ⟨last,cap,clocks⟩ := ih tail busy (by rw [age]; omega)
      rw [age] at clocks
      exact ⟨last,cap.trans same,by omega⟩

def CaptureBound (c : Capture) : Prop := c.decoder.ones ≤ 6 ∧ c.decoder.logical.consumed ≤ 97

theorem captured_bounds (c next : Capture) (bit : Bool) (bounded : CaptureBound c)
    (capture : sampleOnTick c bit = some next) : CaptureBound next := by
  unfold sampleOnTick tick at capture
  split at capture
  · simp at capture
    subst next
    exact bounded
  · split at capture
    · simp only [List.foldlM_cons,List.foldlM_nil] at capture
      unfold ingestSymbol at capture
      dsimp only at capture
      split at capture
      · split at capture
        · contradiction
        · simp at capture
          subst next
          exact ⟨Nat.zero_le _,bounded.2⟩
      · simp at capture
        subst next
        simp only [CaptureBound, ingestLogical]
        constructor
        · have bounds := bounded.1
          split <;> omega
        · exact Nat.min_le_left ..
    · simp at capture
      subst next
      exact bounded

theorem receive_body (tape : List Bool) (trace : Transcript s (tape.map asWire) e)
    (h : Live s 2) (beforeDeadline : (s .age).toNat+tape.length ≤ 2047)
    (bounded : CaptureBound (getCapture s)) (cap : Capture)
    (accepted : tape.foldlM sampleOnTick (getCapture s) = some cap) :
    Live e 2 ∧ getCapture e = cap ∧ (e .age).toNat = (s .age).toNat+tape.length := by
  induction tape generalizing s with
  | nil =>
    cases trace
    exact ⟨h,Option.some.inj accepted,by simp⟩
  | cons bit rest ih =>
    cases trace with
    | @cons s _ _ _ i quiet seen tr =>
      try dsimp only at *
      have raw : s (.base .stage2) = (if bit then 1 else 2) := by
        cases bit <;> exact seen
      have clock := eval_age_live i s quiet h.busy (h.active (by decide)) (by simp at beforeDeadline; omega)
      cases parsed : sampleOnTick (getCapture s) bit with
      | none => simp [parsed] at accepted
      | some mid =>
        have ⟨listen,capMatch⟩ := pulse_data_step i s quiet (Or.inr rfl) h bit raw
          (by intro h; exact False.elim ((show (2 : BitVec 3) ≠ 1 by decide) h))
          (by simp at beforeDeadline; omega) bounded.1 bounded.2 mid parsed
        have before : ((circuit.step i s) .age).toNat+rest.length ≤ 2047 := by
          simp at beforeDeadline
          rw [clock]
          omega
        have nextBound := captured_bounds (getCapture s) mid bit bounded parsed
        have remaining : rest.foldlM sampleOnTick (getCapture (circuit.step i s)) = some cap := by
          simpa [parsed,capMatch] using accepted
        have ⟨last,bytes,clocks⟩ := ih tr listen before (by rw [capMatch]; exact nextBound) remaining
        rw [clock] at clocks
        exact ⟨last,bytes,by simp; omega⟩

theorem start_body (tape : List Bool) (trace : Transcript s (tape.map asWire) e)
    (h : Live s 1) (firstK : ∃ rest, tape = true :: rest)
    (beforeDeadline : (s .age).toNat+tape.length ≤ 2047)
    (fresh : getCapture s = {}) (cap : Capture)
    (accepted : tape.foldlM sampleOnTick {} = some cap) :
    Live e 2 ∧ getCapture e = cap ∧ (e .age).toNat = (s .age).toNat+tape.length := by
  obtain ⟨rest,rfl⟩ := firstK
  cases trace with
  | @cons s _ _ _ i quiet seen tail =>
    try dsimp only at *
    have early : (s .age).toNat < 2047 := by simp at beforeDeadline; omega
    have parse : sampleOnTick (getCapture s) true = some ⟨⟨true,7⟩,{}⟩ := by
      rw [fresh]
      rfl
    have bounded : CaptureBound (getCapture s) := by rw [fresh]; exact ⟨by decide,by decide⟩
    have ⟨onWire,capNext⟩ := pulse_data_step i s quiet (Or.inl rfl) h true seen
      (by intro _; rfl) early bounded.1 bounded.2 _ parse
    have age := eval_age_live i s quiet h.busy (h.active (by decide)) (by omega)
    have before : ((circuit.step i s) .age).toNat+rest.length ≤ 2047 := by
      simp at beforeDeadline
      rw [age]
      omega
    have remaining : rest.foldlM sampleOnTick (getCapture (circuit.step i s)) = some cap := by
      rw [capNext]
      change (sampleOnTick ({} : Capture) true).bind (fun cap => rest.foldlM sampleOnTick cap) = some cap at accepted
      rw [show sampleOnTick ({} : Capture) true = some ⟨⟨true,7⟩,{}⟩ by rfl] at accepted
      exact accepted
    have bounds := captured_bounds (getCapture s) _ true bounded parse
    have ⟨last,found,clocks⟩ := receive_body rest tail onWire before
      (by rw [capNext]; exact bounds) cap remaining
    rw [age] at clocks
    exact ⟨last,found,by simp; omega⟩

theorem count_more_marker (n : Nat) (trace : Transcript s (List.replicate n .se0) e)
    (h : Live s 3) (within : (s .timer).toNat+n ≤ 33) (budget : (s .age).toNat+n ≤ 2047) :
    Live e 3 ∧ getCapture e = getCapture s ∧
      (e .timer).toNat = (s .timer).toNat+n ∧ (e .age).toNat = (s .age).toNat+n := by
  induction n generalizing s with
  | zero => cases trace; exact ⟨h,rfl,by simp,by simp⟩
  | succ n ih =>
    rw [List.replicate_succ] at trace
    cases trace with
    | @cons s _ _ _ i quiet seen tail =>
      try dsimp only at *
      have ⟨marker,same,w⟩ := marker_clock i s quiet (Or.inr rfl) h seen (by omega) (by intro _; omega)
      have age := eval_age_live i s quiet h.busy (h.active (by decide)) (by omega)
      have width : ((circuit.step i s) .timer).toNat = (s .timer).toNat+1 := by
        simpa only [if_neg (show (3 : BitVec 3) ≠ 2 by decide)] using w
      have ⟨last,cap,clocks,elapsed⟩ := ih tail marker (by rw [width]; omega) (by rw [age]; omega)
      rw [width] at clocks
      rw [age] at elapsed
      exact ⟨last,cap.trans same,by omega,by omega⟩

theorem count_marker (width : Nat) (trace : Transcript s (List.replicate width .se0) e)
    (h : Live s 2) (legal : 0 < width ∧ width ≤ 33) (budget : (s .age).toNat+width ≤ 2047) :
    Live e 3 ∧ getCapture e = getCapture s ∧
      (e .timer).toNat = width ∧ (e .age).toNat = (s .age).toNat+width := by
  cases width with
  | zero => omega
  | succ n =>
    rw [List.replicate_succ] at trace
    cases trace with
    | @cons s _ _ _ i quiet seen tail =>
      try dsimp only at *
      have ⟨marker,same,w⟩ := marker_clock i s quiet (Or.inl rfl) h seen (by omega)
        (by intro e; exact False.elim ((show (2 : BitVec 3) ≠ 3 by decide) e))
      have age := eval_age_live i s quiet h.busy (h.active (by decide)) (by omega)
      have width : ((circuit.step i s) .timer).toNat = 1 := by simpa using w
      have ⟨last,cap,clocks,elapsed⟩ := count_more_marker n tail marker
        (by rw [width]; omega) (by rw [age]; omega)
      rw [width] at clocks
      rw [age] at elapsed
      exact ⟨last,cap.trans same,by omega,by omega⟩

theorem send_after_delay (tape : List Wire) (trace : Transcript s tape e)
    (h : Live s 4) (ticks : (s .timer).toNat = tape.length) (nonempty : 0 < tape.length)
    (budget : (s .age).toNat+tape.length ≤ 2047) :
    Live e 5 ∧ getCapture e = getCapture s ∧ (e .timer).toNat = 304 := by
  induction tape generalizing s with
  | nil => simp at nonempty
  | cons w rest ih =>
    cases trace with
    | @cons s _ _ _ i quiet _ tail =>
      try dsimp only at *
      have earlier : (s .age).toNat < 2047 := by simp at budget; omega
      have step := wait_to_ack i s quiet h earlier (by omega)
      cases rest with
      | nil =>
        have same := tail.empty_end
        simp only [same,register_eq same]
        have last : (s .timer).toNat = 1 := by simpa using ticks
        simpa [last] using step
      | cons v rest =>
        have more : (s .timer).toNat ≠ 1 := by simp at ticks; omega
        simp only [more,if_false] at step
        have age := eval_age_live i s quiet h.busy (h.active (by decide)) (by omega)
        have len : ((circuit.step i s) .timer).toNat = (v::rest).length := by
          have counter := step.2.2
          simp at ticks ⊢
          omega
        have enough : ((circuit.step i s) .age).toNat+(v::rest).length ≤ 2047 := by
          simp at budget ⊢
          rw [age]
          omega
        have ⟨last,cap,timer⟩ := ih tail step.1 len (by simp) enough
        exact ⟨last,cap.trans step.2.1,timer⟩

theorem keep_ack_flight (tape : List Wire) (trace : Transcript s tape e)
    (h : Live s 5) (beforeEnd : tape.length < (s .timer).toNat) :
    Live e 5 ∧ getCapture e = getCapture s ∧ (e .timer).toNat = (s .timer).toNat-tape.length := by
  induction tape generalizing s with
  | nil => cases trace; exact ⟨h,rfl,by simp⟩
  | cons w rest ih =>
    cases trace with
    | @cons s _ _ _ i quiet _ tail =>
      try dsimp only at *
      have ⟨onWire,cap,timer⟩ := ack_tick i s quiet h (by simp at beforeEnd; omega)
      have ⟨last,bytes,clock⟩ := ih tail onWire (by simp at beforeEnd; rw [timer]; omega)
      rw [timer] at clock
      exact ⟨last,bytes.trans cap,by simp; omega⟩

theorem complete_ack_flight (tape : List Wire) (trace : Transcript s tape e)
    (h : Live s 5) (ticks : tape.length = (s .timer).toNat) (nonempty : 0 < tape.length) :
    e (.base .phase) = 5 ∧ e .mode = 0 ∧ e (.base .rxCount) = 2 ∧ e (.base .rxProduced) = 64 ∧
    e (.base (.rxWord 0#1)) = s (.base (.rxWord 0#1)) ∧
    e (.base (.rxWord 1#1)) = s (.base (.rxWord 1#1)) := by
  induction tape generalizing s with
  | nil => simp at nonempty
  | cons w rest ih =>
    cases trace with
    | @cons s _ _ _ i quiet _ tail =>
      try dsimp only at *
      cases rest with
      | nil =>
        have same := tail.empty_end
        simp only [register_eq same]
        have last : (s .timer).toNat ≤ 1 := by simp at ticks; omega
        have result := publish_after_final_ack i s quiet h.busy h.state last
        exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,result.2.2.2.2.2⟩
      | cons v rest =>
        have ⟨onWire,cap,timer⟩ := ack_tick i s quiet h (by simp at ticks; omega)
        have count : (v::rest).length = ((circuit.step i s) .timer).toNat := by
          rw [timer]
          simp at ticks ⊢
          omega
        have ⟨phase,mode,n,produced,first,second⟩ := ih tail onWire count (by simp)
        exact ⟨phase,mode,n,produced,
          first.trans (congrArg (fun c : Capture => c.decoder.logical.payloadFirst) cap),
          second.trans (congrArg (fun c : Capture => c.decoder.logical.payloadSecond) cap)⟩

/-- Agreement at the actual circuit's receive entry, first driven ACK edge,
    and retained output. The two words stay unobservable at ACK start. -/
theorem complete_sampled_transaction (payload body : List Bool) (idle width : Nat)
    (delay flight : List Wire) (s e : CoreState)
    (h : Live s 1) (fresh : getCapture s = {}) (ageZero : (s .age).toNat = 0)
    (payloadSize : payload.length = 64) (firstK : ∃ rest, body = true :: rest)
    (samples : (sampleTrace {} body).2 = emitNRZI false (insertStuff (canonicalDATA1 payload) 0))
    (starts : idle ≤ 127) (legalMarker : 31 ≤ width ∧ width ≤ 33)
    (budget : idle + body.length + width + 1 + 46 ≤ 2047)
    (gap : delay.length = 46) (ackLength : flight.length = 304)
    (trace : Transcript s ((List.replicate idle .j ++ body.map asWire) ++
      ((List.replicate width .se0 ++ [.j]) ++ delay) ++ flight) e) :
    ∃ ack : CoreState, ∃ words : Pair,
      Transcript s ((List.replicate idle .j ++ body.map asWire) ++
        ((List.replicate width .se0 ++ [.j]) ++ delay)) ack ∧
      Transcript ack flight e ∧
      Live ack 5 ∧ (ack .timer).toNat = 304 ∧
      e (.base .phase) = 5 ∧ e .mode = 0 ∧ e (.base .rxCount) = 2 ∧
      e (.base .rxProduced) = 64 ∧ e (.base (.rxWord 0#1)) = words.first ∧
      e (.base (.rxWord 1#1)) = words.second ∧
      decodeWord words.first 32 ++ decodeWord words.second 32 = payload := by
  obtain ⟨c,words,decoded,valid,bytes⟩ := sampled_canonical_payload body payload payloadSize samples
  have fieldWords : ⟨c.decoder.logical.payloadFirst,c.decoder.logical.payloadSecond⟩ = words := by
    unfold verifyFrame at valid
    cases done : finishSymbols c.decoder with
    | none => simp [done] at valid
    | some registers =>
      have fields : registers = c.decoder.logical := by
        unfold finishSymbols at done
        split at done
        · contradiction
        · exact (Option.some.inj done).symm
      simp only [done] at valid
      rw [fields] at valid
      split at valid <;> try contradiction
      split at valid <;> try contradiction
      split at valid <;> try contradiction
      split at valid <;> try contradiction
      split at valid <;> try contradiction
      exact Verdict.data.inj valid
  obtain ⟨ack,head,endFlight⟩ := trace.cut _
  obtain ⟨afterData,beforeMark,afterMark⟩ := head.cut _
  obtain ⟨ready,firstWait,raw⟩ := beforeMark.cut _
  obtain ⟨eop,throughMarker,waitAck⟩ := afterMark.cut _
  obtain ⟨preJ,held,lastJ⟩ := throughMarker.cut _
  have ⟨listening,clock,elapsed⟩ := live_wait idle firstWait h (by omega)
  have ⟨reading,readCap,readTime⟩ :=
    start_body body raw listening firstK (by omega) (clock.trans fresh) c decoded
  have ⟨marker,markCap,markWidth,markTime⟩ :=
    count_marker width held reading (by omega) (by omega)
  have armed : Live eop 4 ∧ getCapture eop = c ∧ (eop .timer).toNat = 46 ∧
      (eop .age).toNat = idle+body.length+width+1 := by
    obtain ⟨i,q,seen,eqStep⟩ := lastJ.single
    simp only [eqStep,register_eq eqStep]
    have saved : getCapture preJ = c := markCap.trans readCap
    have check : verifyFrame (getCapture preJ) = .data words := by rw [saved]; exact valid
    have ⟨active,frame,timer⟩ := arm_ack i preJ q marker seen
      (by omega) (by omega) (by omega) ⟨words,check⟩
    have latest := eval_age_live i preJ q marker.busy (marker.active (by decide)) (by omega)
    exact ⟨active,frame.trans saved,timer,by rw [latest]; omega⟩
  have ⟨sending,packet,timer⟩ :=
    send_after_delay delay waitAck armed.1 (armed.2.2.1.trans gap.symm) (by omega) (by omega)
  have ⟨complete,off,two,published,firstWord,secondWord⟩ :=
    complete_ack_flight flight endFlight sending (ackLength.trans timer.symm) (by omega)
  have atAck : getCapture ack = c := packet.trans armed.2.1
  have first := congrArg Pair.first fieldWords
  have second := congrArg Pair.second fieldWords
  have firstAck : ack (.base (.rxWord 0#1)) = words.first :=
    (congrArg (fun v : Capture => v.decoder.logical.payloadFirst) atAck).trans first
  have secondAck : ack (.base (.rxWord 1#1)) = words.second :=
    (congrArg (fun v : Capture => v.decoder.logical.payloadSecond) atAck).trans second
  exact ⟨ack,words,head,endFlight,sending,timer,complete,off,two,published,
    firstWord.trans firstAck,secondWord.trans secondAck,bytes⟩

theorem ack_prefix_pins (i : Values Input) (tape : List Wire) (trace : Transcript s tape e)
    (ack : Live s 5) (full : (s .timer).toNat = 304) (before : tape.length < 304) :
    circuit.observe i e .enabled = 3 ∧ circuit.observe i e .levels =
      BitVec.ofNat 3 (padValue (ackClocks[tape.length]'(by rw [ack_clock_count]; exact before))) := by
  have ⟨flight,_,left⟩ := keep_ack_flight tape trace ack (by omega)
  have h := ack_pins i e flight.state (by omega) (by omega)
  have index : 304-(e .timer).toNat = tape.length := by omega
  simpa [index] using h

def dataSamples (rate : PeerRate) (sop : Int) (offset : Nat) (payload : List Bool) : List Wire :=
  let runs := dataRuns payload
  let markerAt := advanceTime rate sop (wireCells runs)
  let j := advanceTime rate markerAt 2
  let idle := (ceilTick sop rate.den).toNat+2-offset
  let tape := clockTape (digitizeRuns rate sop runs)
  let width := clockSpan markerAt j rate.den
  (List.replicate idle .j ++ tape.map asWire) ++
    ((List.replicate width .se0 ++ [.j]) ++ List.replicate 46 .j)

/-- The offset counts clocks of the IN prefix already elapsed at receiver
    entry, relative to its return to J. Entry precedes peer SOP. The ACK
    edge in the same coordinate system is the raw sampled J edge plus 48. -/
theorem clocked_transaction (rate : PeerRate) (sop : Int) (nonnegative : 0 ≤ sop)
    (timely : 2*sop ≤ 15*rate.period) (offset : Nat) (opened : offset ≤ (ceilTick sop rate.den).toNat)
    (payload : List Bool) (payloadSize : payload.length = 64) (s e : CoreState)
    (h : Live s 1) (fresh : getCapture s = {}) (ageZero : (s .age).toNat = 0)
    (flight : List Wire) (flightClocks : flight.length = 304)
    (trace : Transcript s (dataSamples rate sop offset payload ++ flight) e) :
    let runs := dataRuns payload
    let j := advanceTime rate (advanceTime rate sop (wireCells runs)) 2
    let rawJ := (ceilTick j rate.den).toNat
    (dataSamples rate sop offset payload).length + offset = rawJ+49 ∧
    ∃ ack : CoreState, ∃ words : Pair,
      Transcript s (dataSamples rate sop offset payload) ack ∧
      Transcript ack flight e ∧
      Live ack 5 ∧ (ack .timer).toNat = 304 ∧
      e (.base .phase) = 5 ∧ e .mode = 0 ∧ e (.base .rxCount) = 2 ∧
      e (.base .rxProduced) = 64 ∧ e (.base (.rxWord 0#1)) = words.first ∧
      e (.base (.rxWord 1#1)) = words.second ∧
      decodeWord words.first 32 ++ decodeWord words.second 32 = payload := by
  let runs := dataRuns payload
  let markerAt := advanceTime rate sop (wireCells runs)
  let j := advanceTime rate markerAt 2
  let rawJ := (ceilTick j rate.den).toNat
  let idle := (ceilTick sop rate.den).toNat+2-offset
  let tape := clockTape (digitizeRuns rate sop runs)
  let width := clockSpan markerAt j rate.den
  have clocks : idle ≤ 124 ∧ rawJ+48 ≤ 2022 := by
    have limits := measured_canonical_deadline rate sop nonnegative timely payload payloadSize
    dsimp only at limits
    change (ceilTick sop rate.den).toNat+2 ≤ 124 ∧ rawJ+48 ≤ 2022 at limits
    change (ceilTick sop rate.den).toNat+2-offset ≤ 124 ∧ rawJ+48 ≤ 2022
    omega
  have a := advanceTime_ordered rate sop (wireCells runs)
  have b := advanceTime_ordered rate markerAt 2
  have spanOk : tape.length + width = clockSpan sop j rate.den := by
    change (clockTape (digitizeRuns rate sop runs)).length + clockSpan markerAt j rate.den = _
    rw [digitized_clock_length]
    exact ceilSpan_add sop markerAt j rate.den rate.positive a b
  have absOk : (ceilTick sop rate.den).toNat + clockSpan sop j rate.den = rawJ :=
    relative_clocks_add_absolute sop j rate nonnegative (Int.le_trans a b)
  have anchor : idle+tape.length+width+1+46+offset = rawJ+49 := by
    change (ceilTick sop rate.den).toNat+2-offset+tape.length+width+1+46+offset = rawJ+49
    omega
  have markerSpan : j-markerAt = 2*rate.period := by
    change markerAt + (2 : Int)*rate.period - markerAt = _
    omega
  obtain ⟨off,early,late,lo,hi⟩ := span_rounded markerAt j rate.den rate.positive b
  rw [markerSpan] at lo hi
  have framing := end_marker_quantized rate width off early late lo hi
  have sequence := symbolic_trace_measured rate sop runs false (all_data_runs_legal payload)
  have recovered : (sampleTrace {} tape).2 = emitNRZI false (insertStuff (canonicalDATA1 payload) 0) :=
    (sample_runs_exact _ {} (trace_of_rate rate _ _ sequence)).trans
      ((digitize_preserves_bits rate sop runs).trans (data_runs_exact payload))
  refine ⟨?_,?_⟩
  · change (dataSamples rate sop offset payload).length+offset = rawJ+49
    simp only [dataSamples,List.length_append,List.length_replicate,List.length_map,
      List.length_cons,List.length_nil]
    change idle+tape.length+(width+(0+1)+46)+offset = _
    omega
  · exact complete_sampled_transaction payload tape idle width (List.replicate 46 .j)
      flight s e h fresh ageZero payloadSize (data_tape_begins_k rate sop payload)
      recovered (by omega) framing (by omega) List.length_replicate flightClocks trace

theorem selected_receiver_timing (rate : PeerRate) (sop : Int)
    (offset : Nat) (opened : offset ≤ (ceilTick sop rate.den).toNat)
    (payload : List Bool) :
    (dataSamples rate sop offset payload).take 2 = [.j,.j] := by
  have enough : 2 ≤ (ceilTick sop rate.den).toNat+2-offset := by omega
  have prefixLen : 2 ≤ (List.replicate ((ceilTick sop rate.den).toNat+2-offset) Wire.j).length := by
    simpa using enough
  unfold dataSamples
  rw [List.append_assoc, List.take_append_of_le_length prefixLen]
  simp [List.take_replicate, Nat.min_eq_left enough]

theorem recorded_clocked_transcript (rate : PeerRate) (sop : Int)
    (offset : Nat) (opened : offset ≤ (ceilTick sop rate.den).toNat)
    (payload : List Bool) (s : CoreState) (flight : List Wire)
    (stage1 : s (.base .stage1) = wireCode .j) (stage2 : s (.base .stage2) = wireCode .j)
    (tail : List Wire) (tailClocks : tail.length = 2) :
    let tape := dataSamples rate sop offset payload ++ flight
    Transcript s tape (rawRun s (tape.drop 2 ++ tail)) := by
  let pre := dataSamples rate sop offset payload
  let tape := pre ++ flight
  have first := selected_receiver_timing rate sop offset opened payload
  have room : 2 ≤ pre.length := by
    have length := congrArg List.length first
    simp [pre,List.length_take] at *
    omega
  have initial : tape.take 2 = [.j,.j] := by
    unfold tape
    rwa [List.take_append_of_le_length room]
  have readBack : [.j,.j] ++ tape.drop 2 = tape := by
    rw [← initial,List.take_append_drop]
  have total : (tape.drop 2 ++ tail).length = tape.length := by
    have all : 2 ≤ tape.length := by simp [tape]; omega
    simp only [List.length_append,List.length_drop,tailClocks]
    omega
  have trace := physical_transcript s (tape.drop 2 ++ tail)
  rw [stage1,stage2,wireCode_readWire] at trace
  change Transcript s (([Wire.j,Wire.j] ++ tape.drop 2 ++ tail).take (tape.drop 2 ++ tail).length)
    (rawRun s (tape.drop 2 ++ tail)) at trace
  rw [total,readBack,List.take_append_length] at trace
  exact trace

/-- Receive dispatch uses the fetched word checked by `installed_receiver`.
    The IN prefix ends with sixteen driven J clocks, followed by the fetch
    edge that releases the pins. The first receive edge has offset seventeen. -/
theorem fetched_in_read (i : Values Input) (s : CoreState) (quiet : Quiet i)
    (selected : entering.eval i s = 1#1) (idle : s .mode = 0#3)
    (empty : s (.base .rxCount) = 0) (first : s (.base (.rxWord 0#1)) = 0)
    (second : s (.base (.rxWord 1#1)) = 0)
    (idleRaw : i .rawInputs = wireCode .j) (priorRaw : s (.base .stage1) = wireCode .j)
    (rate : PeerRate) (sop : Int) (nonnegative : 0 ≤ sop) (minimum : 2*rate.period ≤ sop)
    (timely : 2*sop ≤ 15*rate.period) (payload : List Bool) (size : payload.length = 64)
    (flight tail : List Wire) (ackWidth : flight.length = 304) (lastTwo : tail.length = 2) :
    let sampled := dataSamples rate sop 17 payload
    let raw := (sampled ++ flight).drop 2 ++ tail
    let listening : CoreState := circuit.step i s
    let retained : CoreState := rawRun listening raw
    let endMarker := advanceTime rate (advanceTime rate sop (wireCells (dataRuns payload))) 2
    sampled.length + 17 = (ceilTick endMarker rate.den).toNat+49 ∧
    ∃ ack : CoreState, ∃ words : Pair,
      Transcript listening sampled ack ∧ Transcript ack flight retained ∧
      Live ack 5 ∧ (ack .timer).toNat = 304 ∧
      retained (.base .phase) = 5 ∧ retained .mode = 0 ∧ retained (.base .rxCount) = 2 ∧
      retained (.base .rxProduced) = 64 ∧
      retained (.base (.rxWord 0#1)) = words.first ∧ retained (.base (.rxWord 1#1)) = words.second ∧
      decodeWord words.first 32 ++ decodeWord words.second 32 = payload := by
  have ⟨live,age,_,capture⟩ := gate_accepts_word i s quiet selected idle empty first second
  have hardware := two_stage i s quiet
  have bound := first_peer_drive rate sop minimum
  have startTime : 17 ≤ (ceilTick sop rate.den).toNat := by omega
  have sampled := recorded_clocked_transcript rate sop 17 startTime payload (circuit.step i s) flight
    (hardware.1.trans idleRaw) (hardware.2.trans priorRaw) tail lastTwo
  have age0 : ((circuit.step i s) .age).toNat = 0 := congrArg BitVec.toNat age
  exact clocked_transaction rate sop nonnegative timely 17 startTime payload size _ _
    live capture age0 flight ackWidth sampled

theorem unplugged_no_payload (trace : Transcript s (List.replicate 128 .j) e)
    (h : Live s 1) (start : (s .age).toNat = 0) :
    e .mode = 0 ∧ e (.base .phase) = 6 ∧ e (.base .enabled) = 0 ∧ e (.base .rxCount) = 0 := by
  have window : List.replicate 128 Wire.j = List.replicate 127 .j ++ [.j] := by decide +kernel
  rw [window] at trace
  obtain ⟨waiting,last,expired⟩ := trace.cut (List.replicate 127 .j)
  have ⟨live,_,age⟩ := live_wait 127 last h (by omega)
  obtain ⟨i,quiet,raw,same⟩ := expired.single
  simp only [register_eq same]
  exact waiting_timeout i waiting quiet live raw (by omega)

end Pinwheel.Hardware.USB
