import Pinwheel.Program.StreamingPS2Spec
import Pinwheel.Program.StreamingPS2Core

/-! An arbitrary legal keyboard clock drives the receive-only image.
The capture schedule is derived from the raw waveform and the actual engine. -/
namespace Pinwheel.Program.StreamingPS2
open StreamingReady StreamingPS2Core StreamingUART.QuietTiming

private def cutsFrom (k : Nat) (s : State a) : List Input → List Nat
  | [] => []
  | i :: rest =>
    (if s.rxEvent.isEmpty then [] else [k]) ++ cutsFrom (k + 1) (step program i s) rest

/-- Pre-edge indices of all engine RX events, measured from accepted START. -/
def captureCuts (s : State a) (inputs : List Input) : List Nat := cutsFrom 0 s inputs

private theorem cuts_append (k : Nat) (s : State a) (first rest : List Input) :
    cutsFrom k s (first ++ rest) = cutsFrom k s first ++
      cutsFrom (k + first.length) (run program s first) rest := by
  induction first generalizing k s with
  | nil => rfl
  | cons i tail ih =>
    rw [List.cons_append,cutsFrom,cutsFrom,ih,List.length_cons,List.append_assoc]
    rw [show k + 1 + tail.length = k + (tail.length + 1) by omega]
    rfl

private theorem cuts_size (k : Nat) (s : State a) (inputs : List Input) (trace : BitTrace)
    (quiet : ∀ i ∈ inputs, Quiet i) :
    trace.captured.length + (cutsFrom k s inputs).length =
      (traceRun program s trace inputs).captured.length := by
  induction inputs generalizing k s trace with
  | nil => simp [cutsFrom,traceRun]
  | cons i rest ih =>
    rw [traceRun,← ih (k + 1) _ _ (fun j member => quiet j (List.mem_cons_of_mem _ member))]
    rw [quiet_trace_edge s trace i (quiet i List.mem_cons_self)]
    cases capture : s.captures <;> simp [cutsFrom,State.rxEvent,capture,Nat.add_assoc,Nat.add_comm]

private theorem no_cuts (k : Nat) (s : State a) (inputs : List Input) (trace : BitTrace)
    (quiet : ∀ i ∈ inputs, Quiet i)
    (captured : (traceRun program s trace inputs).captured = trace.captured) :
    cutsFrom k s inputs = [] := by
  have n := cuts_size k s inputs trace quiet
  rw [captured] at n
  exact List.length_eq_zero_iff.mp (by omega)

private theorem one_cut (k : Nat) (s : State a) (i : Input) (inputs : List Input) (trace : BitTrace)
    (quiet : ∀ j ∈ i :: inputs, Quiet j)
    (first : s.rxEvent = [bit])
    (captured : (traceRun program s trace (i :: inputs)).captured = trace.captured ++ [bit]) :
    cutsFrom k s (i :: inputs) = [k] := by
  have later : (traceRun program (step program i s) (trace.step s i) inputs).captured =
      (trace.step s i).captured := by
    rw [quiet_trace_edge s trace i (quiet i List.mem_cons_self),first]
    exact captured
  simp [cutsFrom,first,no_cuts (k + 1) (step program i s) inputs (trace.step s i)
    (fun j member => quiet j (List.mem_cons_of_mem _ member)) later]

private theorem pins_append (s : State a) (first rest : List Input)
    (earlier : ∀ pad ∈ pinTrace program s first, pad = idlePins)
    (later : ∀ pad ∈ pinTrace program (run program s first) rest, pad = idlePins) :
    ∀ pad ∈ pinTrace program s (first ++ rest), pad = idlePins := by
  induction first generalizing s with
  | nil => exact later
  | cons i tail ih =>
    simp only [List.cons_append,pinTrace,List.mem_cons]
    intro pad member
    rcases member with rfl | inTail
    · exact earlier _ (by simp [pinTrace])
    · exact ih (step program i s) (fun p m => earlier p (by simp [pinTrace,m])) later pad inTail

private abbrev rawOf (inputs : List Input) : List (BitVec 2) := inputs.map (·.rawInputs)

private abbrev stateAt (s : State a) (inputs : List Input) (k : Nat) : State a :=
  run program s (inputs.take k)

private abbrev traceAt (s : State a) (inputs : List Input) (k : Nat) : BitTrace :=
  traceRun program s {} (inputs.take k)

private def slice (inputs : List Input) (lo hi : Nat) : List Input :=
  (inputs.drop lo).take (hi - lo)

private theorem slice_mem (member : i ∈ slice inputs lo hi) : i ∈ inputs :=
  List.mem_of_mem_drop (List.mem_of_mem_take member)

private theorem slice_length (inputs : List Input) (lo hi : Nat) (within : hi ≤ inputs.length) :
    (slice inputs lo hi).length = hi - lo := by
  simp only [slice,List.length_take,List.length_drop]
  omega

private theorem take_split (inputs : List Input) (lo hi : Nat) (ordered : lo ≤ hi) :
    inputs.take hi = inputs.take lo ++ slice inputs lo hi := by
  conv => lhs; rw [← Nat.add_sub_of_le ordered,List.take_add]
  rfl

private theorem state_split (s : State a) (inputs : List Input) (lo hi : Nat) (ordered : lo ≤ hi) :
    stateAt s inputs hi = run program (stateAt s inputs lo) (slice inputs lo hi) := by
  simp only [stateAt,take_split inputs lo hi ordered,run_append]

private theorem sampler_at (s : State a) (inputs : List Input) (k : Nat)
    (quiet : ∀ i ∈ inputs, Quiet i) (afterTwo : 2 ≤ k) (within : k ≤ inputs.length) :
    (stateAt s inputs k).samplerSecond = (rawOf inputs)[k-2]?.getD 0 := by
  let j := k - 2
  have jBound : j < inputs.length := by omega
  have jNext : j + 1 < inputs.length := by omega
  have two : k = j + 1 + 1 := by omega
  have portions : inputs.take k = inputs.take j ++ [inputs[j], inputs[j+1]] := by
    rw [two,List.take_succ_eq_append_getElem jNext,List.take_succ_eq_append_getElem jBound]
    simp only [List.append_assoc,List.singleton_append]
  rw [stateAt,portions,(run_two_samples program s _ _ _
    ((quiet _ (List.getElem_mem jBound)).runtime _) ((quiet _ (List.getElem_mem jNext)).runtime _)).2]
  simp [j,List.getElem?_eq_getElem jBound]

private structure Seen (s : State a) (inputs : List Input) (k : Nat) (falls : List Nat) : Prop where
  captured : (traceAt s inputs k).captured = falls.map (dataAt (rawOf inputs))
  pins : ∀ pad ∈ pinTrace program s (inputs.take k), pad = idlePins
  cuts : cutsFrom 0 s (inputs.take k) = falls.map (· + 2)

private theorem Seen.extend (seen : Seen s inputs lo before) (ordered : lo ≤ hi)
    (within : hi ≤ inputs.length)
    (captured : (traceRun program (stateAt s inputs lo) (traceAt s inputs lo)
      (slice inputs lo hi)).captured = (traceAt s inputs lo).captured ++ after.map (dataAt (rawOf inputs)))
    (pins : ∀ pad ∈ pinTrace program (stateAt s inputs lo) (slice inputs lo hi), pad = idlePins)
    (cuts : cutsFrom lo (stateAt s inputs lo) (slice inputs lo hi) = after.map (· + 2)) :
    Seen s inputs hi (before ++ after) := by
  constructor
  · simp only [traceAt,take_split inputs lo hi ordered,trace_append,List.map_append]
    rw [captured,seen.captured]
  · rw [take_split inputs lo hi ordered]
    exact pins_append s _ _ seen.pins pins
  · rw [take_split inputs lo hi ordered,cuts_append,List.length_take,
      Nat.min_eq_left (Nat.le_trans ordered within),Nat.zero_add,seen.cuts,cuts,List.map_append]

private theorem slice_head (inputs : List Input) (lo hi : Nat) (ordered : lo < hi)
    (within : lo < inputs.length) :
    slice inputs lo hi = inputs[lo] :: slice inputs (lo + 1) hi := by
  unfold slice
  rw [List.drop_eq_getElem_cons within,show hi - lo = hi - (lo + 1) + 1 by omega]
  rfl

private theorem await (s : State a) (inputs : List Input) (quiet : ∀ i ∈ inputs, Quiet i)
    (n lo hi : Nat) (afterTwo : 2 ≤ lo) (ordered : lo ≤ hi) (within : hi ≤ inputs.length)
    (armed : Armed (stateAt s inputs lo) n) (seen : Seen s inputs lo before)
    (high : ∀ k, lo ≤ k → k < hi → clockAt (rawOf inputs) (k-2) = true) :
    Armed (stateAt s inputs hi) n ∧ Seen s inputs hi before := by
  induction hi with
  | zero => omega
  | succ k ih =>
    by_cases arrived : lo = k + 1
    · subst lo
      exact ⟨armed,seen⟩
    have loToK : lo ≤ k := by omega
    have atK := ih loToK (by omega) (fun j lower upper => high j lower (by omega))
    have inBounds : k < inputs.length := by omega
    have edgeSlice : slice inputs k (k+1) = [inputs[k]] := by
      rw [slice_head inputs k (k+1) (by omega) inBounds]
      simp [slice]
    have highSample := high k loToK (by omega)
    rw [clockAt,← sampler_at s inputs k quiet (by omega) (by omega)] at highSample
    have edgeQuiet := quiet _ (List.getElem_mem inBounds)
    have next := wait_miss _ _ atK.1 _ edgeQuiet highSample
    have nextState : Armed (stateAt s inputs (k+1)) n := by
      rw [state_split s inputs k (k+1) (by omega),edgeSlice]
      exact next.1
    refine ⟨nextState, ?_⟩
    simpa only [List.append_nil] using (atK.2.extend (hi := k+1) (after := []) (by omega) within
      (by simp [edgeSlice,traceRun,quiet_trace_edge _ _ _ edgeQuiet,next.2])
      (by simp [edgeSlice,pinTrace,atK.1.pins,next.1.pins])
      (by simp [edgeSlice,cutsFrom,next.2]))

private theorem at_fall (s : State a) (inputs : List Input) (quiet : ∀ i ∈ inputs, Quiet i)
    (n lo fall : Nat) (afterTwo : 2 ≤ lo) (beforeFall : lo ≤ fall + 2) (within : fall + 2 ≤ inputs.length)
    (high : ∀ k, lo - 2 ≤ k → k < fall → clockAt (rawOf inputs) k = true)
    (low : clockAt (rawOf inputs) fall = false)
    (armed : Armed (stateAt s inputs lo) n) (seen : Seen s inputs lo earlier) :
    Armed (stateAt s inputs (fall+2)) n ∧ Seen s inputs (fall+2) earlier ∧
      (stateAt s inputs (fall+2)).samplerSecond[0] = false ∧
      (stateAt s inputs (fall+2)).samplerSecond[1] = dataAt (rawOf inputs) fall := by
  have missed := await s inputs quiet n lo (fall+2) afterTwo beforeFall within armed seen (by
    intro k lower upper
    exact high (k-2) (by omega) (by omega))
  have sampled := sampler_at s inputs (fall+2) quiet (by omega) within
  simp only [Nat.add_sub_cancel] at sampled
  exact ⟨missed.1,missed.2,by rw [sampled]; exact low,by rw [sampled]; rfl⟩

private theorem seen_capture (seen : Seen s inputs (fall+2) earlier) (ordered : fall+2 ≤ hi)
    (within : hi ≤ inputs.length) (quiet : ∀ j ∈ edge :: tail, Quiet j)
    (parts : slice inputs (fall+2) hi = edge :: tail)
    (event : (stateAt s inputs (fall+2)).rxEvent = [dataAt (rawOf inputs) fall])
    (captured : (traceRun program (stateAt s inputs (fall+2)) (traceAt s inputs (fall+2))
      (edge :: tail)).captured = (traceAt s inputs (fall+2)).captured ++ [dataAt (rawOf inputs) fall])
    (pins : pinTrace program (stateAt s inputs (fall+2)) (edge :: tail) = List.replicate (tail.length+2) idlePins) :
    Seen s inputs hi (earlier ++ [fall]) := by
  apply seen.extend ordered within
  · rw [parts]
    exact captured
  · rw [parts,pins]
    intro pad member
    exact List.eq_of_mem_replicate member
  · rw [parts]
    exact one_cut _ _ _ _ _ quiet event captured

private theorem run_clocking (s : State a) (inputs : List Input) (quiet : ∀ i ∈ inputs, Quiet i)
    {fall : Nat} {later : List Nat} (clocking : Clocking (rawOf inputs) fall later)
    (lo : Nat) (afterTwo : 2 ≤ lo) (beforeFall : lo ≤ fall + 2)
    (high : ∀ k, lo - 2 ≤ k → k < fall → clockAt (rawOf inputs) k = true)
    (armed : Armed (stateAt s inputs lo) (later.length + 1)) (seen : Seen s inputs lo earlier) :
    (run program s inputs).phase = .completed ∧
      Seen s inputs inputs.length (earlier ++ fall :: later) := by
  induction clocking generalizing lo earlier with
  | @last fall rise minLow _ low _ wireLength =>
    simp only [List.length_map] at wireLength
    have atFall := at_fall s inputs quiet 1 lo fall afterTwo beforeFall (by omega)
      high (low _ (Nat.le_refl _) (by omega)) armed seen
    let k := fall + 2
    have inBounds : k < inputs.length := by omega
    let edge := inputs[k]
    let tail := slice inputs (k+1) inputs.length
    have parts : slice inputs k inputs.length = edge :: tail :=
      slice_head inputs k inputs.length inBounds inBounds
    have segmentQuiet : ∀ j ∈ edge :: tail, Quiet j := by
      rw [← parts]
      exact fun j member => quiet j (slice_mem member)
    have duration : tail.length = 218 := by
      rw [slice_length inputs (k+1) inputs.length (Nat.le_refl _)]
      omega
    obtain ⟨complete,_,_,captured,pins⟩ := capture_complete _ atFall.1 (traceAt s inputs k)
      edge tail atFall.2.2.1 segmentQuiet duration
    have recorded := seen_capture atFall.2.1 (by omega) (Nat.le_refl _) segmentQuiet parts
      ((armed_capture _ _ atFall.1 atFall.2.2.1).trans (congrArg List.singleton atFall.2.2.2))
      (by rw [← atFall.2.2.2]; exact captured) pins
    have total : stateAt s inputs inputs.length = run program (stateAt s inputs k) (edge :: tail) :=
      (state_split s inputs k inputs.length (by omega)).trans (congrArg _ parts)
    simp only [stateAt,List.take_length] at total
    rw [total]
    exact ⟨complete,recorded⟩
  | @next fall rise nextFall rest minLow maxLow minHigh _ low highPhase laterClock ih =>
    have endBound := laterClock.fits
    simp only [List.length_map] at endBound
    have atFall := at_fall s inputs quiet (rest.length+2) lo fall afterTwo beforeFall (by omega)
      high (low _ (Nat.le_refl _) (by omega)) armed seen
    let k := fall + 2
    let rearmed := fall + 222
    have inBounds : k < inputs.length := by omega
    have rearmedBound : rearmed ≤ inputs.length := by omega
    let edge := inputs[k]
    let tail := slice inputs (k+1) rearmed
    have parts : slice inputs k rearmed = edge :: tail :=
      slice_head inputs k rearmed (by omega) inBounds
    have segmentQuiet : ∀ j ∈ edge :: tail, Quiet j := by
      rw [← parts]
      exact fun j member => quiet j (slice_mem member)
    have duration : tail.length = 219 := by
      rw [slice_length inputs (k+1) rearmed rearmedBound]
      omega
    obtain ⟨nextArmed,captured,pins⟩ := capture_rearm _ _ atFall.1 (traceAt s inputs k)
      edge tail atFall.2.2.1 segmentQuiet duration (by omega)
    have record := seen_capture atFall.2.1 (by omega) rearmedBound segmentQuiet parts
      ((armed_capture _ _ atFall.1 atFall.2.2.1).trans (congrArg List.singleton atFall.2.2.2))
      (by rw [← atFall.2.2.2]; exact captured) pins
    have rearm : Armed (stateAt s inputs rearmed) (rest.length+1) := by
      rw [state_split s inputs k rearmed (by omega),parts]
      exact nextArmed
    have after := ih rearmed (by omega) (by omega) (fun j lower upper => highPhase j (by omega) upper)
      rearm record
    simpa only [List.append_assoc,List.singleton_append] using after

/-- Each raw falling clock edge accounts for the one capture exactly two
core clocks later, with CLK and DATA released throughout the run. -/
theorem run_frame (before : State a) (command : Input) (inputs : List Input)
    (count : command.startCount = 11#16) (quiet : ∀ i ∈ inputs, Quiet i)
    (peer : PeerFrame (inputs.map (·.rawInputs)) symbols) :
    let seed := before.start program command
    (run program seed inputs).phase = .completed ∧
    (traceRun program seed {} inputs).captured = symbols ∧
    (∀ pad ∈ pinTrace program seed inputs, pad.enabled = 0) ∧
    captureCuts seed inputs = peer.falls.map (· + 2) := by
  intro seed
  have within := peer.clocking.fits
  simp only [List.length_map] at within
  have initialLength : (inputs.take 3).length = 3 := by
    rw [List.length_take,Nat.min_eq_left (by omega)]
  have initialQuiet : ∀ i ∈ inputs.take 3, Quiet i :=
    fun i member => quiet i (List.mem_of_mem_take member)
  obtain ⟨armed,capture,pins⟩ := started_waiting before command (inputs.take 3) count initialQuiet initialLength
  have initial : Seen seed inputs 3 [] := ⟨capture,by
    rw [pins]
    exact fun pad member => List.eq_of_mem_replicate member,
    no_cuts 0 seed _ {} initialQuiet capture⟩
  have ready : Armed (stateAt seed inputs 3) (peer.laterFalls.length + 1) := by
    simpa only [peer.laterCount] using armed
  obtain ⟨completed,observed⟩ := run_clocking seed inputs quiet peer.clocking 3 (by decide)
    (by have := peer.start; omega) (fun k _ early => peer.idle k early) ready initial
  have bits := observed.captured
  have drives := observed.pins
  have cuts := observed.cuts
  simp only [traceAt,List.take_length,List.nil_append] at bits
  simp only [List.take_length] at drives
  simp only [List.take_length,List.nil_append] at cuts
  exact ⟨completed,bits.trans peer.data,fun pad member => by rw [drives pad member]; rfl,cuts⟩

end Pinwheel.Program.StreamingPS2
