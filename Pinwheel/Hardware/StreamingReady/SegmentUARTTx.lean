import Pinwheel.Hardware.StreamingReady.SegmentPulseRefinement
import Pinwheel.Hardware.StreamingReady.SegmentTimingImages
import Pinwheel.Program.StreamingReadyUARTTx

/-! Verify the held-out 8N1 transmitter on the ordinary pulse API. Each
    observed sample is the actual pad state after one supplied edge. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentUARTTx

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentPulseRefinement
open Pinwheel.Program.StreamingReady (Pins Instruction encode encode_fields)
open Pinwheel.Program.StreamingReadySegments (Row)
open Pinwheel.Program.StreamingReadyUARTTx (cell config cycles pins rows symbols symbols_eq_frame)
open ProtocolOwnership (DrainInput)
open SegmentTiming (run)

def pose (s : Values (Register a)) : Pins := ⟨s (.base .levels), s (.base .enabled)⟩

theorem supported (hold : Fin 253) (byte : BitVec 8) :
    SegmentTimingImages.SupportedRows (rows hold byte) := rfl

def padTrace (registered : Bool) (s : Values (Register a)) : List (Values Core.Input) → List Pins
  | [] => []
  | i :: rest =>
    let after : Values (Register a) := (circuit a registered).step i s
    pose after :: padTrace registered after rest

theorem padTrace_append (registered : Bool) (s : Values (Register a))
    (first rest : List (Values Core.Input)) :
    padTrace registered s (first ++ rest) =
      padTrace registered s first ++ padTrace registered (run registered s first) rest := by
  induction first generalizing s with
  | nil => rfl
  | cons i first ih => simp [padTrace, run, ih]

private theorem ordinary (h : DrainInput i) : NoReset i := ⟨h.1, by simp [h.2.1]⟩

private theorem low_pose (registered : Bool) (s : Values (Register a))
    (clocks : List (Values Core.Input)) (phase : s (.base .phase) = 3#3)
    (room : clocks.length ≤ (s (.base .countdown)).toNat)
    (runtime : ∀ i ∈ clocks, NoReset i) :
    padTrace registered s clocks = List.replicate clocks.length (pose s) := by
  induction clocks generalizing s with
  | nil => rfl
  | cons i rest ih =>
    let after : Values (Register a) := (circuit a registered).step i s
    have first : [@i].length ≤ (s (.base .countdown)).toNat := by
      simp only [List.length_cons, List.length_nil]
      simp only [List.length_cons] at room
      omega
    have dwell := SegmentStreamStep.low_span_runtime registered s [@i] phase first
      (by simpa using runtime i (by simp))
    have stable : pose after = pose s := by
      change (⟨after (.base .levels), after (.base .enabled)⟩ : Pins) =
        ⟨s (.base .levels), s (.base .enabled)⟩
      rw [show after (.base .levels) = _ from dwell.pose.levels,
        show after (.base .enabled) = _ from dwell.pose.enabled]
    have remaining : rest.length ≤ (after (.base .countdown)).toNat := by
      rw [show (after (.base .countdown)).toNat = _ from dwell.countdown]
      simp only [List.length_cons, List.length_nil] at room ⊢
      omega
    change pose after :: padTrace registered after rest = _
    rw [ih after dwell.phase remaining (fun j hj => runtime j (List.mem_cons_of_mem _ hj)), stable]
    rfl

set_option linter.unusedSimpArgs false in
private theorem pulse_exit_pose (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (hold : Fin 253) (level : Bool) (clean : NoReset i) (high : s (.base .phase) = 4#3)
    (elapsed : s (.base .countdown) = 0#8) (loaded : s (.base .currentWord) = encode (.pulse (cell hold level))) :
    pose ((circuit a registered).step i s) = pins level := by
  have fields := encode_fields (.pulse (cell hold level))
  have op : (s (.base .currentWord)).extractLsb' 0 3 = 0#3 := loaded ▸ fields.operation
  have levels : (s (.base .currentWord)).extractLsb' 19 3 = (pins level).levels := loaded ▸ fields.lowLevels
  have enabled : (s (.base .currentWord)).extractLsb' 22 3 = (pins level).enabled := loaded ▸ fields.lowEnabled
  have mask (value : BitVec 3) : ~~~(~~~value &&& 7#3) = value := by decide +revert +kernel
  suffices pair : ((circuit a registered).step i s) (.base .levels) = (pins level).levels ∧
      ((circuit a registered).step i s) (.base .enabled) = (pins level).enabled by
    change (⟨((circuit a registered).step i s) (.base .levels),
      ((circuit a registered).step i s) (.base .enabled)⟩ : Pins) = pins level
    rw [pair.1, pair.2]
  have expose {w : Nat} (r : Core.Register a w) : (circuit a registered).step i s (.base r) =
      (nextBase r).eval i (withFetch s ((word registered).eval i s)) := bindWord_eval _ _ _ _
  constructor <;>
    simp [expose, nextBase, originalNext, Expr.eval_bind, usesEntryWord, runtimeInput, decodedRegister, lift,
      withFetch, Expr.eval, Core.next, Core.nextRaw, Core.nextPins, Core.basePins, Core.lastCell, Core.stream,
      Core.cold, Core.warm, Core.cmd, Core.resetting, Core.both, Core.either, Core.free, Core.starting,
      Core.releasing, Core.hostOwner, Core.owned, Core.retained, Core.isPhase, Core.fetching, Core.enteringCell,
      Core.reserving, Core.advancing, Core.highEnd, Core.lowEnd, Core.guardedLowEnd, Core.waitSuccess,
      Core.standaloneSuccess, Core.waitFault, Core.capturingRX, Core.capture, Core.field,
      SegmentCore.control, SegmentCore.discard, branch, setCount, fetching, both, either, field,
      clean.1, clean.2, high, elapsed, op, levels, enabled, mask] <;> done

private theorem pose_eq (s : Values (Register a)) (p : Pins)
    (levels : s (.base .levels) = p.levels) (enabled : s (.base .enabled) = p.enabled) : pose s = p := by
  cases p with
  | mk lvl ena =>
    change (⟨s (.base .levels), s (.base .enabled)⟩ : Pins) = ⟨lvl, ena⟩
    rw [levels, enabled]

/-- All clocks of one constant pulse publish the same symbol, including
    its fetch, reservation, transition and exit overhead. -/
theorem pulse_block (registered : Bool) (s : Values (Register a)) (hold : Fin 253) (level : Bool)
    (atFetch : AtBoundary registered image pc capture s)
    (row : image[pc]? = some (.cell (.pulse (cell hold level))))
    (fetch arm rise leave : Values Core.Input) (low : List (Values Core.Input))
    (lowLength : low.length = hold.val)
    (runtime : ∀ i ∈ @fetch :: @arm :: (low ++ [@rise, @leave]), DrainInput i) :
    let inputs : List (Values Core.Input) := @fetch :: @arm :: (low ++ [@rise, @leave])
    padTrace registered s inputs = List.replicate (config hold).cycles (pins level) ∧
      AtBoundary registered image (pc + 1) capture (run registered s inputs) := by
  let encoded := cell hold level
  have canonical : (Instruction.pulse encoded).Canonical :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have lowClean : ∀ i ∈ low, DrainInput i := fun i hi => runtime i (by simp [hi])
  let loaded : Values (Register a) := (circuit a registered).step fetch s
  let reserved : Values (Register a) := (circuit a registered).step arm loaded
  let descended : Values (Register a) := run registered reserved low
  let climbed : Values (Register a) := (circuit a registered).step rise descended
  obtain ⟨load, reserve, lowSpan, enter, next⟩ := run_pulse_row registered s encoded atFetch row canonical
    fetch arm rise leave low [] (ordinary (runtime _ (by simp))) (ordinary (runtime _ (by simp)))
    (ordinary (runtime _ (by simp))) (ordinary (runtime _ (by simp))) lowClean (by simp) lowLength rfl
  have first : pose loaded = pins level := pose_eq loaded _ load.levels load.enabled
  have second : pose reserved = pins level := pose_eq reserved _ reserve.levels reserve.enabled
  have high : pose climbed = pins level := pose_eq climbed _ enter.levels enter.enabled
  have dwell : padTrace registered reserved low = List.replicate low.length (pins level) := by
    rw [← second]
    apply low_pose registered reserved low reserve.phase
    · have count : reserved (.base .countdown) = BitVec.ofNat 8 hold.val := reserve.countdown
      rw [count, BitVec.toNat_ofNat, lowLength, Nat.mod_eq_of_lt (show hold.val < 256 from by omega)]
      exact Nat.le_refl _
    · exact fun i hi => ordinary (lowClean i hi)
  have expired : climbed (.base .countdown) = 0#8 := enter.countdown
  have current : climbed (.base .currentWord) = encode (.pulse encoded) :=
    enter.current.trans (lowSpan.pose.current.trans (reserve.current.trans load.current))
  have finalPose := pulse_exit_pose registered leave climbed hold level
    (ordinary (runtime _ (by simp))) enter.phase expired current
  constructor
  · change pose loaded :: pose reserved :: padTrace registered reserved (low ++ [@rise, @leave]) = _
    rw [padTrace_append, first, second, dwell]
    change pins level :: pins level :: (List.replicate low.length (pins level) ++
      [pose climbed, pose ((circuit a registered).step leave climbed)]) = _
    rw [high, finalPose, lowLength, cycles]
    change List.replicate 2 (pins level) ++
      (List.replicate hold.val (pins level) ++ List.replicate 2 (pins level)) = _
    rw [List.replicate_append_replicate, List.replicate_append_replicate]
    simp only [Nat.add_left_comm, Nat.reduceAdd]
  · change AtBoundary registered image (pc + 1) capture (run registered reserved (low ++ [@rise, @leave]))
    rw [SegmentTiming.run_append]
    exact next

private theorem pulse_tape (registered : Bool) (s : Values (Register a)) (hold : Fin 253) (level : Bool)
    (atFetch : AtBoundary registered image pc capture s)
    (row : image[pc]? = some (.cell (.pulse (cell hold level))))
    (tape : List (Values Core.Input)) (length : tape.length = (config hold).cycles)
    (drains : ∀ i ∈ tape, DrainInput i) :
    padTrace registered s tape = List.replicate (config hold).cycles (pins level) ∧
      AtBoundary registered image (pc + 1) capture (run registered s tape) := by
  rw [cycles] at length
  cases tape with
  | nil => simp at length
  | cons fetch tail =>
    cases tail with
    | nil => simp at length
    | cons arm rest =>
      simp only [List.length_cons] at length
      let low := rest.take hold.val
      have lowLength : low.length = hold.val := by simp [low, Nat.min_eq_left (show hold.val ≤ rest.length by omega)]
      have ends : (rest.drop hold.val).length = 2 := by rw [List.length_drop]; omega
      cases suffix : rest.drop hold.val with
      | nil => simp [suffix] at ends
      | cons rise tail =>
        cases tail with
        | nil => simp [suffix] at ends
        | cons leave tail =>
          have empty : tail = [] := by simpa [suffix] using ends
          subst tail
          have restShape : rest = low ++ [@rise, @leave] := calc
            _ = low ++ rest.drop hold.val := (List.take_append_drop _ _).symm
            _ = _ := by rw [suffix]
          rw [restShape] at drains ⊢
          exact pulse_block registered s hold level atFetch row fetch arm rise leave low lowLength drains

private theorem pulses (registered : Bool) (s : Values (Register a)) (hold : Fin 253)
    (bits : List Bool) (atFetch : AtBoundary registered image pc capture s)
    (schedule : ∀ (i : Nat) (inside : i < bits.length),
      image[pc + i]? = some (.cell (.pulse (cell hold bits[i]))))
    (tape : List (Values Core.Input)) (length : tape.length = bits.length * (config hold).cycles)
    (drains : ∀ i ∈ tape, DrainInput i) :
    padTrace registered s tape = bits.flatMap (fun level => List.replicate (config hold).cycles (pins level)) ∧
      AtBoundary registered image (pc + bits.length) capture (run registered s tape) := by
  induction bits generalizing pc s tape with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul, List.length_eq_zero_iff] at length
    subst tape
    simpa [padTrace, run] using atFetch
  | cons level bits ih =>
    let clocks := (config hold).cycles
    let first := tape.take clocks
    let rest := tape.drop clocks
    have tapeShape : first ++ rest = tape := List.take_append_drop _ _
    have enough : clocks ≤ tape.length := by
      rw [length, List.length_cons, Nat.succ_mul]
      exact Nat.le_add_left _ _
    have firstLength : first.length = clocks := by simp [first, Nat.min_eq_left enough]
    have restLength : rest.length = bits.length * clocks := by
      change (tape.drop (config hold).cycles).length = bits.length * (config hold).cycles
      rw [List.length_drop, length, List.length_cons, Nat.succ_mul]
      omega
    have firstRow : image[pc]? = some (.cell (.pulse (cell hold level))) := by
      exact schedule 0 (by simp)
    obtain ⟨firstPins, next⟩ := pulse_tape registered s hold level atFetch firstRow first firstLength
      (fun i member => drains i (List.mem_of_mem_take member))
    have nextRows (i : Nat) (inside : i < bits.length) :
        image[pc + 1 + i]? = some (.cell (.pulse (cell hold bits[i]))) := by
      have eq : pc + 1 + i = pc + (i + 1) := by omega
      rw [eq]
      exact schedule (i + 1) (by simp; omega)
    obtain ⟨restPins, endState⟩ := ih (run registered s first) next nextRows rest restLength
      (fun i member => drains i (List.mem_of_mem_drop member))
    rw [← tapeShape, padTrace_append, SegmentTiming.run_append, firstPins, restPins]
    exact ⟨rfl, by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using endState⟩

/-- For any accepted START and any ordinary drain tape that spans the 8N1
    frame, the actual driven pads reproduce every clock of the independent
    UART frame and reach its final FETCH. -/
theorem waveform_from_start (registered : Bool) (hold : Fin 253) (byte : BitVec 8)
    (before : Values (Register a)) (start : Values Core.Input)
    (installed : Installed (rows hold byte) before)
    (admitted : Core.starting.eval start (project before) = 1#1)
    (tape : List (Values Core.Input)) (length : tape.length = (config hold).frameCycles)
    (drains : ∀ i ∈ tape, DrainInput i) :
    let started : Values (Register a) := (circuit a registered).step start before
    padTrace registered started tape = (Pinwheel.UART.frame byte).toList.flatMap
      (fun level => List.replicate (config hold).cycles (pins level)) ∧
    AtBoundary registered (rows hold byte) 10 none (run registered started tape) := by
  let started : Values (Register a) := (circuit a registered).step start before
  have initial := (start_at_boundary registered start before installed admitted).1
  have count : (symbols byte).length = 10 := by rw [symbols_eq_frame, Array.length_toList, Pinwheel.UART.frame_size]
  have clocks : tape.length = (symbols byte).length * (config hold).cycles := by
    rw [count]
    exact length
  have schedule (i : Nat) (inside : i < (symbols byte).length) :
      (rows hold byte)[0 + i]? = some (.cell (.pulse (cell hold (symbols byte)[i]))) := by
    simp only [rows, Nat.zero_add]
    rw [List.getElem?_append_left (by simp [inside]), List.getElem?_map]
    simp [List.getElem?_eq_getElem inside]
  obtain ⟨trace, ending⟩ := pulses registered started hold (symbols byte) initial schedule tape clocks drains
  exact ⟨by rw [trace, symbols_eq_frame], by simpa only [count, Nat.zero_add] using ending⟩

/-- Fetching the generated HALT retains the same owner and accounting and
    drives the idle pose installed by the generic loader. -/
theorem halt_after_waveform (registered : Bool) (hold : Fin 253) (byte : BitVec 8)
    (before : Values (Register a)) (start finish : Values Core.Input)
    (installed : Installed (rows hold byte) before)
    (admitted : Core.starting.eval start (project before) = 1#1)
    (tape : List (Values Core.Input)) (length : tape.length = (config hold).frameCycles)
    (drains : ∀ i ∈ tape, DrainInput i) (finalDrain : DrainInput finish) :
    let opened : Values (Register a) := (circuit a registered).step start before
    let atHalt : Values (Register a) := run registered opened tape
    let retained : Values (Register a) := (circuit a registered).step finish atHalt
    ProtocolOwnership.TerminalCut.of retained =
      {ProtocolOwnership.TerminalCut.of atHalt with phase := 5#3} ∧
      pose retained = ⟨atHalt (.base .idleLevels), atHalt (.base .idleEnabled)⟩ := by
  have halt := (waveform_from_start registered hold byte before start installed admitted tape length drains).2
  obtain ⟨finished, levels, enabled⟩ := terminal_step halt finish finalDrain false rfl
  exact ⟨finished, pose_eq _ _ levels enabled⟩

end Pinwheel.Hardware.StreamingReady.SegmentUARTTx
