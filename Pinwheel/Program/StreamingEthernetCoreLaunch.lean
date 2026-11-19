import Pinwheel.Program.StreamingEthernetCoreFrame

/-! Synchronization from an armed, preloaded owner to the first serial bit.
The canonical fixture asserts GO on a sampled PHY rising edge. -/
namespace Pinwheel.Program.StreamingEthernetCore
open StreamingReady

set_option linter.unusedSimpArgs false

private def goRow : Instruction := .driveWait idlePins goGuard

private structure AwaitGo (s : State 1) : Prop where
  phase : s.phase = .waiting
  pc : s.pc = 0
  row : s.current = goRow
  count : s.countdown = 0
  remaining : s.remaining = 576
  pins : s.pins = idlePins

private theorem arm_step (before : State 1) (start i : Input) (runtime : i.Runtime)
    (count : start.startCount = 576) : AwaitGo (step program i (before.start program start)) := by
  have fetched : program.fetch 0 = some goRow := image.program_fetch 0 (by decide +kernel)
  rw [step_busy_eq_clock program _ i runtime (by rfl)]
  constructor <;> simp [clock, engine, State.start, fetched, count, goRow, goGuard,
    WaitLimit.initialCountdown]

private theorem go_match (raw : BitVec 2) : goGuard.matches raw = raw[1] := by
  decide +revert +kernel

private theorem arm_miss (s : State 1) (i : Input) (runtime : i.Runtime) (armed : AwaitGo s)
    (goLow : s.samplerSecond[1] = false) : AwaitGo (step program i s) := by
  rw [step_busy_eq_clock program s i runtime (by simp [armed.phase, Phase.busy])]
  have miss : s.waitReady = false := by
    rw [State.waitReady, armed.row]
    exact (go_match s.samplerSecond).trans goLow
  constructor <;> simp [clock, engine, armed.phase, armed.pc, miss, armed.row, armed.count, armed.pins,
    armed.remaining, goRow, Instruction.guard, goGuard, WaitLimit.expires, WaitLimit.poll]

private theorem hold_armed (s : State 1) (inputs : List Input) (armed : AwaitGo s)
    (firstLow : s.samplerFirst[1] = false) (secondLow : s.samplerSecond[1] = false)
    (runtime : ∀ i ∈ inputs, i.Runtime) (rawLow : ∀ i ∈ inputs, i.rawInputs[1] = false) :
    AwaitGo (run program s inputs) ∧
      pinTrace program s inputs = List.replicate (inputs.length + 1) idlePins := by
  induction inputs generalizing s with
  | nil => exact ⟨armed, by simp [pinTrace, armed.pins]⟩
  | cons i rest ih =>
    have ordinary := runtime i List.mem_cons_self
    have samples := step_samples program s i ordinary
    have next := arm_miss s i ordinary armed secondLow
    obtain ⟨endArm, pins⟩ := ih (step program i s) next (by rw [samples.1]; exact rawLow i List.mem_cons_self)
      (by rw [samples.2]; exact firstLow) (fun j h => runtime j (List.mem_cons_of_mem _ h))
      (fun j h => rawLow j (List.mem_cons_of_mem _ h))
    exact ⟨endArm, by simp [pinTrace, armed.pins, pins, List.replicate_succ]⟩

private theorem arm_prefix (before : State 1) (start : Input) (inputs : List Input)
    (count : start.startCount = 576) (more : inputs ≠ []) (startLow : start.rawInputs[1] = false)
    (runtime : ∀ i ∈ inputs, i.Runtime) (rawLow : ∀ i ∈ inputs, i.rawInputs[1] = false) :
    let seed := before.start program start
    AwaitGo (run program seed inputs) ∧
      pinTrace program seed inputs = List.replicate (inputs.length + 1) idlePins := by
  cases inputs with
  | nil => exact False.elim (more rfl)
  | cons first rest =>
    let seed := before.start program start
    have ordinary := runtime first List.mem_cons_self
    have armed := arm_step before start first ordinary count
    have samples := step_samples program seed first ordinary
    obtain ⟨endArm, pins⟩ := hold_armed (step program first seed) rest armed
      (by rw [samples.1]; exact rawLow first List.mem_cons_self)
      (by rw [samples.2]; exact startLow)
      (fun j h => runtime j (List.mem_cons_of_mem _ h)) (fun j h => rawLow j (List.mem_cons_of_mem _ h))
    refine ⟨endArm, ?_⟩
    change idlePins :: pinTrace program (step program first seed) rest = _
    rw [pins]
    rfl

private def erase (s : State 1) : State 1 :=
  {phase := s.phase, pc := s.pc, current := s.current, remaining := s.remaining,
    countdown := s.countdown, pins := s.pins, samplerFirst := s.samplerFirst,
    samplerSecond := s.samplerSecond}

private theorem erase_engine (s : State 1) (phase : s.phase = .fetch ∨ s.phase = .waiting) :
    erase (engine program s) = erase (engine program (erase s)) := by
  have phaseEq : (erase s).phase = s.phase := rfl
  have pcEq : (erase s).pc = s.pc := rfl
  have remainingEq : (erase s).remaining = s.remaining := rfl
  have currentEq : (erase s).current = s.current := rfl
  have countEq : (erase s).countdown = s.countdown := rfl
  have readyEq : (erase s).waitReady = s.waitReady := rfl
  rcases phase with phase | phase
  · simp only [engine, phaseEq, pcEq, phase, remainingEq]
    generalize program.fetch s.pc.toNat = fetched
    cases fetched with
    | none => rfl
    | some instruction =>
      cases instruction <;> try rfl
      by_cases empty : (s.remaining == 0) = true <;> simp only [empty, ↓reduceIte] <;> rfl
  · simp only [engine, phaseEq, phase, currentEq, countEq, readyEq]
    cases wait : s.waitReady <;> cases stream : s.current.isStream <;>
      cases expires : s.current.guard.limit.expires s.countdown <;> rfl

private theorem erased_step (s t : State 1) (i j : Input)
    (runtimeI : i.Runtime) (runtimeJ : j.Runtime) (raw : i.rawInputs = j.rawInputs)
    (same : erase s = erase t) (launch : t.phase = .fetch ∨ t.phase = .waiting) :
    erase (step program i s) = erase (step program j t) := by
  have phases := congrArg State.phase same
  have sLaunch : s.phase = .fetch ∨ s.phase = .waiting := phases.symm ▸ launch
  have sBusy : s.phase.busy = true := by rcases sLaunch with h | h <;> simp [h, Phase.busy]
  have tBusy : t.phase.busy = true := by rcases launch with h | h <;> simp [h, Phase.busy]
  have engineEq := (erase_engine s sLaunch).trans (by rw [same, ← erase_engine t launch])
  have first : s.samplerFirst = t.samplerFirst := by
    change (erase s).samplerFirst = (erase t).samplerFirst
    rw [same]
  rw [step_busy_eq_clock program s i runtimeI sBusy, step_busy_eq_clock program t j runtimeJ tBusy]
  change {erase (engine program s) with samplerFirst := i.rawInputs, samplerSecond := s.samplerFirst} =
    {erase (engine program t) with samplerFirst := j.rawInputs, samplerSecond := t.samplerFirst}
  rw [engineEq, raw, first]

private def prelaunch (s : State 1) : List Input → Bool
  | [] => true
  | i :: rest => (s.phase == .fetch || s.phase == .waiting) && prelaunch (step program i s) rest

private theorem paired (s t : State 1) (actual reference : List Input) (same : erase s = erase t)
    (runtimeA : ∀ i ∈ actual, i.Runtime) (runtimeR : ∀ i ∈ reference, i.Runtime)
    (rawEq : actual.map (·.rawInputs) = reference.map (·.rawInputs))
    (launch : prelaunch t reference = true) :
    erase (run program s actual) = erase (run program t reference) ∧
      pinTrace program s actual = pinTrace program t reference := by
  induction actual generalizing s t reference with
  | nil =>
    have empty : reference = [] := List.length_eq_zero_iff.mp (by simpa using congrArg List.length rawEq.symm)
    subst reference
    exact ⟨same, by change [(erase s).pins] = [(erase t).pins]; rw [same]⟩
  | cons i rest ih =>
    cases reference with
    | nil => simp at rawEq
    | cons j tail =>
      have values := List.cons.inj (show i.rawInputs :: rest.map (·.rawInputs) =
        j.rawInputs :: tail.map (·.rawInputs) from rawEq)
      have stages : (t.phase = .fetch ∨ t.phase = .waiting) ∧ prelaunch (step program j t) tail = true := by
        simpa [prelaunch] using launch
      have after := erased_step s t i j (runtimeA i List.mem_cons_self) (runtimeR j List.mem_cons_self)
        values.1 same stages.1
      obtain ⟨final, pins⟩ := ih _ _ tail after
        (fun q h => runtimeA q (List.mem_cons_of_mem _ h)) (fun q h => runtimeR q (List.mem_cons_of_mem _ h))
        values.2 stages.2
      have samePins : s.pins = t.pins := by
        change (erase s).pins = (erase t).pins
        rw [same]
      exact ⟨final, by change s.pins :: _ = t.pins :: _; rw [samePins, pins]⟩

private def armedReference : State 1 :=
  {phase := .waiting, current := goRow, remaining := 576, pins := idlePins}

/-- GO is high and clock rises in slots 0, 6, 12. Sampled clock high lasts
one or two core clocks in each period, independently. -/
def launchRaw (wide0 wide1 wide2 : Bool) : List (BitVec 2) :=
  let slot (j : Nat) :=
    let wide := if j < 6 then wide0 else if j < 12 then wide1 else wide2
    if j % 6 = 0 || (j % 6 = 1 && wide) then (3 : BitVec 2) else 2
  (List.range 16).map slot

private def reference (wide0 wide1 wide2 : Bool) : List Input :=
  (launchRaw wide0 wide1 wide2).map (fun raw => {rawInputs := raw})

private theorem reference_result (wide0 wide1 wide2 : Bool) :
    let data := reference wide0 wide1 wide2
    let last := run program armedReference data
    prelaunch armedReference data = true ∧
    last.phase = .boundary ∧ last.current = streamRow ∧ last.pc = 4 ∧ last.remaining.toNat = 576 ∧
    last.pins = txPins false ∧
    pinTrace program armedReference data = List.replicate 16 idlePins ++ [txPins false] := by
  cases wide0 <;> cases wide1 <;> cases wide2 <;> decide +kernel

private theorem trace_append (s : State a) (first rest : List Input) :
    pinTrace program s (first ++ rest) = (pinTrace program s first).take first.length ++
      pinTrace program (run program s first) rest := by
  induction first generalizing s with
  | nil => rfl
  | cons i tail ih => simp [pinTrace, run, ih]

/-- Starting on deasserted GO, a pre-arm interval of any length followed by
the canonical PHY clocks takes the enabled sender to its first reservation.
The last two pre-GO clocks have both raw inputs low, as they do before a
six-tick PHY rising edge of width at most two. -/
theorem synchronized_start (before : State 1) (start : Input) (early : List Input) (idle0 idle1 : Input)
    (wave : List Input) (wide0 wide1 wide2 : Bool)
    (count : start.startCount = 576) (startLow : start.rawInputs[1] = false)
    (runtime : ∀ i ∈ (early ++ [idle0, idle1]) ++ wave, i.Runtime)
    (preGO : ∀ i ∈ early ++ [idle0, idle1], i.rawInputs[1] = false)
    (last0 : idle0.rawInputs = 0) (last1 : idle1.rawInputs = 0)
    (waveEq : wave.map (·.rawInputs) = launchRaw wide0 wide1 wide2) :
    let alignment := (early ++ [idle0, idle1]) ++ wave
    let seed := before.start program start
    Boundary (run program seed alignment) 576 ∧
      pinTrace program seed alignment = List.replicate alignment.length idlePins ++ [txPins false] := by
  let idleInputs := early ++ [idle0, idle1]
  let seed := before.start program start
  let armed := run program seed idleInputs
  have idleRuntime : ∀ i ∈ idleInputs, i.Runtime :=
    fun i h => runtime i (List.mem_append_left _ h)
  have waveRuntime : ∀ i ∈ wave, i.Runtime :=
    fun i h => runtime i (List.mem_append_right _ h)
  have inert := arm_prefix before start idleInputs count (by simp [idleInputs]) startLow idleRuntime preGO
  have last0Runtime := idleRuntime idle0 (by simp [idleInputs])
  have last1Runtime := idleRuntime idle1 (by simp [idleInputs])
  have samplers := run_two_samples program seed early idle0 idle1 last0Runtime last1Runtime
  have s0 : armed.samplerFirst = 0 := samplers.1.trans last1
  have s1 : armed.samplerSecond = 0 := samplers.2.trans last0
  have same : erase armed = erase armedReference := by
    have arm : AwaitGo armed := inert.1
    simp [erase, arm.phase, arm.pc, arm.row, arm.count, arm.remaining, arm.pins, s0, s1, armedReference]
  have refRuntime : ∀ i ∈ reference wide0 wide1 wide2, i.Runtime := by
    intro i hit
    obtain ⟨raw, _, rfl⟩ := List.mem_map.mp hit
    exact ⟨rfl, show (0 : BitVec 4) ≠ 15 by decide⟩
  have rawEq : wave.map (·.rawInputs) = (reference wide0 wide1 wide2).map (·.rawInputs) := by
    simpa [reference, List.map_map, Function.comp_def] using waveEq
  have facts := reference_result wide0 wide1 wide2
  have transferred := paired armed armedReference wave _ same waveRuntime refRuntime rawEq facts.1
  let endState := run program armed wave
  have copy := transferred.1
  have location : Boundary endState 576 := by
    constructor
    · exact (congrArg State.phase copy).trans facts.2.1
    · exact (congrArg State.current copy).trans facts.2.2.1
    · exact (congrArg State.pc copy).trans facts.2.2.2.1
    · exact (congrArg (fun s : State 1 => s.remaining.toNat) copy).trans facts.2.2.2.2.1
    · decide
    · exact (congrArg State.pins copy).trans facts.2.2.2.2.2.1
  have waveSize : wave.length = 16 := by
    simpa only [List.length_map, launchRaw, List.length_range] using congrArg List.length waveEq
  change Boundary (run program seed (idleInputs ++ wave)) 576 ∧ _
  refine ⟨?_, ?_⟩
  · rw [show run program seed (idleInputs ++ wave) = endState from List.foldl_append]
    exact location
  · rw [trace_append, inert.2, transferred.2, facts.2.2.2.2.2.2]
    rw [List.take_replicate, Nat.min_eq_left (Nat.le_succ idleInputs.length), ← List.append_assoc,
      List.replicate_append_replicate]
    simp only [idleInputs, List.length_append, waveSize]

end Pinwheel.Program.StreamingEthernetCore
