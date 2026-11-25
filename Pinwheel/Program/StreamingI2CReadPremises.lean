import Pinwheel.Program.StreamingI2CReadWitness

/-! The checked scenario satisfies each source-level premise of the I²C
read-completion theorem. Loop facts are proved for an arbitrary starting loop by
forward induction; `checked` supplies the finite facts up to `settle`, and the
loop is a fixed point from there on. -/
namespace Pinwheel.Program.StreamingI2CReadWitness
open Pinwheel Pinwheel.Program.StreamingReady

/-! ### Loop runs -/

theorem runLoop_succ (n : Nat) (l : Loop) : runLoop (n+1) l = (runLoop n l).step := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => exact ih l.step

theorem runLoop_add (m n : Nat) (l : Loop) : runLoop (m+n) l = runLoop n (runLoop m l) := by
  induction m generalizing l with
  | zero => simp [runLoop]
  | succ m ih => rw [Nat.add_right_comm]; exact ih l.step

/-- The pins the loop produces from `l`, as the service theorem's traffic. -/
def trafficOf (l : Loop) (k : Nat) : Session.Pins := (runLoop k l).pin

/-- The engine inputs the loop produces, in order. -/
def inputsOf : Nat → Loop → List Input
  | 0, _ => []
  | n+1, l => (l.s.command l.pin).runtime :: inputsOf n l.step

theorem clocks_succ (l : Loop) (n : Nat) :
    SessionService.clocks (trafficOf l) (n+1) = l.pin :: SessionService.clocks (trafficOf l.step) n := by
  simp only [SessionService.clocks, List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem run_clocks (l : Loop) (n : Nat) :
    l.s.run program false (SessionService.clocks (trafficOf l) n) = (runLoop n l).s := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => rw [clocks_succ]; exact ih l.step

theorem runtimeInputs_clocks (l : Loop) (n : Nat) :
    l.s.runtimeInputs program false (SessionService.clocks (trafficOf l) n) = inputsOf n l := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [clocks_succ]
    exact congrArg (_ :: ·) (ih l.step)

theorem run_inputsOf (l : Loop) (n : Nat) : run program l.s.core (inputsOf n l) = (runLoop n l).s.core := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => exact ih l.step

theorem inputsOf_length (l : Loop) (n : Nat) : (inputsOf n l).length = n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => simp [inputsOf, ih]

theorem inputsOf_take (l : Loop) {t n : Nat} (le : t ≤ n) : (inputsOf n l).take t = inputsOf t l := by
  induction t generalizing l n with
  | zero => rfl
  | succ t ih =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [inputsOf, List.take_succ_cons]
      rw [ih l.step (by omega : t ≤ n)]

theorem inputsOf_get (l : Loop) {t n : Nat} (lt : t < n) :
    (inputsOf n l)[t]? = some (((runLoop t l).s.command (runLoop t l).pin).runtime) := by
  induction t generalizing l n with
  | zero => cases n with
    | zero => omega
    | succ n => rfl
  | succ t ih => cases n with
    | zero => omega
    | succ n => exact ih l.step (by omega)

/-- A clock that is not RESET, START or RELEASE appends its accepted bits; when
they are the next slice of the host plan, the trace stays the plan's prefix. -/
theorem accepted_step (l : Loop) (tr : BitTrace)
    (h : tr.accepted = StreamingI2CRead.hostBits.take l.accepted)
    (run : runtimeOK l = true) (slice : acceptedOK l = true) :
    (StreamingReady.BitTrace.step tr l.s.core (l.s.command l.pin).runtime).accepted =
      StreamingI2CRead.hostBits.take l.step.accepted := by
  simp only [runtimeOK, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at run
  obtain ⟨⟨⟨⟨⟨init, c15⟩, -⟩, -⟩, c4⟩, c3⟩ := run
  simp only [acceptedOK, beq_iff_eq] at slice
  rw [StreamingReady.BitTrace.step, if_neg (by simp [init]), if_neg (by simpa using c15),
    if_neg (by intro h; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact c3 h.1),
    if_neg (by intro h; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact c4 h.1)]
  show tr.accepted ++ _ = StreamingI2CRead.hostBits.take
    (l.accepted + (l.s.core.acceptedBits (l.s.command l.pin).runtime).length)
  rw [List.take_add, ← slice, h]

theorem accepted_run (l : Loop) (tr : BitTrace) (n : Nat)
    (h : tr.accepted = StreamingI2CRead.hostBits.take l.accepted)
    (ok : ∀ k < n, runtimeOK (runLoop k l) = true ∧ acceptedOK (runLoop k l) = true) :
    (l.s.traceRun program false tr (SessionService.clocks (trafficOf l) n)).accepted =
      StreamingI2CRead.hostBits.take (runLoop n l).accepted := by
  induction n generalizing l tr with
  | zero => exact h
  | succ n ih =>
    rw [clocks_succ]
    exact ih l.step _ (accepted_step l tr h (ok 0 (by omega)).1 (ok 0 (by omega)).2)
      (fun k lt => ok (k+1) (by omega))

/-- Captures among the states before each input. -/
def capCount (s : State 1) : List Input → Nat
  | [] => 0
  | i :: rest => (if s.captures then 1 else 0) + capCount (step program i s) rest

theorem captures_inputsOf (l : Loop) (n : Nat) :
    (runLoop n l).captures = l.captures + capCount l.s.core (inputsOf n l) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    change (runLoop n l.step).captures = _
    rw [ih l.step]
    simp only [Loop.step, inputsOf, capCount]
    change _ + capCount (l.s.step program false l.pin).core _ = _
    simp only [Session.State.step]
    omega

theorem raw2_eq (l : Loop) (t : Nat) : (runLoop (t+2) l).raw2 = (runLoop t l).pin.rawInputs := by
  rw [runLoop_succ, runLoop_succ]; rfl

theorem peer2_eq (l : Loop) (t : Nat) : (runLoop (t+2) l).peer2 = (runLoop t l).peer := by
  rw [runLoop_succ, runLoop_succ]; rfl

/-! ### Qualified captures -/

theorem qualified_at (s : State 1) (inputs : List Input) (k : Nat) (q : State 1)
    (h : (StreamingI2CTrace.Profiled.qualifiedStates profile s inputs)[k]? = some q) :
    ∃ t, t < inputs.length ∧ q = run program s (inputs.take t) ∧ q.captures = true ∧
      capCount s (inputs.take t) = k := by
  induction inputs generalizing s k with
  | nil => simp [StreamingI2CTrace.Profiled.qualifiedStates] at h
  | cons i rest ih =>
    unfold StreamingI2CTrace.Profiled.qualifiedStates at h
    cases hc : s.captures
    · simp only [hc] at h
      obtain ⟨t, lt, eq, cap, count⟩ := ih (step program i s) k h
      refine ⟨t+1, by simp; omega, eq, cap, ?_⟩
      simp [capCount, hc, count]
    · simp only [hc, if_true] at h
      cases k with
      | zero =>
        simp only [List.singleton_append, List.getElem?_cons_zero, Option.some.injEq] at h
        exact ⟨0, by simp, by simp [run, h], h ▸ hc, rfl⟩
      | succ k =>
        simp only [List.singleton_append, List.getElem?_cons_succ] at h
        obtain ⟨t, lt, eq, cap, count⟩ := ih (step program i s) k h
        refine ⟨t+1, by simp; omega, eq, cap, ?_⟩
        simp [capCount, hc, count]; omega

/-! ### The checked execution -/

theorem scan_fst (n t : Nat) (l : Loop) : (scan n t l).1 = runLoop n l := by
  induction n generalizing t l with
  | zero => rfl
  | succ n ih => exact ih (t+1) l.step

theorem scan_good (n t : Nat) (l : Loop) (h : (scan n t l).2 = true) :
    ∀ k < n, good (t+k) (runLoop k l) = true := by
  induction n generalizing t l with
  | zero => intro k lt; omega
  | succ n ih =>
    simp only [scan, Bool.and_eq_true] at h
    intro k lt
    cases k with
    | zero => exact h.1
    | succ k =>
      have := ih (t+1) l.step h.2 k (by omega)
      rwa [show t + 1 + k = t + (k+1) by omega] at this

theorem settled_eq : (scan settle 0 origin).1 = settled := scan_fst _ _ _

theorem fixed (n : Nat) (le : settle ≤ n) : runLoop n origin = settled := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le le
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, runLoop_succ, ih (by omega)]
    exact settled_fixed

theorem good_at (t : Nat) : good t (runLoop t origin) = true := by
  by_cases lt : t < settle
  · simpa using scan_good settle 0 origin scan_ok t lt
  · rw [fixed t (by omega)]
    have h := settled_good
    have two : 2 ≤ t := by unfold settle at lt; omega
    have done : completion ≤ t := by unfold settle completion at *; omega
    have twoS : 2 ≤ settle := by decide
    have doneS : completion ≤ settle := by decide
    simp only [good, deadlineOK, captureOK, two, done, twoS, doneS, decide_true, Bool.true_and,
      Bool.true_or, Bool.and_true] at h ⊢
    exact h

theorem good_parts {t : Nat} {l : Loop} (h : good t l = true) :
    runtimeOK l = true ∧ framingOK l = true ∧ deadlineOK t l = true ∧ captureOK t l = true ∧
      acceptedOK l = true ∧ (completion ≤ t ∨ l.s.core.phase ≠ .completed) := by
  simp only [good, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨r, f⟩, d⟩, c⟩, a⟩, done⟩ := h
  exact ⟨r, f, d, c, a, done⟩

/-! ### Premises -/

theorem origin_accepted : origin.accepted = 0 := rfl

/-- `hostPrefix`: the accepted bits are always a prefix of the host plan. -/
theorem hostPrefix (edges : Nat) :
    (origin.s.traceRun program false {} (SessionService.clocks traffic edges)).accepted
      <+: StreamingI2CRead.hostBits := by
  rw [show traffic = trafficOf origin from rfl,
    accepted_run origin {} edges (by rw [origin_accepted]; rfl)
      (fun k _ => ⟨(good_parts (good_at k)).1, (good_parts (good_at k)).2.2.2.2.1⟩)]
  exact List.take_prefix _ _

/-! ### Session runs of the loop -/

theorem inputsOf_add (m n : Nat) (l : Loop) :
    inputsOf (m + n) l = inputsOf m l ++ inputsOf n (runLoop m l) := by
  induction m generalizing l with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih =>
    rw [Nat.add_right_comm]
    change _ :: inputsOf (m + n) l.step = _ :: (inputsOf m l.step ++ _)
    rw [ih l.step]; rfl

/-- A prefix of the loop's engine inputs ends at the loop state of that length. -/
theorem prefix_run {edges : Nat} {earlier rest : List Input} {clock : Input}
    (h : inputsOf edges origin = earlier ++ clock :: rest) :
    earlier.length < edges ∧ run program origin.s.core earlier = (runLoop earlier.length origin).s.core := by
  have len : earlier.length < edges := by
    have := congrArg List.length h
    simp only [inputsOf_length, List.length_append, List.length_cons] at this
    omega
  refine ⟨len, ?_⟩
  have take : (inputsOf edges origin).take earlier.length = earlier := by rw [h]; simp
  conv => lhs; rw [← take]
  rw [inputsOf_take origin (Nat.le_of_lt len), run_inputsOf]

/-- Pins the loop produces from `l` are ordinary runtime commands other than
RELEASE whenever each clock passes `runtimeOK`. -/
theorem runtimeTrace_loop (l : Loop) (n : Nat) (ok : ∀ k < n, runtimeOK (runLoop k l) = true) :
    Session.RuntimeTrace program false l.s (SessionService.clocks (trafficOf l) n) ∧
      ∀ i ∈ l.s.runtimeInputs program false (SessionService.clocks (trafficOf l) n), i.command ≠ 4#4 := by
  induction n generalizing l with
  | zero => exact ⟨trivial, by simp [SessionService.clocks, Session.State.runtimeInputs]⟩
  | succ n ih =>
    have h := ok 0 (by omega)
    simp only [runtimeOK, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨⟨⟨init, c15⟩, c1⟩, c2⟩, c4⟩, -⟩ := h
    obtain ⟨trace, unreleased⟩ := ih l.step (fun k lt => ok (k+1) (by omega))
    rw [clocks_succ]
    refine ⟨⟨⟨init, c15, c1, c2⟩, trace⟩, ?_⟩
    intro i mem
    simp only [Session.State.runtimeInputs, List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact c4
    · exact unreleased i mem

/-- A drain that `ordinary` accepts is a runtime trace with no RELEASE. -/
theorem ordinary_sound (s : Session.State 1) (ps : List Session.Pins) (h : ordinary s ps = true) :
    Session.RuntimeTrace program false s ps ∧ ∀ i ∈ s.runtimeInputs program false ps, i.command ≠ 4#4 := by
  induction ps generalizing s with
  | nil => exact ⟨trivial, by simp [Session.State.runtimeInputs]⟩
  | cons p rest ih =>
    simp only [ordinary, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨⟨⟨init, c15⟩, c1⟩, c2⟩, c4⟩, tail⟩ := h
    obtain ⟨trace, unreleased⟩ := ih _ tail
    refine ⟨⟨⟨init, c15, c1, c2⟩, trace⟩, ?_⟩
    intro i mem
    simp only [Session.State.runtimeInputs, List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact c4
    · exact unreleased i mem

theorem runtimeInputs_append (s : Session.State 1) (xs ys : List Session.Pins) :
    s.runtimeInputs program false (xs ++ ys) =
      s.runtimeInputs program false xs ++ (s.run program false xs).runtimeInputs program false ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons p rest ih => exact congrArg (_ :: ·) (ih _)

theorem run_append (s : Session.State 1) (xs ys : List Session.Pins) :
    s.run program false (xs ++ ys) = (s.run program false xs).run program false ys := by
  simp [Session.State.run, List.foldl_append]

/-! ### The service premises -/

theorem state_eq (n : Nat) :
    SessionService.state program false origin.s traffic n = (runLoop n origin).s := by
  rw [SessionService.state_eq_run]; exact run_clocks origin n

theorem coreInputs_eq (n : Nat) : SessionService.coreInputs program false origin.s traffic n =
    ((runLoop n origin).s.command (runLoop n origin).pin).runtime := by
  unfold SessionService.coreInputs; rw [state_eq]; rfl

theorem atClock_eq (n : Nat) : StreamingI2CService.Profiled.atClock profile origin.s.core
    (SessionService.coreInputs program false origin.s traffic) n = (runLoop n origin).s.core := by
  change EventualService.state program origin.s.core _ n = _
  rw [← SessionService.core_state, state_eq]

/-- `runtime`: every host pin is an ordinary runtime command. -/
theorem runtime : SessionService.Runtime program false origin.s traffic := by
  intro n
  rw [state_eq]
  exact (runtimeTrace_loop (runLoop n origin) 1 (fun k lt => by
    obtain rfl : k = 0 := by omega
    exact (good_parts (good_at n)).1)).1.1

/-- `unreleased`: the host never sends RELEASE during the frame. -/
theorem unreleased (n : Nat) :
    (SessionService.coreInputs program false origin.s traffic n).command ≠ 4#4 := by
  have h := (good_parts (good_at n)).1
  simp only [runtimeOK, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  rw [coreInputs_eq]
  exact h.1.2

/-- `credits`: from `settle` on, the engine can always reserve. -/
theorem credits (n : Nat) :
    ∃ m, n ≤ m ∧ (SessionService.state program false origin.s traffic m).core.canReserve = true :=
  ⟨max n settle, Nat.le_max_left _ _, by
    rw [state_eq, fixed _ (Nat.le_max_right _ _)]; exact settled_reserve⟩

/-- `deadlines`: at each last guard poll the sample from two clocks earlier is ready. -/
theorem deadlines : StreamingI2CService.Profiled.MeetsDeadlines profile origin.s.core
    (SessionService.coreInputs program false origin.s traffic) peer := by
  intro k waiting zero
  rw [atClock_eq] at waiting zero ⊢
  have h := (good_parts (good_at k)).2.2.1
  simp only [deadlineOK, waiting, zero, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at h
  obtain ⟨two, ready⟩ := h.resolve_left (by decide)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [show j + 2 - 2 = j by omega, atClock_eq]
  rw [raw2_eq] at ready
  exact ready

theorem inputs_eq (edges : Nat) :
    origin.s.runtimeInputs program false (SessionService.clocks traffic edges) = inputsOf edges origin :=
  runtimeInputs_clocks origin edges

/-- `peerSetup`: the target drives each captured slot from its payload two
clocks before the capture, and releases at START and STOP. -/
theorem peerSetup (edges : Nat) : StreamingI2CTrace.Profiled.ReadPeer profile origin.s.core
    (origin.s.runtimeInputs program false (SessionService.clocks traffic edges)) payload peer := by
  rw [inputs_eq]
  constructor
  · intro k q hq
    obtain ⟨t, lt, rfl, cap, count⟩ := qualified_at _ _ k q hq
    rw [inputsOf_length] at lt
    rw [inputsOf_take origin (Nat.le_of_lt lt)] at cap count ⊢
    rw [run_inputsOf] at cap
    have c := (good_parts (good_at t)).2.2.2.1
    simp only [captureOK, cap, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at c
    obtain ⟨two, setup⟩ := c
    have caps : (runLoop t origin).captures = k := by
      rw [captures_inputsOf, count]; simp [origin]
    obtain ⟨j, rfl⟩ : ∃ j, t = j + 2 := ⟨t - 2, by omega⟩
    rw [caps, peer2_eq] at setup
    obtain ⟨n, rfl⟩ : ∃ n, edges = j + 2 + n := ⟨edges - (j + 2), by omega⟩
    have pair : inputsOf 2 (runLoop j origin) =
        [((runLoop j origin).s.command (runLoop j origin).pin).runtime,
          ((runLoop (j+1) origin).s.command (runLoop (j+1) origin).pin).runtime] := by
      rw [runLoop_succ]; rfl
    refine ⟨inputsOf j origin, ((runLoop j origin).s.command (runLoop j origin).pin).runtime,
      ((runLoop (j+1) origin).s.command (runLoop (j+1) origin).pin).runtime,
      inputsOf n (runLoop (j+2) origin), false, ?_, ?_, ?_⟩
    · rw [inputsOf_add, inputsOf_add j 2, pair]; simp
    · rw [inputsOf_add j 2, pair]; rfl
    · rw [inputsOf_length]; exact setup
  · intro earlier clock rest h edge
    obtain ⟨_, hrun⟩ := prefix_run h
    rw [show StreamingI2CTrace.Profiled.program profile = program from rfl, hrun] at edge
    have f := (good_parts (good_at earlier.length)).2.1
    have fr : framing (runLoop earlier.length origin).s.core = true := by
      rcases edge with ⟨ph, pc⟩ | ⟨ph, pc⟩ <;> simp [framing, ph, pc]
    simp only [framingOK, fr, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at f
    exact f.1.1

/-- The drain service: from any completed cut, the loop's own traffic up to
`settle` and then the checked drain reach an admissible RELEASE. -/
theorem drainService (edges : Nat)
    (_completed : (origin.s.run program false (SessionService.clocks traffic edges)).core.phase = .completed) :
    let cut := origin.s.run program false (SessionService.clocks traffic edges)
    ∃ (drain : List Session.Pins) (releasePin : Session.Pins),
      let final := cut.run program false drain
      Session.RuntimeTrace program false cut drain ∧
      (∀ i ∈ cut.runtimeInputs program false drain, i.command ≠ 4#4) ∧
      Session.RuntimeInput final releasePin ∧
      (final.command releasePin).runtime.command = 4#4 ∧
      final.core.canRelease (final.command releasePin).runtime = true := by
  intro cut
  have cutEq : cut = (runLoop edges origin).s := run_clocks origin edges
  let l := runLoop edges origin
  let slice := SessionService.clocks (trafficOf l) (settle - edges)
  have reach : (runLoop (settle - edges) l) = settled := by
    rw [← runLoop_add]; exact fixed _ (by omega)
  have sliceRun : l.s.run program false slice = settled.s := by
    rw [run_clocks, reach]
  have sliceOK := runtimeTrace_loop l (settle - edges) (fun k _ => by
    rw [← runLoop_add]; exact (good_parts (good_at _)).1)
  have drain := settled_drain
  simp only [drainOK, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at drain
  obtain ⟨⟨⟨ord, init⟩, four⟩, release⟩ := drain
  obtain ⟨drainTrace, drainUnreleased⟩ := ordinary_sound _ _ ord
  refine ⟨slice ++ drainPins settled.s, releasePin settled.s, ?_⟩
  intro final
  have finalEq : final = settled.s.run program false (drainPins settled.s) := by
    change cut.run program false _ = _
    rw [cutEq, run_append, sliceRun]
  rw [finalEq]
  refine ⟨?_, ?_, ⟨init, by rw [four]; decide, by rw [four]; decide, by rw [four]; decide⟩, four, release⟩
  · rw [cutEq]
    exact (SessionService.runtimeTrace_append program false _ _ _).mpr
      ⟨sliceOK.1, by rw [sliceRun]; exact drainTrace⟩
  · rw [cutEq, runtimeInputs_append]
    intro i mem
    rcases List.mem_append.mp mem with mem | mem
    · exact sliceOK.2 i mem
    · rw [sliceRun] at mem; exact drainUnreleased i mem

/-! ### Before START -/

/-- An ordinary session input: not RESET, and not command 15, 1 or 2. -/
def sessionOK (l : Loop) : Bool :=
  let c := (l.s.command l.pin).runtime
  !c.initialize && c.command != 15 && c.command != 1 && c.command != 2

def allSession : Nat → Loop → Bool
  | 0, _ => true
  | n+1, l => sessionOK l && allSession n l.step

abbrev startLoop : Loop := runLoop startCut initialLoop

/-- The clocks before START are ordinary, and START is admitted for 585 bits. -/
def preStart : Bool :=
  let c := (startLoop.s.command startLoop.pin).runtime
  allSession startCut initialLoop && sessionOK startLoop && c.command == 3 &&
    startLoop.s.core.canStart c && c.startCount == 585

set_option maxRecDepth 100000 in
theorem preStart_ok : preStart = true := by decide +kernel

theorem sessionOK_input {l : Loop} (h : sessionOK l = true) : Session.RuntimeInput l.s l.pin := by
  simp only [sessionOK, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem allSession_trace (l : Loop) (n : Nat) (h : allSession n l = true) :
    Session.RuntimeTrace program false l.s (SessionService.clocks (trafficOf l) n) := by
  induction n generalizing l with
  | zero => trivial
  | succ n ih =>
    simp only [allSession, Bool.and_eq_true] at h
    rw [clocks_succ]
    exact ⟨sessionOK_input h.1, ih l.step h.2⟩

theorem preStart_parts :
    Session.RuntimeTrace program false initialLoop.s (SessionService.clocks (trafficOf initialLoop) startCut) ∧
    Session.RuntimeInput startLoop.s startLoop.pin ∧
    (startLoop.s.command startLoop.pin).runtime.command = 3 ∧
    startLoop.s.core.canStart (startLoop.s.command startLoop.pin).runtime = true ∧
    (startLoop.s.command startLoop.pin).runtime.startCount = 585 := by
  have h := preStart_ok
  simp only [preStart, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨all, ok⟩, three⟩, can⟩, count⟩ := h
  exact ⟨allSession_trace _ _ all, sessionOK_input ok, three, can, count⟩

theorem origin_s : origin.s = startLoop.s.step program false startLoop.pin := by
  unfold origin; rw [runLoop_succ]; rfl

/-- The pin the engine sees on each loop clock carries the resolved bus. -/
theorem pinTrace_get (s : State 1) (inputs : List Input) (k : Nat) (inside : k ≤ inputs.length) :
    (pinTrace program s inputs)[k]? = some (run program s (inputs.take k)).pins := by
  induction inputs generalizing s k with
  | nil =>
    obtain rfl : k = 0 := by simpa using inside
    rfl
  | cons i rest ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih (step program i s) k (by simpa using inside)

end Pinwheel.Program.StreamingI2CReadWitness
