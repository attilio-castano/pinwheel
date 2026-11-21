import Pinwheel.I2C.RegisterRead

/-! A causal digital target for the combined register read. The target sees
    its own resolved bus and advances once per physical clock. Its output
    is chosen from the previous target state, before the bus is resolved. -/
namespace Pinwheel.I2C.RegisterReadPeer

open RegisterRead

/-- The target may refuse one of the three address/register bytes. It may
    hold SCL after the first observed fall for up to five following clocks.
    With the four-clock controller setup this adds at most two clocks of
    actual stretching. Other low intervals are edge reactive as usual. -/
structure Target where
  payload : BitVec 8
  nack : Option (Fin 3) := none
  initialStretch : Fin 6 := 0

def Target.stopAfter (target : Target) : Nat :=
  match target.nack with
  | none => 36
  | some stage => 9 * (stage.val + 1)

def Target.outcome (target : Target) : RegisterRead.Outcome :=
  match target.nack with
  | none => .success target.payload
  | some stage =>
    if stage.val == 0 then .writeAddressNack
    else if stage.val == 1 then .registerNack
    else .readAddressNack

structure State where
  previous : Bus := {}
  starts : Nat := 0
  slots : Nat := 0
  stopped : Bool := false
  left : Nat := 0
  sda : Drive := .release
  deriving DecidableEq, Repr

def initial : State := {}

def bitDrive (target : Target) (slot : Nat) : Drive :=
  if target.stopAfter ≤ slot then .release
  else if slot == 8 then if target.nack == some 0 then .release else .low
  else if slot == 17 then if target.nack == some 1 then .release else .low
  else if slot == 26 then if target.nack == some 2 then .release else .low
  else if 27 ≤ slot && slot < 35 then if target.payload.getLsbD (34 - slot) then .release else .low
  else .release

def drive (state : State) : Pins :=
  ⟨if state.left = 0 then .release else .low, state.sda⟩

def step (target : Target) (state : State) (bus : Bus) : State :=
  let fall := state.previous.scl && !bus.scl
  let rise := !state.previous.scl && bus.scl
  let start := state.previous.scl && bus.scl && state.previous.sda && !bus.sda
  let stop := state.previous.scl && bus.scl && !state.previous.sda && bus.sda
  let active := state.starts != 0 && !state.stopped
  let restart := state.slots == 18 && state.starts == 1
  let slot := rise && active && !restart && state.slots < target.stopAfter
  { previous := bus
    starts := state.starts + (if start then 1 else 0)
    slots := state.slots + (if slot then 1 else 0)
    stopped := state.stopped || (active && stop)
    left := if fall && active && state.starts == 1 && state.slots == 0 then
        target.initialStretch.val else state.left - 1
    sda := if fall && active then bitDrive target state.slots else state.sda }

/-- Once a stretch expires, a duplicate resolved low sample leaves the
    target unchanged. -/
theorem stationary_low (target : Target) (state : State) (bus : Bus)
    (low : bus.scl = false) (steady : state.previous = bus) (expired : state.left = 0) :
    step target state bus = state := by
  cases state
  simp_all [step]

abbrev Pair := RegisterRead.State × State

def bus (request : RegisterRead.Request) (state : Pair) : Bus :=
  resolve (pins request state.1.phase) (drive state.2)

def edge (cfg : Config) (request : RegisterRead.Request) (target : Target) (state : Pair) : Pair :=
  let b := bus request state
  ⟨RegisterRead.step cfg state.1 b, step target state.2 b⟩

def run (cfg : Config) (request : RegisterRead.Request) (target : Target) (state : Pair) : Nat → Pair
  | 0 => state
  | n + 1 => run cfg request target (edge cfg request target state) n

theorem run_add (cfg : Config) (request : RegisterRead.Request) (target : Target)
    (state : Pair) (left right : Nat) :
    run cfg request target state (left + right) =
      run cfg request target (run cfg request target state left) right := by
  induction left generalizing state with
  | zero => simp only [Nat.zero_add, run]
  | succ left ih => simpa only [Nat.succ_add, run] using ih (edge cfg request target state)

/-- The digital setup used by the retiming experiment. -/
def cfg : Config := ⟨3, 7⟩
def request : RegisterRead.Request := ⟨0x53, 0xA6⟩
def start : Pair := ⟨RegisterRead.initial cfg, initial⟩

/-- An oversized initial hold spends at most two extra clocks in the first
    rising wait. A shorter hold expires during ordinary setup. -/
def Target.extra (target : Target) : Nat := target.initialStretch.val - 3

def Target.firstDispatch (target : Target) : Nat := 124 + target.extra

def Target.completion (target : Target) : Nat :=
  (match target.nack with
  | none => 502
  | some stage => if stage.val = 0 then 138 else if stage.val = 1 then 255 else 385) + target.extra

def Target.startCount (target : Target) : Nat :=
  match target.nack with
  | none => 2
  | some stage => if stage.val < 2 then 1 else 2

def observe (target : Target) (clocks : Nat) : Pair := run cfg request target start clocks

private def payloadBlind (target : Target) (state : Pair) : Prop :=
  ¬ (state.2.previous.scl = true ∧ (bus request state).scl = false ∧
    state.2.starts ≠ 0 ∧ state.2.stopped = false) ∨
  target.stopAfter ≤ state.2.slots ∨ state.2.slots < 27 ∨ 35 ≤ state.2.slots

local instance (target : Target) (state : Pair) : Decidable (payloadBlind target state) := by
  unfold payloadBlind
  infer_instance

private def blindPrefix (target : Target) (state : Pair) : Nat → Bool
  | 0 => true
  | n + 1 => decide (payloadBlind target state) && blindPrefix target (edge cfg request target state) n

private theorem bitDrive_blind (target : Target) (slot : Nat) (byte : BitVec 8)
    (irrelevant : target.stopAfter ≤ slot ∨ slot < 27 ∨ 35 ≤ slot) :
    bitDrive {target with payload := byte} slot = bitDrive target slot := by
  have same : ({target with payload := byte}).stopAfter = target.stopAfter := rfl
  simp only [bitDrive, same]
  rcases irrelevant with stopped | beforeData | pastData
  · simp [stopped]
  · simp [show ¬ 27 ≤ slot by omega]
  · simp [show ¬ slot < 35 by omega]

private theorem edge_blind (target : Target) (state : Pair) (byte : BitVec 8)
    (blind : payloadBlind target state) :
    edge cfg request {target with payload := byte} state = edge cfg request target state := by
  rcases blind with quiet | irrelevant
  · have notSetting :
      (state.2.previous.scl && !(bus request state).scl && (state.2.starts != 0 && !state.2.stopped)) = false := by
      simpa [Bool.and_eq_false_imp, Bool.and_eq_true, Bool.not_eq_true, bne] using quiet
    simp [edge, step, Target.stopAfter, notSetting] <;> rfl
  · simp [edge, step, Target.stopAfter, bitDrive_blind target state.2.slots byte irrelevant] <;> rfl

private theorem run_blind (target : Target) (state : Pair) (byte : BitVec 8) (clocks : Nat)
    (blind : blindPrefix target state clocks = true) :
    run cfg request {target with payload := byte} state clocks = run cfg request target state clocks := by
  induction clocks generalizing state with
  | zero => rfl
  | succ clocks ih =>
    simp only [blindPrefix, Bool.and_eq_true, decide_eq_true_eq] at blind
    simp only [run, edge_blind target state byte blind.1]
    exact ih (edge cfg request target state) blind.2

private theorem blindPrefix_le (target : Target) (state : Pair) {long short : Nat}
    (bound : short ≤ long) (blind : blindPrefix target state long = true) :
    blindPrefix target state short = true := by
  induction long generalizing state short with
  | zero =>
    have empty : short = 0 := by omega
    subst short
    rfl
  | succ long ih =>
    cases short with
    | zero => rfl
    | succ short =>
      simp only [blindPrefix, Bool.and_eq_true] at blind ⊢
      exact ⟨blind.1, ih _ (by omega) blind.2⟩

private theorem stretch_cases (delay : Fin 6) :
    delay = 0 ∨ delay = 1 ∨ delay = 2 ∨ delay = 3 ∨ delay = 4 ∨ delay = 5 := by omega

private theorem nack_cases (nack : Option (Fin 3)) : nack = none ∨ nack = some 0 ∨ nack = some 1 ∨ nack = some 2 := by
  cases nack with
  | none => exact Or.inl rfl
  | some stage =>
    have branch : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
    simpa using branch

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem initial_blind (nack : Option (Fin 3)) (delay : Fin 6) :
    blindPrefix ⟨0, nack, delay⟩ start 134 = true := by
  rcases nack_cases nack with rfl | rfl | rfl | rfl <;>
    rcases stretch_cases delay with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

/-- All observations through the first ACK and its resumed edge are
    independent of the later data byte. -/
theorem prefix_payload_independent (target : Target) (clocks : Nat) (within : clocks ≤ 134) :
    observe target clocks = observe {target with payload := 0} clocks := by
  cases target with
  | mk payload nack delay =>
    exact run_blind ⟨0, nack, delay⟩ start payload clocks
      (blindPrefix_le _ _ within (initial_blind nack delay))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem firstDispatch_zero (nack : Option (Fin 3)) (delay : Fin 6) :
    let target : Target := ⟨0, nack, delay⟩
    let state := observe target target.firstDispatch
    state.1.phase = .fall 8 ∧ state.1.remaining = 0 ∧ state.2.slots = 9 ∧ state.2.starts = 1 ∧
    state.2.left = 0 ∧ state.2.previous = bus request state ∧ (bus request state).scl = false := by
  rcases nack_cases nack with rfl | rfl | rfl | rfl <;>
    rcases stretch_cases delay with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

/-- The bus itself leads to the stationary first-ACK dispatch cut, even
    when the target stretches its first bit or stops after a NACK. -/
theorem firstDispatch_spec (target : Target) :
    let state := observe target target.firstDispatch
    state.1.phase = .fall 8 ∧ state.1.remaining = 0 ∧ state.2.slots = 9 ∧ state.2.starts = 1 ∧
    state.2.left = 0 ∧ state.2.previous = bus request state ∧ (bus request state).scl = false := by
  dsimp only
  have bound : target.firstDispatch ≤ 134 := by
    have := target.initialStretch.isLt
    unfold Target.firstDispatch Target.extra
    omega
  rw [prefix_payload_independent target _ bound]
  exact firstDispatch_zero target.nack target.initialStretch

private def afterFirstAck : Phase → Prop
  | .free | .startHold => False
  | .setup slot | .rise slot | .high slot | .fall slot => 8 < slot.val
  | _ => True

private instance (phase : Phase) : Decidable (afterFirstAck phase) := by
  cases phase <;> unfold afterFirstAck <;> infer_instance

private theorem afterFirstAck_afterFall (samples : Vector Bool 16) (slot : Fin 36)
    (past : 8 < slot.val) : afterFirstAck (afterFall samples slot) := by
  unfold afterFall
  split
  · trivial
  · split
    · trivial
    · split
      · change 8 < slot.val + 1
        omega
      · trivial

private theorem afterFirstAck_step (cfg : Config) (state : RegisterRead.State) (wire : Bus)
    (past : afterFirstAck state.phase) : afterFirstAck (RegisterRead.step cfg state wire).phase := by
  cases phase : state.phase <;> simp [phase, afterFirstAck] at past
  all_goals
    simp only [RegisterRead.step, phase, timed, guarded, move, finish, count, blocked]
    repeat' first
      | exact past
      | exact afterFirstAck_afterFall _ _ past
      | trivial
      | exact (by decide : afterFirstAck (.setup 18))
      | split

private theorem afterFirstAck_run (target : Target) (state : Pair) (clocks : Nat)
    (past : afterFirstAck state.1.phase) :
    afterFirstAck (run cfg request target state clocks).1.phase := by
  induction clocks generalizing state with
  | zero => exact past
  | succ clocks ih => exact ih _ (afterFirstAck_step cfg state.1 (bus request state) past)

private def dispatch (state : Pair) : Bool :=
  state.1.phase == .fall 8 && state.1.remaining == 0

private def noDispatchPrefix (target : Target) (state : Pair) : Nat → Bool
  | 0 => true
  | n + 1 => !dispatch state && noDispatchPrefix target (edge cfg request target state) n

private theorem no_dispatch_before (target : Target) (state : Pair) (bound clocks : Nat)
    (within : clocks < bound) (checked : noDispatchPrefix target state bound = true) :
    dispatch (run cfg request target state clocks) = false := by
  induction clocks generalizing state bound with
  | zero =>
    cases bound with
    | zero => omega
    | succ bound =>
      simp only [noDispatchPrefix, Bool.and_eq_true] at checked
      change dispatch state = false
      cases h : dispatch state <;> simp_all
  | succ clocks ih =>
    cases bound with
    | zero => omega
    | succ bound =>
      simp only [noDispatchPrefix, Bool.and_eq_true] at checked
      exact ih _ bound (by omega) checked.2

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem dispatch_prefix_checked (nack : Option (Fin 3)) (delay : Fin 6) :
    let target : Target := ⟨0, nack, delay⟩
    noDispatchPrefix target start target.firstDispatch = true ∧
    afterFirstAck (observe target (target.firstDispatch + 1)).1.phase := by
  rcases nack_cases nack with rfl | rfl | rfl | rfl <;>
    rcases stretch_cases delay with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

/-- The first ACK can dispatch only once in any closed run of this target. -/
theorem firstDispatch_unique (target : Target) (clocks : Nat)
    (phase : (observe target clocks).1.phase = .fall 8)
    (remaining : (observe target clocks).1.remaining = 0) : clocks = target.firstDispatch := by
  have bound : target.firstDispatch + 1 ≤ 134 := by
    have := target.initialStretch.isLt
    unfold Target.firstDispatch Target.extra
    omega
  obtain earlier | atCut | later := Nat.lt_trichotomy clocks target.firstDispatch
  · have checked := (dispatch_prefix_checked target.nack target.initialStretch).1
    have prohibited := no_dispatch_before {target with payload := 0} start target.firstDispatch
      clocks earlier checked
    change dispatch (observe {target with payload := 0} clocks) = false at prohibited
    rw [← prefix_payload_independent target clocks (by omega)] at prohibited
    simp [dispatch, phase, remaining] at prohibited
  · exact atCut
  · have past := (dispatch_prefix_checked target.nack target.initialStretch).2
    change afterFirstAck (observe {target with payload := 0} (target.firstDispatch + 1)).1.phase at past
    rw [← prefix_payload_independent target (target.firstDispatch + 1) bound] at past
    have split : clocks = (target.firstDispatch + 1) + (clocks - (target.firstDispatch + 1)) := by omega
    have future := afterFirstAck_run target (observe target (target.firstDispatch + 1))
      (clocks - (target.firstDispatch + 1)) past
    change afterFirstAck (run cfg request target
      (run cfg request target start (target.firstDispatch + 1)) (clocks - (target.firstDispatch + 1))).1.phase at future
    rw [← run_add, ← split] at future
    change afterFirstAck (observe target clocks).1.phase at future
    rw [phase] at future
    change 8 < 8 at future
    omega

/-- The controller reaches its expected terminal outcome and the wire target
    observes the corresponding STOP, START count, and number of bit slots. -/
def Completes (target : Target) (state : Pair) : Prop :=
  RegisterRead.result state.1 = some target.outcome ∧ state.2.stopped = true ∧
    state.2.slots = target.stopAfter ∧ state.2.starts = target.startCount

private instance (target : Target) (state : Pair) : Decidable (Completes target state) := by
  unfold Completes
  infer_instance

-- The third ACK has been captured. The fall that introduces the first
-- data bit has yet to reach the target, so no payload bit has been read.
private def dataEntry : Pair :=
  ⟨⟨.fall 26, 3, 7, Vector.replicate 16 false⟩,
    { previous := ⟨true, false⟩, starts := 2, slots := 27, sda := .low }⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem data_entry_zero (delay : Fin 6) :
    let target : Target := ⟨0, none, delay⟩
    blindPrefix target start (368 + target.extra) = true ∧
      observe target (368 + target.extra) = dataEntry := by
  rcases stretch_cases delay with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem stretch_irrelevant_edge (target : Target) (state : Pair) (delay : Fin 6)
    (restarted : 2 ≤ state.2.starts) :
    edge cfg request {target with initialStretch := delay} state = edge cfg request target state := by
  have beyond : (state.2.starts == 1) = false := by simp [show state.2.starts ≠ 1 by omega]
  simp [edge, step, beyond, bitDrive, Target.stopAfter] <;> rfl

private theorem starts_nondecreasing (target : Target) (state : Pair) :
    state.2.starts ≤ (edge cfg request target state).2.starts := by
  change state.2.starts ≤ (step target state.2 (bus request state)).starts
  simp only [step]
  omega

private theorem stretch_irrelevant_run (target : Target) (state : Pair) (delay : Fin 6) (clocks : Nat)
    (restarted : 2 ≤ state.2.starts) :
    run cfg request {target with initialStretch := delay} state clocks =
      run cfg request target state clocks := by
  induction clocks generalizing state with
  | zero => rfl
  | succ clocks ih =>
    simp only [run, stretch_irrelevant_edge target state delay restarted]
    exact ih _ (Nat.le_trans restarted (starts_nondecreasing target state))

set_option maxRecDepth 16384 in
private theorem data_entry_restarted : 2 ≤ dataEntry.2.starts := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem data_tail : ∀ (payload : BitVec 8),
    let target : Target := ⟨payload, none, 0⟩
    Completes target (run cfg request target dataEntry 134) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem nack_completion_zero (stage : Fin 3) (delay : Fin 6) :
    let target : Target := ⟨0, some stage, delay⟩
    blindPrefix target start target.completion = true ∧ Completes target (observe target target.completion) := by
  have branch : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
  rcases branch with rfl | rfl | rfl <;>
    rcases stretch_cases delay with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

/-- Every payload, each possible first NACK, and all six initial hold
    lengths complete in closed loop on the baseline reference. -/
theorem baseline_correct (target : Target) : Completes target (observe target target.completion) := by
  rcases target with ⟨payload, _ | stage, delay⟩
  · have checked := data_entry_zero delay
    have reached : observe ⟨payload, none, delay⟩ (368 + (⟨payload, none, delay⟩ : Target).extra) = dataEntry :=
      (run_blind ⟨0, none, delay⟩ start payload _ checked.1).trans checked.2
    change Completes _ (run cfg request ⟨payload, none, delay⟩ start (502 + (⟨payload, none, delay⟩ : Target).extra))
    have split : 502 + (⟨payload, none, delay⟩ : Target).extra =
        (368 + (⟨payload, none, delay⟩ : Target).extra) + 134 := by omega
    rw [split, run_add]
    change Completes _ (run cfg request ⟨payload, none, delay⟩
      (observe ⟨payload, none, delay⟩ (368 + (⟨payload, none, delay⟩ : Target).extra)) 134)
    rw [reached, stretch_irrelevant_run ⟨payload, none, 0⟩ dataEntry delay 134 data_entry_restarted]
    exact data_tail payload
  · have checked := nack_completion_zero stage delay
    have same : observe ⟨payload, some stage, delay⟩ (⟨payload, some stage, delay⟩ : Target).completion =
        observe ⟨0, some stage, delay⟩ (⟨0, some stage, delay⟩ : Target).completion :=
      run_blind ⟨0, some stage, delay⟩ start payload _ checked.1
    rw [same]
    exact checked.2

end Pinwheel.I2C.RegisterReadPeer
