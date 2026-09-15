import Pinwheel.UART.Spec

/-! A finite-state UART transmitter with separate symbol and intra-symbol counters. -/

namespace Pinwheel.UART

/-- Captured byte, symbol index (start=0, data=1..8, stop=9), and cycle within the symbol. -/
inductive State (cfg : Config) where
  | idle
  | active (byte : BitVec 8) (symbol : Fin 10) (tick : Fin cfg.cycles)
  deriving DecidableEq, Repr

/-- Inputs sampled at a rising edge. Requests carry the byte to capture. -/
structure Input where
  reset : Bool := false
  request : Option (BitVec 8) := none
  deriving Repr

/-- State immediately after accepting a start request. -/
def initial (cfg : Config) (byte : BitVec 8) : State cfg :=
  .active byte 0 ⟨0, Nat.zero_lt_succ _⟩

/-- Combinational pin output, implemented independently of the frame array. -/
def pin {cfg : Config} : State cfg → Bool
  | .idle => true
  | .active byte symbol _ =>
    if symbol.val = 0 then false
    else if symbol.val = 9 then true
    else byte.getLsbD (symbol.val - 1)

/-- Whether a frame is in progress during the current clock interval. -/
def busy {cfg : Config} : State cfg → Bool
  | .idle => false
  | .active .. => true

/-- Advance one interval; rollover advances the symbol, and the last rollover halts. -/
def advance {cfg : Config} : State cfg → State cfg
  | .idle => .idle
  | .active byte symbol tick =>
    if ht : tick.val + 1 < cfg.cycles then
      .active byte symbol ⟨tick.val + 1, ht⟩
    else if hs : symbol.val + 1 < 10 then
      .active byte ⟨symbol.val + 1, hs⟩ ⟨0, Nat.zero_lt_succ _⟩
    else .idle

/-- Synchronous reset has priority; requests on every busy edge are ignored. -/
def step {cfg : Config} (state : State cfg) (input : Input) : State cfg :=
  if input.reset then .idle
  else match state with
    | .idle => match input.request with
      | none => .idle
      | some byte => initial cfg byte
    | .active .. => advance state

/-- Quiet execution after acceptance: no reset or subsequent accepted request. -/
def run {cfg : Config} (state : State cfg) : Nat → State cfg
  | 0 => state
  | n + 1 => advance (run state n)

/-- Relate a concrete pair of counters to elapsed time in the protocol contract. -/
def Represents (cfg : Config) (byte : BitVec 8) (cycle : Nat) (state : State cfg) : Prop :=
  if cycle < cfg.frameCycles then
    ∃ symbol tick, state = .active byte symbol tick ∧
      cycle = symbol.val * cfg.cycles + tick.val
  else state = .idle

/-- Counter ranges are finite and the duration is always positive. -/
theorem cycles_bounds (cfg : Config) : 1 ≤ cfg.cycles ∧ cfg.cycles ≤ 256 := by
  have h := cfg.durationMinusOne.isLt
  change 1 ≤ cfg.durationMinusOne.val + 1 ∧ cfg.durationMinusOne.val + 1 ≤ 256
  omega

/-- One machine transition advances the represented protocol time by one cycle. -/
theorem represents_advance (cfg : Config) (byte : BitVec 8) (cycle : Nat)
    (state : State cfg) (h : Represents cfg byte cycle state) :
    Represents cfg byte (cycle + 1) (advance state) := by
  have symbol_bound (symbol : Fin 10) :
      (symbol.val + 1) * cfg.cycles ≤ cfg.frameCycles :=
    Nat.mul_le_mul_right cfg.cycles symbol.isLt
  have next_symbol_bound (symbol : Fin 10) (hs : symbol.val + 1 < 10) :
      (symbol.val + 2) * cfg.cycles ≤ cfg.frameCycles :=
    Nat.mul_le_mul_right cfg.cycles hs
  grind [Represents, advance, Config.frameCycles]

/-- An accepted start begins at symbol zero, cycle zero. -/
theorem represents_initial (cfg : Config) (byte : BitVec 8) :
    Represents cfg byte 0 (initial cfg byte) := by
  simp [Represents, initial, Config.frameCycles, Config.cycles]
  exact ⟨0, ⟨0, Nat.zero_lt_succ _⟩, rfl, by simp⟩

/-- Every elapsed cycle of quiet execution has the specified counter interpretation. -/
theorem run_represents (cfg : Config) (byte : BitVec 8) (cycle : Nat) :
    Represents cfg byte cycle (run (initial cfg byte) cycle) :=
  Nat.recOn cycle (represents_initial cfg byte)
    (fun n ih => represents_advance cfg byte n (run (initial cfg byte) n) ih)

/-- The implementation's pin selection agrees with the independent frame array. -/
theorem pin_symbol (cfg : Config) (byte : BitVec 8) (symbol : Fin 10)
    (tick : Fin cfg.cycles) :
    pin (.active byte symbol tick) = (frame byte).getD symbol.val true := by
  have h : symbol.val = 0 ∨ symbol.val = 1 ∨ symbol.val = 2 ∨ symbol.val = 3 ∨
      symbol.val = 4 ∨ symbol.val = 5 ∨ symbol.val = 6 ∨ symbol.val = 7 ∨
      symbol.val = 8 ∨ symbol.val = 9 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h
  all_goals simp [pin, frame, Array.getD, h]

/-- Counter decomposition selects exactly the intended protocol symbol. -/
theorem counter_symbol (cfg : Config) (symbol : Fin 10) (tick : Fin cfg.cycles) :
    (symbol.val * cfg.cycles + tick.val) / cfg.cycles = symbol.val := by
  simpa only [Nat.add_comm (symbol.val * cfg.cycles) tick.val,
    Nat.div_eq_of_lt tick.isLt, Nat.zero_add] using
    Nat.add_mul_div_right tick.val symbol.val
      (show 0 < cfg.cycles from Nat.zero_lt_succ _)

/-- A state representing a protocol cycle drives the independently specified level. -/
theorem represented_pin (cfg : Config) (byte : BitVec 8) (cycle : Nat)
    (state : State cfg) (h : Represents cfg byte cycle state) :
    pin state = expected cfg byte cycle := by
  have after_frame : cfg.frameCycles ≤ cycle → 10 ≤ cycle / cfg.cycles :=
    fun h => (Nat.le_div_iff_mul_le (show 0 < cfg.cycles from Nat.zero_lt_succ _)).2 h
  grind [Represents, expected, pin_symbol, counter_symbol, frame_size, pin]

/-- All bytes, supported bit durations, and elapsed cycles match the UART specification. -/
theorem waveform_correct (cfg : Config) (byte : BitVec 8) (cycle : Nat) :
    pin (run (initial cfg byte) cycle) = expected cfg byte cycle :=
  represented_pin cfg byte cycle _ (run_represents cfg byte cycle)

/-- At and after the exact frame boundary, quiet execution is idle. -/
theorem run_complete (cfg : Config) (byte : BitVec 8) (cycle : Nat)
    (h : cfg.frameCycles ≤ cycle) : run (initial cfg byte) cycle = .idle := by
  simpa [Represents, Nat.not_lt.mpr h] using run_represents cfg byte cycle

/-- Idle drives a high line. -/
theorem idle_high (cfg : Config) : pin (State.idle : State cfg) = true := rfl

/-- Reset aborts every state and overrides a simultaneous request. -/
theorem reset_dominates (cfg : Config) (state : State cfg) (request : Option (BitVec 8)) :
    step state ⟨true, request⟩ = .idle := rfl

/-- An idle request captures its byte and starts the frame immediately after the edge. -/
theorem start_accepted (cfg : Config) (byte : BitVec 8) :
    step (.idle : State cfg) ⟨false, some byte⟩ = initial cfg byte := rfl

/-- Requests while busy cannot replace the captured byte, even on the completion edge. -/
theorem busy_request_ignored (cfg : Config) (byte : BitVec 8) (symbol : Fin 10)
    (tick : Fin cfg.cycles) (request : Option (BitVec 8)) :
    step (.active byte symbol tick) ⟨false, request⟩ = advance (.active byte symbol tick) := rfl

/-- A new byte can be accepted on the edge after completion. -/
theorem restart_after_completion (cfg : Config) (first next : BitVec 8) :
    step (run (initial cfg first) cfg.frameCycles) ⟨false, some next⟩ = initial cfg next :=
  congrArg (fun state => step state ⟨false, some next⟩)
    (run_complete cfg first cfg.frameCycles (Nat.le_refl _))

/-- Quiet edge inputs implement exactly the transition used in the waveform theorem. -/
theorem quiet_step (cfg : Config) (state : State cfg) :
    step state ⟨false, none⟩ = advance state :=
  match state with
  | .idle => rfl
  | .active .. => rfl

/-- Every cycle within a symbol interval has that symbol's specified pin level. -/
theorem symbol_interval (cfg : Config) (byte : BitVec 8) (symbol : Fin 10)
    (tick : Fin cfg.cycles) :
    pin (run (initial cfg byte) (symbol.val * cfg.cycles + tick.val)) =
      (frame byte).getD symbol.val true :=
  (waveform_correct cfg byte _).trans
    (congrArg (fun index => (frame byte).getD index true) (counter_symbol cfg symbol tick))

/-- Busy stays asserted for exactly ten bit intervals, with no early completion. -/
theorem busy_exact (cfg : Config) (byte : BitVec 8) (cycle : Nat) :
    busy (run (initial cfg byte) cycle) = decide (cycle < cfg.frameCycles) := by
  grind [run_represents, Represents, busy]

end Pinwheel.UART
