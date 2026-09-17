import Pinwheel.UART.RxFrames

namespace Pinwheel.UART.Rx.Stream

/-- Back-to-back 8N1 frames, each using the existing one-byte transmitter specification. -/
def wireBody (cfg : UART.Config) : List (BitVec 8) → Nat → Bool
  | [], _ => true
  | byte :: rest, n =>
    if n < cfg.frameCycles then UART.expected cfg byte n
    else wireBody cfg rest (n - cfg.frameCycles)

def wire (cfg : UART.Config) (start : Nat) (bytes : List (BitVec 8)) (n : Nat) : Bool :=
  if n < start then true else wireBody cfg bytes (n - start)

def idealTx (cfg : Config) (fits : cfg.bitCycles ≤ 256) : UART.Config := (UART.Link.ideal cfg fits 0).tx
def rearmGap (cfg : Config) : Nat := cfg.bitCycles - cfg.half - 1

def idealFrames (cfg : Config) (start : Nat) : List (BitVec 8) → List FrameSpec
  | [] => []
  | byte :: rest => ⟨start, byte⟩ :: idealFrames cfg (rearmGap cfg) rest

theorem rearmGap_two (cfg : Config) : 2 ≤ rearmGap cfg := by
  have minimum := cfg.minimum
  unfold rearmGap Config.half
  omega

theorem ideal_cycles (cfg : Config) (fits : cfg.bitCycles ≤ 256) :
    (idealTx cfg fits).cycles = cfg.bitCycles := by
  simp only [idealTx, UART.Link.ideal, UART.Config.cycles]
  have minimum := cfg.minimum
  omega

theorem wire_idle (cfg : UART.Config) (start : Nat) (bytes : List (BitVec 8)) (n : Nat)
    (before : n < start) : wire cfg start bytes n = true := if_pos before

theorem wire_symbol (cfg : UART.Config) (start : Nat) (byte : BitVec 8) (rest : List (BitVec 8))
    (n : Nat) (symbol : Fin 10) (lo : start + symbol.val * cfg.cycles ≤ n)
    (hi : n < start + (symbol.val + 1) * cfg.cycles) :
    wire cfg start (byte :: rest) n = (UART.frame byte).getD symbol.val true := by
  have endpoint := Nat.mul_le_mul_right cfg.cycles (show symbol.val + 1 ≤ 10 from by omega)
  have quotient : (n - start) / cfg.cycles = symbol.val :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  simp [wire, wireBody, show ¬ n < start from by omega,
    show n - start < cfg.frameCycles from by unfold UART.Config.frameCycles; omega,
    UART.expected, quotient]

theorem wire_shift (cfg : UART.Config) (start offset : Nat) (bytes : List (BitVec 8))
    (n : Nat) (before : offset ≤ start) :
    wire cfg start bytes (offset + n) = wire cfg (start - offset) bytes n := by
  simp [wire, show (offset + n < start) ↔ (n < start - offset) from by omega,
    show offset + n - start = n - (start - offset) from by omega]

theorem wire_stop_suffix (cfg : UART.Config) (start : Nat) (byte : BitVec 8)
    (rest : List (BitVec 8)) (n : Nat) (afterStop : start + 9 * cfg.cycles ≤ n) :
    wire cfg start (byte :: rest) n = wire cfg (start + cfg.frameCycles) rest n := by
  by_cases inside : n < start + cfg.frameCycles
  · rw [wire_symbol cfg start byte rest n 9 afterStop (by simpa [UART.Config.frameCycles,
        show (9 : Fin 10).val = 9 from rfl] using inside),
      wire_idle cfg (start + cfg.frameCycles) rest n inside]
    simp [UART.frame, Array.getD, show (9 : Fin 10).val = 9 from rfl]
  · simp [wire, wireBody, inside, show ¬ n < start from by omega,
      show ¬ n - start < cfg.frameCycles from by omega, Nat.sub_sub]

theorem wire_first_frame (cfg : Config) (fits : cfg.bitCycles ≤ 256)
    (start : Nat) (later : 2 ≤ start) (byte : BitVec 8) (rest : List (BitVec 8))
    (incoming : Nat → Input) (line : ∀ n, (incoming n).line = wire (idealTx cfg fits) start (byte :: rest) n)
    (quiet : ∀ n, (incoming n).reset = false) : Frame cfg incoming start byte := by
  have observations (symbol : Fin 10) :
      (incoming (start + cfg.half + symbol.val * cfg.bitCycles)).line =
        (UART.frame byte).getD symbol.val true := by
    rw [line]
    apply wire_symbol _ start byte rest _ symbol
    all_goals simp only [ideal_cycles, Nat.add_mul, Nat.one_mul, Config.half]
    all_goals have minimum := cfg.minimum
    all_goals omega
  refine ⟨later, (fun k _ before => (line k).trans (wire_idle _ _ _ k before)), ?_, ?_,
    ⟨(fun bit => (observations ⟨bit.val + 1, by omega⟩).trans (UART.Link.frame_data byte bit)), ?_⟩,
    (fun k _ _ => quiet k)⟩
  case refine_1 => simp [line, wire, wireBody, UART.expected, UART.frame, Array.getD,
    UART.Config.frameCycles, UART.Config.cycles]
  case refine_2 => simpa [UART.frame, Array.getD] using observations 0
  case refine_3 => simpa [sampleTime, UART.frame, Array.getD,
    show (9 : Fin 10).val = 9 from rfl] using observations 9

theorem wire_rearm_tail (cfg : Config) (fits : cfg.bitCycles ≤ 256) (start : Nat)
    (byte : BitVec 8) (rest : List (BitVec 8)) (n : Nat) :
    wire (idealTx cfg fits) start (byte :: rest) (completion cfg start + 1 + n) =
      wire (idealTx cfg fits) (rearmGap cfg) rest n := by
  rw [wire_stop_suffix _ start byte rest _ (by simp only [ideal_cycles, completion]; omega)]
  have minimum := cfg.minimum
  rw [wire_shift _ _ (completion cfg start + 1) rest n (by
    simp only [UART.Config.frameCycles, ideal_cycles, completion, Config.half]
    omega)]
  congr 1
  simp only [UART.Config.frameCycles, ideal_cycles, completion, rearmGap, Config.half]
  omega

theorem ideal_matches (cfg : Config) (fits : cfg.bitCycles ≤ 256) (bytes : List (BitVec 8))
    (start : Nat) (later : 2 ≤ start) (incoming : Nat → Input)
    (line : ∀ n, (incoming n).line = wire (idealTx cfg fits) start bytes n)
    (quiet : ∀ n, (incoming n).reset = false) : Matches cfg incoming (idealFrames cfg start bytes) := by
  induction bytes generalizing start incoming with
  | nil => trivial
  | cons byte rest ih =>
    exact ⟨wire_first_frame cfg fits start later byte rest incoming line quiet,
      ih (rearmGap cfg) (rearmGap_two cfg) (fun n => incoming (completion cfg start + 1 + n))
        (fun n => (line _).trans (wire_rearm_tail cfg fits start byte rest n)) (fun n => quiet _)⟩

/-- Exact result pulses for any finite ideal back-to-back byte sequence and consumer history. -/
theorem ideal_series (cfg : Config) (fits : cfg.bitCycles ≤ 256) (bytes : List (BitVec 8))
    (start : Nat) (later : 2 ≤ start) (buffer : Buffer.State) (incoming : Nat → Input)
    (line : ∀ n, (incoming n).line = wire (idealTx cfg fits) start bytes n)
    (quiet : ∀ n, (incoming n).reset = false) (n : Nat)
    (within : n ≤ horizon cfg (idealFrames cfg start bytes)) :
    arrival (run cfg ⟨Rx.initial, buffer⟩ incoming n) = expected cfg (idealFrames cfg start bytes) n :=
  series_correct cfg _ buffer incoming (ideal_matches cfg fits bytes start later incoming line quiet) n within

end Pinwheel.UART.Rx.Stream
