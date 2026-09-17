import Pinwheel.UART.Spec

/-! Receive-side 8N1 contract. Times refer to already sampled digital input,
not directly to an asynchronous physical pin. -/
namespace Pinwheel.UART.Rx

/-- The bound leaves room for ten split delays in the 256-address engine. -/
structure Config where
  bitCycles : Nat
  minimum : 8 ≤ bitCycles
  maximum : bitCycles ≤ 6656
  input : Fin 2 := 0
  deriving DecidableEq, Repr

def Config.ofCycles (cycles : Nat) (input : Fin 2 := 0) : Option Config :=
  if h : 8 ≤ cycles ∧ cycles ≤ 6656 then some ⟨cycles, h.1, h.2, input⟩ else none

def Config.half (cfg : Config) : Nat := cfg.bitCycles / 2

/-- Symbol zero validates start; symbols 1–8 capture data; symbol 9 checks stop. -/
def duration (cfg : Config) (symbol : Fin 10) : Nat :=
  if symbol.val = 0 then cfg.half else cfg.bitCycles

def sampleTime (cfg : Config) (detected : Nat) (symbol : Fin 10) : Nat :=
  detected + cfg.half + symbol.val * cfg.bitCycles

/-- Slots 0–7 hold data in UART wire order. Start observation and stop have separate slots. -/
def sampleSlot (symbol : Fin 10) : Fin 16 :=
  if symbol.val = 0 then 8 else if symbol.val = 9 then 9
  else ⟨symbol.val - 1, by omega⟩

def received (samples : Vector Bool 16) : BitVec 8 :=
  BitVec.ofBoolListBE [samples[7], samples[6], samples[5], samples[4],
    samples[3], samples[2], samples[1], samples[0]]

inductive Outcome where
  | byte (value : BitVec 8)
  | framingError (value : BitVec 8)
  deriving DecidableEq, Repr

def outcome (samples : Vector Bool 16) : Outcome :=
  if samples[9] then .byte (received samples) else .framingError (received samples)

/-- An independently generated ideal frame, with an arbitrary start edge and bit period. -/
def wire (byte : BitVec 8) (start bitCycles cycle : Nat) : Bool :=
  if cycle < start then true else
    (UART.frame byte).getD ((cycle - start) / bitCycles) true

/-- Digital timing premise: each designated data/stop sample has the transmitted level.
This does not presume transmitter and receiver clocks are equal. -/
def SamplesFrame (cfg : Config) (detected : Nat) (incoming : Nat → Bool)
    (byte : BitVec 8) : Prop :=
  (∀ k : Fin 8, incoming (sampleTime cfg detected ⟨k.val + 1, by omega⟩) =
    byte.getLsbD k.val) ∧ incoming (sampleTime cfg detected 9) = true

/-- Independent event specification for a suffix of the eight data bits and stop.
`elapsed` is the edge before that suffix. Only the nine designated observations matter. -/
def suffixSlot (following : Nat) : Fin 16 :=
  if following = 0 then 9 else Fin.ofNat 16 (8 - following)

def collect (cfg : Config) : Nat → Nat → Vector Bool 16 → (Nat → Bool) → Vector Bool 16
  | 0, _, slots, _ => slots
  | n + 1, elapsed, slots, incoming =>
    collect cfg n (elapsed + cfg.bitCycles)
      (slots.set (suffixSlot n) (incoming (elapsed + cfg.bitCycles))) incoming

def expectedByte (cfg : Config) (elapsed : Nat) (incoming : Nat → Bool) : BitVec 8 :=
  BitVec.ofBoolListBE [incoming (elapsed + 8 * cfg.bitCycles), incoming (elapsed + 7 * cfg.bitCycles),
    incoming (elapsed + 6 * cfg.bitCycles), incoming (elapsed + 5 * cfg.bitCycles),
    incoming (elapsed + 4 * cfg.bitCycles), incoming (elapsed + 3 * cfg.bitCycles),
    incoming (elapsed + 2 * cfg.bitCycles), incoming (elapsed + cfg.bitCycles)]

end Pinwheel.UART.Rx
