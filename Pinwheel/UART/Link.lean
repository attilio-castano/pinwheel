import Pinwheel.UART.Tx
import Pinwheel.UART.Rx

/-! A digital UART link with independent clock periods/phases and bounded observation age.
All times use one arbitrary integer quantum. A physical sampler must justify this contract. -/
namespace Pinwheel.UART.Link

structure Timing where
  tx : UART.Config
  rx : Rx.Config
  txTick : Nat
  txTickPositive : 0 < txTick
  rxTick : Nat
  rxTickPositive : 0 < rxTick
  txStart : Nat
  rxPhase : Nat := 0
  deriving DecidableEq, Repr

def Timing.edge (t : Timing) (cycle : Nat) : Nat := t.rxPhase + cycle * t.rxTick
def Timing.txBit (t : Timing) : Nat := t.tx.cycles * t.txTick
def Timing.rxBit (t : Timing) : Nat := t.rx.bitCycles * t.rxTick
def Timing.center (t : Timing) : Nat := t.rx.half * t.rxTick

structure Latency where
  earliest : Nat
  latest : Nat
  ordered : earliest ≤ latest
  deriving DecidableEq, Repr

def Latency.spread (b : Latency) : Nat := b.latest - b.earliest
def Latency.fixed (delay : Nat) : Latency := ⟨delay, delay, Nat.le_refl _⟩

/-- Age is allowed to vary independently at every observation; no analog behavior is inferred. -/
def Latency.Contains (b : Latency) (age : Nat → Nat) : Prop :=
  ∀ cycle, b.earliest ≤ age cycle ∧ age cycle ≤ b.latest

/-- Observe a source indexed by its own clock cycles since TX acceptance. Before that
acceptance becomes visible, the line is idle high. Transitions use half-open intervals. -/
def observe (t : Timing) (source : Nat → Bool) (age : Nat → Nat) (cycle : Nat) : Bool :=
  if t.edge cycle < t.txStart + age cycle then true
  else source ((t.edge cycle - (t.txStart + age cycle)) / t.txTick)

def transmitter (cfg : UART.Config) (byte : BitVec 8) (cycle : Nat) : Bool :=
  UART.pin (UART.run (UART.initial cfg byte) cycle)

def sampled (t : Timing) (byte : BitVec 8) (age : Nat → Nat) : Nat → Bool :=
  observe t (transmitter t.tx byte) age

/-- First RX edge at/after the delayed start, when that start is later than RX cycle zero. -/
def firstEdge (t : Timing) (delay : Nat) : Nat :=
  (t.txStart + delay - t.rxPhase - 1) / t.rxTick + 1

def completion (t : Timing) (detected : Nat) : Nat :=
  detected + (t.rx.half + 9 * t.rx.bitCycles)

/-- Byte-independent sufficient bounds. The center and stop endpoints imply all ten
sampling windows. The one-RX-tick allowance covers unknown start-edge phase. -/
def Safe (t : Timing) (b : Latency) : Prop :=
  t.edge 1 < t.txStart + b.earliest ∧
  b.spread ≤ t.center ∧
  t.center + b.spread + t.rxTick ≤ t.txBit ∧
  9 * t.txBit + b.spread ≤ t.center + 9 * t.rxBit ∧
  t.center + 9 * t.rxBit + b.spread + t.rxTick ≤ 10 * t.txBit

instance (t : Timing) (b : Latency) : Decidable (Safe t b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Equal unit clocks and zero receiver phase, over the two compilers' shared period range. -/
def ideal (rx : Rx.Config) (fits : rx.bitCycles ≤ 256) (start : Nat) : Timing :=
  { tx := ⟨⟨rx.bitCycles - 1, by omega⟩⟩
    rx := rx
    txTick := 1
    txTickPositive := by decide
    rxTick := 1
    rxTickPositive := by decide
    txStart := start }

end Pinwheel.UART.Link
