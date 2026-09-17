import Pinwheel.UART.StreamLink
import Pinwheel.Latency

/-! A registered input pipeline in front of a receiver. Every stage delays each
digital observation by one RX tick and leaves the observation-age spread
unchanged. Metastability and asynchronous arrival remain outside this model. -/
namespace Pinwheel.UART.Link

def Latency.delayed (b : Latency) (delay : Nat) : Latency :=
  ⟨b.earliest + delay, b.latest + delay, Nat.add_le_add_right b.ordered delay⟩

theorem Latency.delayed_spread (b : Latency) (delay : Nat) :
    (b.delayed delay).spread = b.spread := by
  simp only [Latency.delayed, Latency.spread]
  omega

/-- Age of the sample consumed on an RX cycle behind `stages` registers: the pin
sample taken `stages` edges earlier, with its own age. -/
def pipelineAge (t : Timing) (stages : Nat) (age : Nat → Nat) (cycle : Nat) : Nat :=
  age (cycle - stages) + stages * t.rxTick

theorem pipelineAge_contains (t : Timing) (b : Latency) (stages : Nat) (age : Nat → Nat)
    (within : b.Contains age) :
    (b.delayed (stages * t.rxTick)).Contains (pipelineAge t stages age) := by
  intro cycle
  have bounded := within (cycle - stages)
  simp only [Latency.delayed, pipelineAge]
  omega

/-- The sufficient single-frame bounds constrain only the earliest age from below
and the spread, so a uniform additional delay preserves them. -/
theorem Safe.delayed {t : Timing} {b : Latency} (safe : Safe t b) (delay : Nat) :
    Safe t (b.delayed delay) := by
  simp only [Safe, Latency.delayed_spread] at safe ⊢
  simp only [Latency.delayed]
  omega

/-- What a direct receiver observes on a cycle is what the pipelined receiver
consumes `stages` cycles later. -/
theorem observe_pipeline (t : Timing) (source : Nat → Bool) (age : Nat → Nat)
    (stages cycle : Nat) :
    observe t source (pipelineAge t stages age) (cycle + stages) = observe t source age cycle := by
  have edge : t.edge (cycle + stages) = t.edge cycle + stages * t.rxTick := by
    simp only [Timing.edge, Nat.add_mul]
    omega
  simp only [observe, pipelineAge, Nat.add_sub_cancel, edge]
  by_cases early : t.edge cycle < t.txStart + age cycle
  · rw [if_pos early, if_pos (by omega)]
  · rw [if_neg early, if_neg (by omega)]
    congr 2
    omega

/-- If every stage holds the idle level when receiver cycle zero begins, the
engine-side history is an ordinary observation history whose age bounds are both
`stages` RX ticks later. Existing link theorems then apply to the delayed bounds. -/
theorem pipelined_observe (t : Timing) (b : Latency) (safe : Safe t b) (source : Nat → Bool)
    (age : Nat → Nat) (within : b.Contains age) (stages cycle : Nat) :
    (if cycle < stages then true else observe t source age (cycle - stages)) =
      observe t source (pipelineAge t stages age) cycle := by
  by_cases draining : cycle < stages
  · have bounded := within (cycle - stages)
    have ticks := Nat.mul_le_mul_right t.rxTick (show cycle + 1 ≤ stages from draining)
    have first := safe.1
    have early : t.edge cycle < t.txStart + pipelineAge t stages age cycle := by
      simp only [Timing.edge, pipelineAge, Nat.add_mul, Nat.one_mul] at first ticks ⊢
      omega
    rw [if_pos draining]
    unfold observe
    rw [if_pos early]
  · rw [if_neg draining]
    have split : cycle = cycle - stages + stages := by omega
    rw [split, observe_pipeline, ← split]

/-- The same statement in the shared vocabulary: what a receiver consumes behind
`stages` idle-high registers is an ordinary observation history with later age. -/
theorem delayed_observe (t : Timing) (b : Latency) (safe : Safe t b) (source : Nat → Bool)
    (age : Nat → Nat) (within : b.Contains age) (stages : Nat) :
    Pinwheel.Latency.delayed stages true (observe t source age) =
      observe t source (pipelineAge t stages age) := by
  funext cycle
  exact pipelined_observe t b safe source age within stages cycle

end Pinwheel.UART.Link

namespace Pinwheel.UART.StreamLink
open Link

/-- Continuous reception adds one more spread-only bound, preserved likewise. -/
theorem Safe.delayed {t : Timing} {b : Latency} (safe : Safe t b) (delay : Nat) :
    Safe t (b.delayed delay) := by
  refine ⟨Link.Safe.delayed safe.1 delay, ?_⟩
  have bound := safe.2
  simp only [Latency.delayed_spread]
  exact bound

end Pinwheel.UART.StreamLink
