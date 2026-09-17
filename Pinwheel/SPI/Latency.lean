import Pinwheel.Latency
import Pinwheel.SPI.Controller

/-! Mode-0 SPI behind an input pipeline. Outputs are not delayed, inputs are, so
the controller effectively samples MISO `d` cycles *before* each rising clock
edge. Whether that is acceptable is a condition on the peripheral's timing. -/
namespace Pinwheel.SPI

/-- Wire-order slot `bit` carries this bit of the reply, most significant first. -/
def replyBit (reply : BitVec 8) (bit : Nat) : Bool := reply.getLsbD (7 - bit)

/-- Peripheral timing contract at the pins: MISO already carries the reply bit
`lead` cycles before its sampling edge and keeps it until that edge. -/
def Presents (cfg : Config) (pins : Nat → Bool) (reply : BitVec 8) (lead : Nat) : Prop :=
  ∀ (bit : Fin 8) (t : Nat), sampleTime cfg bit - lead ≤ t → t ≤ sampleTime cfg bit →
    pins t = replyBit reply bit.val

theorem replyByte (reply : BitVec 8) :
    BitVec.ofBoolListBE [replyBit reply 0, replyBit reply 1, replyBit reply 2, replyBit reply 3,
      replyBit reply 4, replyBit reply 5, replyBit reply 6, replyBit reply 7] = reply := by
  ext i hi
  rw [BitVec.getElem_ofBoolListBE]
  have bound : i < 8 := by simpa using hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases cases with h | h | h | h | h | h | h | h
  all_goals subst h
  all_goals simp +decide [replyBit, BitVec.getLsbD_eq_getElem]

/-- The sample consumed for each slot, behind `d` registers, is the pin value `d`
cycles before the sampling edge. -/
theorem delayed_sample (cfg : Config) (pins : Nat → Bool) (idle : Bool) (d : Nat)
    (hd : d ≤ cfg.halfCycles) (bit : Fin 8) :
    Latency.delayed d idle pins (sampleTime cfg bit) = pins (sampleTime cfg bit - d) := by
  have early : cfg.halfCycles ≤ sampleTime cfg bit :=
    Nat.le_mul_of_pos_left cfg.halfCycles (by omega)
  simp [Latency.delayed, show ¬ sampleTime cfg bit < d by omega]

/-- If the peripheral presents each bit at least `d` cycles before its sampling
edge, the byte received behind `d` input registers is the peripheral's reply. -/
theorem expectedByte_delayed (cfg : Config) (pins : Nat → Bool) (reply : BitVec 8)
    (lead d : Nat) (idle : Bool) (presents : Presents cfg pins reply lead)
    (hd : d ≤ lead) (hl : lead ≤ cfg.halfCycles) :
    expectedByte cfg (Latency.delayed d idle pins) = reply := by
  have sample (bit : Fin 8) :
      Latency.delayed d idle pins (sampleTime cfg bit) = replyBit reply bit.val := by
    rw [delayed_sample cfg pins idle d (Nat.le_trans hd hl) bit]
    exact presents bit _ (by omega) (Nat.sub_le _ _)
  have s0 := sample ⟨0, by omega⟩; have s1 := sample ⟨1, by omega⟩
  have s2 := sample ⟨2, by omega⟩; have s3 := sample ⟨3, by omega⟩
  have s4 := sample ⟨4, by omega⟩; have s5 := sample ⟨5, by omega⟩
  have s6 := sample ⟨6, by omega⟩; have s7 := sample ⟨7, by omega⟩
  simp only [sampleTime, Nat.mul_zero, Nat.zero_add, Nat.one_mul, Nat.reduceMul, Nat.reduceAdd]
    at s0 s1 s2 s3 s4 s5 s6 s7
  rw [← replyByte reply]
  unfold expectedByte
  rw [s0, s1, s2, s3, s4, s5, s6, s7]

/-- End to end: the controller's result behind the pipeline. Its pin waveform is
`waveform_correct` for every input history, so latency cannot disturb it. -/
theorem result_behind_pipeline (cfg : Config) (byte reply : BitVec 8) (pins : Nat → Bool)
    (lead d : Nat) (idle : Bool) (presents : Presents cfg pins reply lead)
    (hd : d ≤ lead) (hl : lead ≤ cfg.halfCycles) (cycle : Nat) :
    result (run cfg byte (Latency.delayed d idle pins) cycle) =
      if cycle < cfg.transferCycles then none else some reply := by
  rw [result_exact, expectedByte_delayed cfg pins reply lead d idle presents hd hl]

/-- A mode-0 peripheral that changes MISO `tco` cycles after each falling clock
edge (chip select for the first bit) presents every bit `halfCycles - tco` early. -/
def Mode0 (cfg : Config) (pins : Nat → Bool) (reply : BitVec 8) (tco : Nat) : Prop :=
  ∀ (bit : Fin 8) (t : Nat), 2 * bit.val * cfg.halfCycles + tco ≤ t →
    t < (2 * bit.val + 2) * cfg.halfCycles + tco → pins t = replyBit reply bit.val

theorem Mode0.presents {cfg : Config} {pins : Nat → Bool} {reply : BitVec 8} {tco : Nat}
    (peripheral : Mode0 cfg pins reply tco) (fits : tco ≤ cfg.halfCycles) :
    Presents cfg pins reply (cfg.halfCycles - tco) := by
  intro bit t lower upper
  have sample : sampleTime cfg bit = 2 * bit.val * cfg.halfCycles + cfg.halfCycles := by
    simp [sampleTime, Nat.add_mul]
  have following : (2 * bit.val + 2) * cfg.halfCycles =
      2 * bit.val * cfg.halfCycles + 2 * cfg.halfCycles := by
    simp [Nat.add_mul]
  have positive : 0 < cfg.halfCycles := Nat.zero_lt_succ _
  rw [sample] at lower upper
  apply peripheral bit t
  · omega
  · rw [following]
    omega

/-- The rate condition: the clock half-period must cover the input latency plus
the peripheral's output delay. -/
theorem mode0_behind_pipeline (cfg : Config) (byte reply : BitVec 8) (pins : Nat → Bool)
    (tco d : Nat) (idle : Bool) (peripheral : Mode0 cfg pins reply tco)
    (rate : d + tco ≤ cfg.halfCycles) (cycle : Nat) :
    result (run cfg byte (Latency.delayed d idle pins) cycle) =
      if cycle < cfg.transferCycles then none else some reply :=
  result_behind_pipeline cfg byte reply pins (cfg.halfCycles - tco) d idle
    (peripheral.presents (by omega)) (by omega) (Nat.sub_le _ _) cycle

end Pinwheel.SPI
