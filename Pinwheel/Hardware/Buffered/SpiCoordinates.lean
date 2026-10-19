import Pinwheel.Hardware.Buffered.SpiSource
import Pinwheel.Hardware.Buffered.ReactiveProofs

/-! Coordinate correspondence for the compact SPI program's two counted loops.
These lemmas evaluate the real packed sequencer expressions. -/
namespace Pinwheel.Hardware.Buffered.SpiCoordinates
open Pinwheel.Hardware

abbrev bitSpan (c : SpiSource.Config) : Nat := 16 * (c.bytesMinusOne.val + 1)

abbrev physicalPC (c : SpiSource.Config) (virtual : Nat) : Nat :=
  if virtual < bitSpan c then virtual % 2 else virtual - bitSpan c + 2

abbrev outer (c : SpiSource.Config) (virtual : Nat) : Nat :=
  if virtual < bitSpan c then virtual / 16 else 0

abbrev inner (c : SpiSource.Config) (virtual : Nat) : Nat :=
  if virtual < bitSpan c then virtual % 16 / 2 else 0

/-- The live coordinates and exact resident source image at a timed SPI leaf.
Payload, owner, sampler, remaining-time and unrelated control registers stay free.
-/
structure At (c : SpiSource.Config) (virtual : Nat) (r : Values Reactive.Register) : Prop where
  phase : r .phase = 1
  virtualPC : r .virtualPC = BitVec.ofNat 10 virtual
  pc : r .pc = BitVec.ofNat 7 (physicalPC c virtual)
  currentControl : r .currentControl =
    (SpiSource.control c (BitVec.ofNat 6 (physicalPC c virtual))).extractLsb' 0 22
  outer : r .outer = BitVec.ofNat 3 (outer c virtual)
  inner : r .inner = BitVec.ofNat 3 (inner c virtual)
  count : r .count = 4
  virtualSpan : r .virtualSpan = BitVec.ofNat 11 (bitSpan c + 2)
  words : ∀ k, r (.word k) = SpiSource.fullWords c k

private abbrev loopConfig (bytes : Fin 4) : SpiSource.Config := ⟨bytes, 2, by decide⟩

private def zeroInput : Values Reactive.Input := fun _ => 0

private def loopRegisters (bytes : Fin 4) (virtual : Nat) : Values Reactive.Register
  | _, .word k => SpiSource.fullWords (loopConfig bytes) k
  | _, .count => 4
  | _, .virtualSpan => BitVec.ofNat 11 (bitSpan (loopConfig bytes) + 2)
  | _, .phase => 1
  | _, .virtualPC => BitVec.ofNat 10 virtual
  | _, .pc => BitVec.ofNat 7 (physicalPC (loopConfig bytes) virtual)
  | _, .currentControl =>
      (SpiSource.control (loopConfig bytes)
        (BitVec.ofNat 6 (physicalPC (loopConfig bytes) virtual))).extractLsb' 0 22
  | _, .outer => BitVec.ofNat 3 (outer (loopConfig bytes) virtual)
  | _, .inner => BitVec.ofNat 3 (inner (loopConfig bytes) virtual)
  | _, _ => 0

private theorem loop_at (bytes : Fin 4) (virtual : Nat) :
    At (loopConfig bytes) virtual (loopRegisters bytes virtual) := by
  constructor <;> first | rfl | exact fun _ => rfl

private theorem loop_certificate : ∀ bytes : Fin 4, ∀ virtual : Fin 65,
    virtual.val ≤ bitSpan (loopConfig bytes) →
    Reactive.entryPC.eval zeroInput (loopRegisters bytes virtual.val) =
        BitVec.ofNat 7 (physicalPC (loopConfig bytes) (virtual.val + 1)) ∧
    Reactive.entryVirtual.eval zeroInput (loopRegisters bytes virtual.val) =
        BitVec.ofNat 11 (virtual.val + 1) ∧
    Reactive.entryOuter.eval zeroInput (loopRegisters bytes virtual.val) =
        BitVec.ofNat 3 (outer (loopConfig bytes) (virtual.val + 1)) ∧
    Reactive.entryInner.eval zeroInput (loopRegisters bytes virtual.val) =
        BitVec.ofNat 3 (inner (loopConfig bytes) (virtual.val + 1)) := by
  decide +kernel

private theorem control_certificate : ∀ bytes : Fin 4, ∀ virtual : Fin 65,
    virtual.val ≤ bitSpan (loopConfig bytes) →
    Reactive.inBounds.eval zeroInput (loopRegisters bytes virtual.val) = 1 ∧
    Reactive.controlCanonical.eval zeroInput (loopRegisters bytes virtual.val) = 1 := by
  decide +kernel

theorem bitSpan_bounds (c : SpiSource.Config) : 16 ≤ bitSpan c ∧ bitSpan c ≤ 64 := by
  have bound := c.bytesMinusOne.isLt
  simp only [bitSpan]
  omega
  done

/-- The packed sequencer advances the nested loop coordinates, including the
last bit, byte rollover, exit to release, and release-to-HALT transition. -/
theorem next_coordinates (c : SpiSource.Config) (virtual : Nat)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (initialized : i .initialize = 0) (command : i .command = 0)
    (h : At c virtual r) (within : virtual ≤ bitSpan c) :
    Reactive.entryPC.eval i r = BitVec.ofNat 7 (physicalPC c (virtual + 1)) ∧
    Reactive.entryVirtual.eval i r = BitVec.ofNat 11 (virtual + 1) ∧
    Reactive.entryOuter.eval i r = BitVec.ofNat 3 (outer c (virtual + 1)) ∧
    Reactive.entryInner.eval i r = BitVec.ofNat 3 (inner c (virtual + 1)) := by
  have certificate := loop_certificate c.bytesMinusOne
    ⟨virtual, by have bound := (bitSpan_bounds c).2; omega⟩ within
  dsimp only [loopConfig, bitSpan, physicalPC, outer, inner] at certificate
  simp [Reactive.entryPC, Reactive.entryVirtual, Reactive.entryOuter, Reactive.entryInner,
    Reactive.sequentialPC, Reactive.sequentialOuter, Reactive.sequentialInner,
    Reactive.starting, Reactive.free, Reactive.busy, Reactive.resetting,
    Reactive.warm, Reactive.cold, Reactive.cmd, Reactive.isPhase,
    Reactive.absoluteDispatch, Reactive.terminalEdge, Reactive.finish,
    Reactive.innerAgain, Reactive.outerAgain, Reactive.currentControl,
    Reactive.controlDepth, Reactive.innerStart, Reactive.outerStart,
    Reactive.innerBound, Reactive.outerBound, Reactive.innerEnd, Reactive.outerEnd,
    Reactive.increment, Reactive.both, Reactive.either, Expr.eval,
    initialized, command, h.phase, h.pc, h.virtualPC, h.currentControl, h.outer, h.inner,
    zeroInput, loopRegisters, physicalPC, bitSpan, outer, inner,
    SpiSource.control] at certificate ⊢
  exact certificate
  done

theorem dispatch_entering (i : Values Reactive.Input) (r : Values Reactive.Register)
    (initialized : i .initialize = 0) (command : i .command = 0)
    (phase : r .phase = 1) (remaining : r .remaining = 0) :
    Reactive.entering.eval i r = 1 := by
  simp [Reactive.entering, Reactive.dispatch, Reactive.isPhase, Reactive.both,
    Reactive.either, Reactive.resetting, Reactive.warm, Reactive.cold, Reactive.cmd,
    Expr.eval, initialized, command, phase, remaining]

theorem entry_record (c : SpiSource.Config) (virtual : Nat)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (initialized : i .initialize = 0) (command : i .command = 0)
    (h : At c virtual r) (within : virtual ≤ bitSpan c) (remaining : r .remaining = 0) :
    Reactive.entryRecord.eval i r =
      SpiSource.fullWords c (BitVec.ofNat 6 (physicalPC c (virtual + 1))) := by
  have entering := dispatch_entering i r initialized command h.phase remaining
  have next := (next_coordinates c virtual i r initialized command h within).1
  simp [Reactive.entryRecord, Expr.eval, entering, Execution.readTree_correct, next, h.words]
  simp [← BitVec.setWidth_ushiftRight_eq_extractLsb,
    BitVec.setWidth_ofNat_of_le (by decide : 6 ≤ 7)]
  done

theorem entry_fields (c : SpiSource.Config) (virtual : Nat)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (initialized : i .initialize = 0) (command : i .command = 0)
    (h : At c virtual r) (within : virtual ≤ bitSpan c) (remaining : r .remaining = 0) :
    let k := BitVec.ofNat 6 (physicalPC c (virtual + 1))
    Reactive.entryWord.eval i r = SpiSource.word c k ∧
    Reactive.entryControl.eval i r = SpiSource.control c k ∧
    Reactive.entryBranch.eval i r = 0 := by
  have record := entry_record c virtual i r initialized command h within remaining
  simp only [Reactive.entryWord, Reactive.entryControl, Reactive.entryBranch,
    Expr.eval, record, SpiSource.fullWords,
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 88),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 64 + 24 ≤ 88),
    BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left]
  simp
  done

end Pinwheel.Hardware.Buffered.SpiCoordinates
