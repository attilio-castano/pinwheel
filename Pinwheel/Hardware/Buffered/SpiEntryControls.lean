import Pinwheel.Hardware.Buffered.SpiAdmission

/-! Actual entry-control evaluations for timed SPI leaves. Buffer comparisons
are inputs to the graph, not a premise about successful source execution. -/
namespace Pinwheel.Hardware.Buffered.SpiEntryControls
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

structure PreEntry (i : Values Reactive.Input) (s : Values Reactive.Register) : Prop where
  resetting : Reactive.resetting.eval i s = 0
  entering : Reactive.entering.eval i s = 1
  legal : Reactive.legalEntry.eval i s = 1
  heldFault : Reactive.heldFault.eval i s = 0
  heldTimeout : Reactive.heldTimeout.eval i s = 0

structure Flags (i : Values Reactive.Input) (s : Values Reactive.Register)
    (run under over consume append completes fails : Bool) : Prop where
  running : Reactive.runEntry.eval i s = BitVec.ofBool run
  underflow : Reactive.underflow.eval i s = BitVec.ofBool under
  overflow : Reactive.overflow.eval i s = BitVec.ofBool over
  consuming : Reactive.consuming.eval i s = BitVec.ofBool consume
  appending : Reactive.appending.eval i s = BitVec.ofBool append
  complete : Reactive.entryComplete.eval i s = BitVec.ofBool completes
  failed : Reactive.entryFailed.eval i s = BitVec.ofBool fails
  stopping : Reactive.stopping.eval i s = BitVec.ofBool (completes || fails)
  timeout : Reactive.entryTimeout.eval i s = 0
  noTimeout : (Reactive.either Reactive.heldTimeout Reactive.entryTimeout).eval i s = 0

theorem quiet_preEntry (i : Values Reactive.Input) (s : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (phase : s .phase = 1) (remaining : s .remaining = 0)
    (legal : Reactive.legalEntry.eval i s = 1) : PreEntry i s := by
  have controls := SpiCircuit.quiet_controls i s quiet
  refine ⟨controls.1, ?_, legal, ?_, ?_⟩
  · simp [Reactive.entering, Reactive.dispatch, Reactive.isPhase, Reactive.both,
      Reactive.either, Expr.eval, controls.1, controls.2.2.1, phase, remaining]
  · simp [Reactive.heldFault, Reactive.isPhase, Reactive.both, Expr.eval, phase]
  · simp [Reactive.heldTimeout, Reactive.isPhase, Reactive.both,
      Reactive.either, Expr.eval, phase]

theorem starting_preEntry (i : Values Reactive.Input) (s : Values Reactive.Register)
    (starting : Reactive.starting.eval i s = 1)
    (legal : Reactive.legalEntry.eval i s = 1) : PreEntry i s := by
  have controls := SpiAdmission.starting_controls i s starting
  exact ⟨controls.resetting, controls.entering, legal,
    controls.heldFault, controls.heldTimeout⟩

theorem low_available (i : Values Reactive.Input) (s : Values Reactive.Register)
    (h : PreEntry i s) (kind : Reactive.kind.eval i s = 1#3)
    (wants : Reactive.wantsRx.eval i s = 0)
    (space : (Reactive.entryConsumed.eval i s).toNat < (Reactive.entryTxLength.eval i s).toNat) :
    Flags i s true false false true false false false := by
  constructor
  all_goals simp [Reactive.runEntry, Reactive.entryTerminal, Reactive.isKind,
    Reactive.underflow, Reactive.overflow, Reactive.consuming, Reactive.appending,
    Reactive.entryComplete, Reactive.entryFailed, Reactive.stopping, Reactive.entryTimeout,
    Reactive.both, Reactive.either, Expr.eval, h.resetting, h.entering, h.legal,
    h.heldFault, h.heldTimeout, kind, wants, space]

theorem low_exhausted (i : Values Reactive.Input) (s : Values Reactive.Register)
    (h : PreEntry i s) (kind : Reactive.kind.eval i s = 1#3)
    (wants : Reactive.wantsRx.eval i s = 0)
    (exhausted : ¬(Reactive.entryConsumed.eval i s).toNat < (Reactive.entryTxLength.eval i s).toNat) :
    Flags i s true true false false false false true := by
  constructor
  all_goals simp [Reactive.runEntry, Reactive.entryTerminal, Reactive.isKind,
    Reactive.underflow, Reactive.overflow, Reactive.consuming, Reactive.appending,
    Reactive.entryComplete, Reactive.entryFailed, Reactive.stopping, Reactive.entryTimeout,
    Reactive.both, Reactive.either, Expr.eval, h.resetting, h.entering, h.legal,
    h.heldFault, h.heldTimeout, kind, wants, exhausted]

theorem high_room (i : Values Reactive.Input) (s : Values Reactive.Register)
    (h : PreEntry i s) (kind : Reactive.kind.eval i s = 2#3)
    (wants : Reactive.wantsRx.eval i s = 1)
    (space : (Reactive.entryRxLength.eval i s).toNat < (Reactive.entryCapacity.eval i s).toNat) :
    Flags i s true false false false true false false := by
  constructor
  all_goals simp [Reactive.runEntry, Reactive.entryTerminal, Reactive.isKind,
    Reactive.underflow, Reactive.overflow, Reactive.consuming, Reactive.appending,
    Reactive.entryComplete, Reactive.entryFailed, Reactive.stopping, Reactive.entryTimeout,
    Reactive.both, Reactive.either, Expr.eval, h.resetting, h.entering, h.legal,
    h.heldFault, h.heldTimeout, kind, wants, space]

theorem high_full (i : Values Reactive.Input) (s : Values Reactive.Register)
    (h : PreEntry i s) (kind : Reactive.kind.eval i s = 2#3)
    (wants : Reactive.wantsRx.eval i s = 1)
    (full : ¬(Reactive.entryRxLength.eval i s).toNat < (Reactive.entryCapacity.eval i s).toNat) :
    Flags i s true false true false false false true := by
  constructor
  all_goals simp [Reactive.runEntry, Reactive.entryTerminal, Reactive.isKind,
    Reactive.underflow, Reactive.overflow, Reactive.consuming, Reactive.appending,
    Reactive.entryComplete, Reactive.entryFailed, Reactive.stopping, Reactive.entryTimeout,
    Reactive.both, Reactive.either, Expr.eval, h.resetting, h.entering, h.legal,
    h.heldFault, h.heldTimeout, kind, wants, full]

theorem release (i : Values Reactive.Input) (s : Values Reactive.Register)
    (h : PreEntry i s) (kind : Reactive.kind.eval i s = 0#3)
    (wants : Reactive.wantsRx.eval i s = 0) :
    Flags i s true false false false false false false := by
  constructor
  all_goals simp [Reactive.runEntry, Reactive.entryTerminal, Reactive.isKind,
    Reactive.underflow, Reactive.overflow, Reactive.consuming, Reactive.appending,
    Reactive.entryComplete, Reactive.entryFailed, Reactive.stopping, Reactive.entryTimeout,
    Reactive.both, Reactive.either, Expr.eval, h.resetting, h.entering, h.legal,
    h.heldFault, h.heldTimeout, kind, wants]

theorem halt (i : Values Reactive.Input) (s : Values Reactive.Register)
    (h : PreEntry i s) (kind : Reactive.kind.eval i s = 3#3) :
    Flags i s false false false false false true false := by
  constructor
  all_goals simp [Reactive.runEntry, Reactive.entryTerminal, Reactive.isKind,
    Reactive.underflow, Reactive.overflow, Reactive.consuming, Reactive.appending,
    Reactive.entryComplete, Reactive.entryFailed, Reactive.stopping, Reactive.entryTimeout,
    Reactive.both, Reactive.either, Expr.eval, h.resetting, h.entering, h.legal,
    h.heldFault, h.heldTimeout, kind]

end Pinwheel.Hardware.Buffered.SpiEntryControls
