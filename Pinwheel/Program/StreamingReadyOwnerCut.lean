import Pinwheel.Program.StreamingReadyCustodySession

namespace Pinwheel.Program.StreamingReady
open Pinwheel.Program.Streaming
set_option linter.unusedSimpArgs false

def Session.State.FreeExport (s : Session.State a) : Prop :=
  s.core.phase = .free → s.host.exportBits = 0#7

theorem engine_free_origin (p : Program) (s : State a) (free : (engine p s).phase = .free) :
    s.phase = .free := by
  by_cases busy : s.phase.busy = true
  · have live := engine_live p s busy
    rw [free] at live
    simp [Phase.busy, Phase.retained] at live
  · cases phase : s.phase <;> simp [phase, Phase.busy] at busy
    all_goals simp_all [engine]

theorem Session.State.FreeExport.step (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (runtime : Session.RuntimeInput s i) (freeExport : s.FreeExport)
    (frames : s.host.FrameSafe) (reservation : s.ReservationSafe) :
    (s.step p pending i).FreeExport := by
  intro free
  have cold : (s.hostInput pending i).initialize = false := runtime.1
  by_cases clear : s.host.clearingExport (s.hostInput pending i).status = true
  · change (Host.step (s.hostInput pending i) s.host).exportBits = 0#7
    simp [Host.step, cold, clear]
  · have noClear := Bool.eq_false_iff.mpr clear
    by_cases admit : s.host.admittingBulk (s.hostInput pending i).status = true
    · exact (s.host.admit_export_fields (s.hostInput pending i) cold admit).2.2.1
    · have noAdmit := Bool.eq_false_iff.mpr admit
      by_cases capture : s.host.stagedRX = true
      · have stage := capture
        simp only [Host.State.stagedRX, Bool.and_eq_true, beq_iff_eq] at stage
        have grant := Session.State.StageGrant.stage s p pending i runtime.1 frames stage.1 (reservation stage.1)
        have owned := grant.owned
        rw [free] at owned
        simp [Phase.busy, Phase.retained] at owned
      · have noCapture := Bool.eq_false_iff.mpr capture
        rw [s.core_clock_no_clear p pending i runtime noClear] at free
        have previous := engine_free_origin p s.core free
        change (Host.step (s.hostInput pending i) s.host).exportBits = 0#7
        simpa only [Host.step, cold, Bool.false_eq_true, ↓reduceIte, noClear, noAdmit, noCapture] using
          freeExport previous

theorem Session.State.FreeExport.started (s : Session.State a) (p : Program) (pending : Bool)
    (i : Session.Pins) (runtime : Session.RuntimeInput s i)
    (start : ((s.command i).runtime.command == 3 && s.core.canStart (s.command i).runtime) = true) :
    (s.step p pending i).FreeExport := by
  intro _
  have clear := s.accepted_clears pending i (Or.inl start)
  have cold : (s.hostInput pending i).initialize = false := runtime.1
  change (Host.step (s.hostInput pending i) s.host).exportBits = 0#7
  simp [Host.step, cold, clear]

theorem Session.State.FreeExport.run (s : Session.State a) (p : Program) (pending : Bool)
    (samples : List Session.Pins) (trace : BitTrace) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace p pending s samples) (custody : s.Custody trace)
    (freeExport : s.FreeExport) : (s.run p pending samples).FreeExport := by
  induction samples generalizing s trace with
  | nil => exact freeExport
  | cons i inputs induction =>
    exact induction (s.step p pending i) (trace.step s.core (s.command i).runtime) runtime.2
      (custody.step s p pending i trace ha runtime.1)
      (freeExport.step s p pending i runtime.1 custody.control.frames custody.reservation)

/-- Allocation of the next owner cannot discard an unacknowledged old interval. -/
theorem Session.State.FreeExport.start_empty (s : Session.State a) (i : Session.Pins)
    (freeExport : s.FreeExport) (interval : s.ExportInterval)
    (admitted : s.core.canStart (s.command i).runtime = true) :
    s.host.exportBits = 0#7 ∧ s.host.unacknowledged = false := by
  have free : s.core.phase = .free := by
    simp only [State.canStart, Bool.and_eq_true, beq_iff_eq] at admitted
    exact admitted.1.1
  have empty := freeExport free
  exact ⟨empty, by simp [Host.State.unacknowledged, Host.State.exportEnd, empty, interval.ack]⟩

end Pinwheel.Program.StreamingReady
