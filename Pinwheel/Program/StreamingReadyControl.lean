import Pinwheel.Program.StreamingReadyCounting

namespace Pinwheel.Program.StreamingReady

theorem step_busy_eq_clock (p : Program) (s : State a) (i : Input)
    (runtime : i.Runtime) (busy : s.phase.busy = true) : step p i s = clock p i s := by
  rcases runtime with ⟨cold,warm⟩
  change i.command ≠ 15#4 at warm
  cases phase : s.phase <;> simp [phase,Phase.busy] at busy
  all_goals simp [step,cold,warm,State.canStart,State.canRelease,phase,Phase.retained]

theorem engine_live (p : Program) (s : State a) (busy : s.phase.busy = true) :
    (engine p s).phase.busy = true ∨ (engine p s).phase.retained = true := by
  cases phase : s.phase
  case waiting =>
    cases ready : s.waitReady <;> cases stream : s.current.isStream <;>
      cases expired : s.current.guard.limit.expires s.countdown <;>
      simp [engine,phase,ready,stream,expired,State.enterHigh,State.captureData,State.timeoutFault,
        Phase.busy,Phase.retained]
  all_goals simp [phase,Phase.busy] at busy
  all_goals simp only [engine,phase]
  all_goals repeat' first | exact Or.inl rfl | exact Or.inr rfl | exact Or.inl busy | split
  all_goals simp [phase,Phase.busy]

end Pinwheel.Program.StreamingReady
