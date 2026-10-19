import Pinwheel.Program.StreamingUARTStartPins
import Pinwheel.Program.StreamingReadyOwnerCut

/-! The checked START control trace is transported through the simultaneous
source feedback. Rejection, START admission and the six MARK arming clocks are
consequences of the installed free state. -/
namespace Pinwheel.Program.StreamingUART.Start
open Pinwheel.Program.StreamingReady
set_option linter.unusedSimpArgs false

inductive CoreCut (p : Profile) : Bool → Nat → State a → Prop
  | free (s : State a) (phase : s.phase = .free) (generation : s.generation = 1) (transfer : s.transfer = 0) :
      CoreCut p false 0 s
  | running (seed : State a) (start : Input) (elapsed : Nat)
      (generation : seed.generation = 1) (transfer : seed.transfer = 0) (count : start.startCount = 8) :
      CoreCut p true elapsed (run (image p).program (seed.start (image p).program start) (List.replicate elapsed Arm.mark))

theorem CoreCut.advance (p : Profile) (s : State a) (c : Pinwheel.Program.Streaming.Host.Command)
    (cut : CoreCut p started elapsed s)
    (delivery : StartPins.Delivery started elapsed c nextStarted nextElapsed) :
    CoreCut p nextStarted nextElapsed (step (image p).program c.runtime s) ∧
      (s.status false c.runtime).rejected = false ∧ c.runtime.Runtime := by
  cases delivery with
  | quiet safe command =>
    have quiet : QuietTiming.Quiet c.runtime := ⟨safe.cold,command,safe.tx,safe.rx⟩
    refine ⟨?_,StartFacts.quiet_rejected s c.runtime false quiet,⟨safe.cold,by rw [command]; decide⟩⟩
    cases cut with
    | free s phase generation transfer =>
      rw [StartFacts.free_quiet_step _ _ _ phase quiet]
      exact .free _ phase generation transfer
    | running seed start elapsed generation transfer count =>
      rw [HostQuiet.step_canonical _ _ _ quiet,safe.raw]
      have append : List.replicate (elapsed+1) Arm.mark = List.replicate elapsed Arm.mark ++ [Arm.mark] := by
        simpa only [List.replicate_one] using
          (List.replicate_append_replicate (n := elapsed) (m := 1) (a := Arm.mark)).symm
      have next := CoreCut.running (p := p) seed start (elapsed+1) generation transfer count
      rw [append,QuietTiming.run_append] at next
      exact next
  | start safe before command generation count =>
    subst started
    cases cut with
    | free s phase oldGeneration transfer =>
      have genMatch : c.runtime.expectedGeneration = s.generation := generation.trans oldGeneration.symm
      have room : s.transfer ≠ 65535#16 := by rw [transfer]; decide
      have admitted := StartFacts.can_start s c.runtime phase genMatch room
      refine ⟨?_,StartFacts.start_rejected s c.runtime false command admitted safe.tx safe.rx,
        ⟨safe.cold,by rw [command]; decide⟩⟩
      rw [StartFacts.accepted_start _ _ _ safe.cold command phase genMatch room]
      exact .running s c.runtime 0 oldGeneration transfer count

theorem CoreCut.armed (p : Profile) (s : State a) (cut : CoreCut p true elapsed s) (long : 6 ≤ elapsed) :
    s = Arm.armed p 1 1 := by
  cases cut with
  | running seed start elapsed generation transfer count =>
    have length : elapsed = 6+(elapsed-6) := by omega
    rw [length,← List.replicate_append_replicate,QuietTiming.run_append,Arm.six_from_start p seed start count,
      Arm.run_armed,generation,transfer]
    rfl

theorem command_project (s : Session.State a) (pin : Session.Pins) (control : StartPins.Control)
    (project : Pinwheel.Program.Streaming.Host.BootControl.project s.host = control) :
    s.command pin = Pinwheel.Program.Streaming.Host.BootControl.command (pin.host {}) control := by
  exact (Pinwheel.Program.Streaming.Host.BootControl.command_correct (pin.host {}) s.host).trans (congrArg (Pinwheel.Program.Streaming.Host.BootControl.command (pin.host {})) project)

/-- Every physical edge is an actual source edge; the certificate constrains
framed commands, not a postulated source execution or sampled outcome. -/
theorem certified_run (p : Profile) (s : Session.State a) (control : StartPins.Control)
    (samples : List Session.Pins) (certificate : StartPins.Certified control started elapsed samples)
    (project : Pinwheel.Program.Streaming.Host.BootControl.project s.host = control) (cut : CoreCut p started elapsed s.core) :
    (s.run (image p).program false samples).core = Arm.armed p 1 1 ∧
      HostQuiet.Idle (s.run (image p).program false samples).host ∧
      Session.RuntimeTrace (image p).program false s samples := by
  induction certificate generalizing s with
  | nil control started elapsed done long phase inactive =>
    subst started
    exact ⟨cut.armed p s.core long,
      ⟨(congrArg Pinwheel.Program.Streaming.Host.BootControl.State.phase project).trans phase,
       (congrArg Pinwheel.Program.Streaming.Host.BootControl.State.active project).trans inactive⟩,trivial⟩
  | @cons control started elapsed pin rest nextStarted nextElapsed safe delivery after induction =>
    have command := command_project s pin control project
    have next := cut.advance p s.core (s.command pin) (by rw [command]; exact delivery)
    have reject : (s.hostInput false pin).status.rejected = false := next.2.1
    have nextProject : Pinwheel.Program.Streaming.Host.BootControl.project (s.step (image p).program false pin).host =
        Pinwheel.Program.Streaming.Host.BootControl.step false (pin.host {}) control := by
      change Pinwheel.Program.Streaming.Host.BootControl.project (Pinwheel.Program.Streaming.Host.step (s.hostInput false pin) s.host) = _
      rw [Pinwheel.Program.Streaming.Host.BootControl.step_correct _ _ (by rw [project]; exact safe),reject,project]
      rfl
    have result := induction (s.step (image p).program false pin) nextProject next.1
    refine ⟨result.1,result.2.1,?_,result.2.2⟩
    have runtime := next.2.2
    refine ⟨runtime.1,runtime.2,?_,?_⟩
    all_goals
      have allowed : (s.command pin).runtime.command = 0 ∨ (s.command pin).runtime.command = 3 := by
        rw [command]
        cases delivery with
        | quiet safe zero => exact Or.inl zero
        | start safe before three generation count => exact Or.inr three
      rcases allowed with zero | three
      · rw [zero]; decide
      · rw [three]; decide

def OwnedCut (started : Bool) (s : Session.State a) : Prop :=
  if started then ∃ trace : BitTrace, s.Custody trace ∧ s.FreeExport else True

theorem owned_advance (p : Profile) (s : Session.State a) (pin : Session.Pins)
    (ha : a ≤ 3) (control : s.host.ControlSafe)
    (cut : CoreCut p started elapsed s.core) (owned : OwnedCut started s)
    (delivery : StartPins.Delivery started elapsed (s.command pin) nextStarted nextElapsed)
    (runtime : Session.RuntimeInput s pin) :
    OwnedCut nextStarted (s.step (image p).program false pin) := by
  cases delivery with
  | quiet safe command =>
    cases started
    · trivial
    · obtain ⟨trace,custody,freeExport⟩ := owned
      exact ⟨trace.step s.core (s.command pin).runtime,
        custody.step s (image p).program false pin trace ha runtime,
        freeExport.step s (image p).program false pin runtime custody.control.frames custody.reservation⟩
  | start safe before command generation count =>
    subst started
    cases cut with
    | free core phase oldGeneration transfer =>
      have admitted : ((s.command pin).runtime.command == 3 && s.core.canStart (s.command pin).runtime) = true := by
        rw [command,StartFacts.can_start s.core (s.command pin).runtime phase
          (generation.trans oldGeneration.symm) (by rw [transfer]; decide)]
        rfl
      exact ⟨{},Session.State.Custody.started s (image p).program false pin runtime control admitted,
        Session.State.FreeExport.started s (image p).program false pin runtime admitted⟩

theorem certified_custody (p : Profile) (s : Session.State a) (control : StartPins.Control)
    (samples : List Session.Pins) (certificate : StartPins.Certified control started elapsed samples)
    (project : Pinwheel.Program.Streaming.Host.BootControl.project s.host = control)
    (cut : CoreCut p started elapsed s.core) (ha : a ≤ 3) (safeHost : s.host.ControlSafe)
    (owned : OwnedCut started s) :
    ∃ trace : BitTrace, (s.run (image p).program false samples).Custody trace ∧
      (s.run (image p).program false samples).FreeExport := by
  induction certificate generalizing s with
  | nil control started elapsed done long phase inactive =>
    subst started
    exact owned
  | @cons control started elapsed pin rest nextStarted nextElapsed safe delivery after induction =>
    have command := command_project s pin control project
    have actualDelivery : StartPins.Delivery started elapsed (s.command pin) nextStarted nextElapsed := by rw [command]; exact delivery
    have next := cut.advance p s.core (s.command pin) actualDelivery
    have reject : (s.hostInput false pin).status.rejected = false := next.2.1
    have nextProject : Pinwheel.Program.Streaming.Host.BootControl.project (s.step (image p).program false pin).host =
        Pinwheel.Program.Streaming.Host.BootControl.step false (pin.host {}) control := by
      change Pinwheel.Program.Streaming.Host.BootControl.project (Pinwheel.Program.Streaming.Host.step (s.hostInput false pin) s.host) = _
      rw [Pinwheel.Program.Streaming.Host.BootControl.step_correct _ _ (by rw [project]; exact safe),reject,project]
      rfl
    have runtime := (certified_run p s control (pin::rest) (.cons safe delivery after) project cut).2.2.1
    exact induction (s.step (image p).program false pin) nextProject next.1
      (s.host.controlSafe_step _ safeHost) (owned_advance p s pin ha safeHost cut owned actualDelivery runtime)

end Pinwheel.Program.StreamingUART.Start
