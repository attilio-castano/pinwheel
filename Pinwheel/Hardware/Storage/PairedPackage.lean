import Pinwheel.Hardware.Storage.PairedLifecycle

/-! The retained package with its actual sampling, decoding and mailbox edges.
The loader status remains the proved graph's status. E64 supplies execution
observations; the mailbox consumes them on the existing, unmodified edge. -/
namespace Pinwheel.Hardware.Storage.PairedPackage
open Pinwheel.Hardware PairedController PairedComposition
open SramController (Reads Out bypass)
set_option backward.isDefEq.respectTransparency false

private theorem inner_values (r : Values R) (x : Values X) :
    (Extended.innerValues (Extended.values r x) : Values R) = (r : Values R) := rfl

private theorem extra_values (r : Values R) (x : Values X) :
    (Extended.extraValues (Extended.values r x) : Values X) = (x : Values X) := rfl

theorem bypass_feed (f : Feeder J X I) (i : Values J) (x : Values X) (q : BitVec 64) :
    ((bypass f).feed (PairedClosed.feedback i q) x : Values (Reads I)) =
      (PairedClosed.feedback (f.feed i x) q : Values (Reads I)) := by
  funext w p
  cases p <;> simp only [Feeder.feed, bypass, Expr.eval_bind, PairedClosed.feedback, Expr.eval]
  done

theorem bypass_step (f : Feeder J X I) (i : Values J) (x : Values X) (q : BitVec 64) :
    ((bypass f).step (PairedClosed.feedback i q) x : Values X) = (f.step i x : Values X) := by
  funext w r
  simp only [Feeder.step, bypass, Expr.eval_bind, PairedClosed.feedback, Expr.eval]
  done

theorem observer_expr (e : HostResult.E w) (i : Values Chip.Pin) (o : Values (Out Loader.Machine.Output))
    (x : Values HostResult.Register) (q : BitVec 64) :
    (SramAssembly.observerExpr e).eval (Observed.values (PairedClosed.feedback i q) o) x =
      e.eval (Observed.values i (fun {_} p => o (.base p))) x := by
  simp only [SramAssembly.observerExpr, Expr.eval_bind, Expr.eval]
  congr 1
  funext w p
  cases p <;> rfl
  done

theorem observer_next (i : Values Chip.Pin) (o : Values (Out Loader.Machine.Output))
    (x : Values HostResult.Register) (q : BitVec 64) (r : HostResult.Register w) :
    (SramAssembly.observer.next r).eval (Observed.values (PairedClosed.feedback i q) o) x =
      (HostResult.observer.next r).eval (Observed.values i (fun {_} p => o (.base p))) x :=
  observer_expr _ i o x q

theorem observer_output (i : Values Chip.Pin) (o : Values (Out Loader.Machine.Output))
    (x : Values HostResult.Register) (q : BitVec 64) (p : Chip.Output w) :
    (SramAssembly.observer.output (.base p)).eval (Observed.values (PairedClosed.feedback i q) o) x =
      (HostResult.observer.output p).eval (Observed.values i (fun {_} p => o (.base p))) x :=
  observer_expr _ i o x q

def decoded (x : Chip.State) : Loader.Machine.Inputs := Serial.feed x.second x.receiver

def adaptersNext (i : Chip.Pins) (x : Chip.State) : Chip.State :=
  ⟨Chip.wired i, x.first, Serial.next x.second x.receiver⟩

private theorem pin_feed (i : Chip.Pins) :
    (Chip.pinMap.feed i.values (Chip.pinModel.state ()) : Values Serial.Input) =
      ((Chip.wired i).values : Values Serial.Input) := Chip.pinModel.feed_eq i ()

private theorem pin_step (i : Chip.Pins) :
    (Chip.pinMap.step i.values (Chip.pinModel.state ()) : Values NoRegister) =
      (Chip.pinModel.state () : Values NoRegister) := Chip.pinModel.step_eq i ()

private theorem sampler_feed (i a b : Serial.Inputs) :
    (Feeder.sampler.feed i.values (Chip.sampling.state (a, b)) : Values Serial.Input) =
      (b.values : Values Serial.Input) := Chip.sampling.feed_eq i (a, b)

private theorem sampler_step (i a b : Serial.Inputs) :
    (Feeder.sampler.step i.values (Chip.sampling.state (a, b)) : Values (Feeder.Sampled Serial.Input)) =
      (Chip.sampling.state (i, a) : Values (Feeder.Sampled Serial.Input)) := Chip.sampling.step_eq i (a, b)

private theorem serial_feed (i : Serial.Inputs) (s : Serial.State) :
    (Serial.receiver.feed i.values s.values : Values Loader.Machine.Input) =
      ((Serial.feed i s).values : Values Loader.Machine.Input) := Serial.model.feed_eq i s

private theorem serial_step (i : Serial.Inputs) (s : Serial.State) :
    (Serial.receiver.step i.values s.values : Values Serial.Register) =
      ((Serial.next i s).values : Values Serial.Register) := Serial.model.step_eq i s

def registers (core : Values Register) (x : Chip.State) (result : HostResult.State) : Values FullRegister :=
  Extended.values (Chip.values core x) result.values

structure State (S : Type) where
  core : Values Register × S
  adapters : Chip.State
  result : HostResult.State

def State.physical (s : State S) : Values FullRegister × S :=
  (registers s.core.1 s.adapters s.result, s.core.2)

def coreOutput (memory : Memory.SinglePort.Contract S 9 64) (s : State S) : Values Loader.Machine.Output :=
  (PairedClosed.implementation graph memory).observe (decoded s.adapters).values s.core

def interpreted (memory : Memory.SinglePort.Contract S 9 64) : Timed.Component Chip.Pins (State S) (Values Chip.Output) where
  step := fun i s => ⟨(PairedClosed.implementation graph memory).step (decoded s.adapters).values s.core,
    adaptersNext i s.adapters, HostResult.next i (coreOutput memory s) s.result⟩
  observe := fun _ s => HostResult.shown (coreOutput memory s) s.result

def executable (c : Component (Reads Chip.Pin) FullRegister (Out Chip.Output))
    (memory : Memory.SinglePort.Contract S 9 64) :
    Timed.Component Chip.Pins (Values FullRegister × S) (Values Chip.Output) where
  step := fun i => (PairedClosed.implementation c memory).step i.values
  observe := fun i => (PairedClosed.implementation c memory).observe i.values

theorem step_physical (memory : Memory.SinglePort.Contract S 9 64) (i : Chip.Pins) (s : State S) :
    (executable (packaged graph) memory).step i s.physical = ((interpreted memory).step i s).physical := by
  apply Prod.ext
  case fst =>
    funext w r
    cases r
    all_goals simp only [executable, PairedClosed.implementation, PairedClosed.closed, State.physical,
      registers, Chip.values, packaged, observed, fed, inner_values, extra_values,
      Extended.values, bypass_feed, bypass_step, pin_feed, sampler_feed,
      serial_feed, pin_step, sampler_step, serial_step,
      interpreted, adaptersNext, decoded]
    exact (observer_next _ _ _ _ _).trans (HostResult.next_correct i (coreOutput memory s) s.result _)
    done
  case snd =>
    simp only [executable, PairedClosed.implementation, PairedClosed.closed, State.physical,
      registers, Chip.values, packaged, observed, fed, inner_values, extra_values, bypass_feed,
      pin_feed, sampler_feed, serial_feed, interpreted, decoded, PairedClosed.command,
      SramAssembly.observer, Observed.values, Expr.eval]
    done

theorem observe_physical (memory : Memory.SinglePort.Contract S 9 64) (i : Chip.Pins) (s : State S) :
    ((executable (packaged graph) memory).observe i s.physical : Values Chip.Output) =
      ((interpreted memory).observe i s : Values Chip.Output) := by
  funext w p
  simp only [executable, PairedClosed.implementation, PairedClosed.closed, State.physical,
    registers, Chip.values, packaged, observed, fed, inner_values, extra_values, bypass_feed,
    pin_feed, sampler_feed, serial_feed, interpreted, observer_output]
  exact HostResult.output_correct i (coreOutput memory s) s.result p
  done

/-- All package output pins, before and after every edge, for arbitrary input
histories and arbitrary represented core, adapter, mailbox and memory states. -/
theorem retained_trace
    (n : Netlist Register (Out Loader.Machine.Output) Input) (hn : PairedValidation.core = .ok n)
    (memory : Memory.SinglePort.Contract S 9 64) (s : State S) (history : List Chip.Pins) :
    (executable (package n).component memory).trace s.physical history =
      (interpreted memory).trace s history := by
  rw [retained_package_correct n hn]
  induction history generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [Timed.Component.trace, Timed.Component.edge, step_physical, observe_physical, ih]
  done

theorem retained_run
    (n : Netlist Register (Out Loader.Machine.Output) Input) (hn : PairedValidation.core = .ok n)
    (memory : Memory.SinglePort.Contract S 9 64) (s : State S) (history : List Chip.Pins) :
    (executable (package n).component memory).run s.physical history =
      ((interpreted memory).run s history).physical := by
  rw [retained_package_correct n hn]
  induction history generalizing s with
  | nil => rfl
  | cons i rest ih => simpa only [Timed.Component.run, step_physical] using ih ((interpreted memory).step i s)

end Pinwheel.Hardware.Storage.PairedPackage
