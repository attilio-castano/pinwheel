import Pinwheel.Compile.I2CLoopProofs

namespace Pinwheel.Compile.I2CLoop
open Engine.Reactive

theorem store_agrees (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request) :
    Fetch.Agrees (program cfg r).store (I2C.program cfg r) := by
  exact ⟨fetch_eq cfg r, rfl, rfl⟩
  done

/-- Entire state equality also covers reset/start requests and every malformed starting state. -/
theorem step_eq (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request)
    (s : State) (resetRequested startRequested : Bool) (inputs : Inputs) :
    Fetch.step (program cfg r).store s resetRequested startRequested inputs =
      step (I2C.program cfg r) s resetRequested startRequested inputs := by
  exact Fetch.step_eq _ _ (store_agrees cfg r) s resetRequested startRequested inputs
  done

def execute (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) : State :=
  Fetch.run (program cfg r).store
    (Fetch.start (program cfg r).store (I2C.encodeInputs (incoming 0)))
    (fun t => I2C.encodeInputs (incoming t)) n

/-- No extra bookkeeping cycles: the full state equals the explicit engine at every edge. -/
theorem execute_eq (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    execute cfg r incoming n = I2C.execute cfg r incoming n := by
  simp only [execute, I2C.execute, Fetch.run_eq _ _ (store_agrees cfg r), Fetch.start,
    start, Fetch.enter_eq _ _ (store_agrees cfg r)]
  done

theorem waveform_correct (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    (execute cfg r incoming n).pins =
      I2C.encodePins (Pinwheel.I2C.pins (Pinwheel.I2C.run cfg (Pinwheel.I2C.initial cfg r) incoming n)) := by
  simpa only [execute_eq] using I2C.waveform_correct cfg r incoming n
  done

theorem result_correct (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    I2C.outcome (execute cfg r incoming n) =
      Pinwheel.I2C.result (Pinwheel.I2C.run cfg (Pinwheel.I2C.initial cfg r) incoming n) := by
  simpa only [execute_eq] using I2C.result_correct cfg r incoming n
  done

theorem busy_correct (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    busy (execute cfg r incoming n) =
      Pinwheel.I2C.busy (Pinwheel.I2C.run cfg (Pinwheel.I2C.initial cfg r) incoming n) := by
  simpa only [execute_eq] using I2C.busy_correct cfg r incoming n
  done

end Pinwheel.Compile.I2CLoop
