import Pinwheel.Compile.UARTRxProofs
import Pinwheel.Hardware.Storage.Capacity
import Pinwheel.Engine.FetchProofs

/-! Receive programs use the existing wide E64 path. PWL version 0 is unchanged. -/
namespace Pinwheel.Hardware.UARTRx
open Engine.Reactive
open Compile.UARTRx

def words (cfg : UART.Rx.Config) : Execution.Words := Execution.imageWords (program cfg)

/-- Load-time rejection remains explicit; an accepted dictionary certifies all 256 lookups. -/
def compact (cfg : UART.Rx.Config) :
    Option {m : Storage.Indexed32 // m.expand = words cfg} := Storage.lower32 (words cfg)

theorem direct_step (cfg : UART.Rx.Config) (s : UART.Rx.State)
    (resetRequested startRequested : Bool) (inputs : Inputs) (h : UART.Rx.WellFormed cfg s) :
    Fetch.step (Execution.directStore (words cfg) (program cfg).idle (program cfg).last)
      (lift cfg s) resetRequested startRequested inputs =
      lift cfg (UART.Rx.step cfg s resetRequested startRequested inputs[cfg.input.val]) := by
  unfold words
  rw [Fetch.step_eq _ _ (Execution.direct_agrees (program cfg)), step_simulation cfg s _ _ _ h]
  done

theorem compact_step (cfg : UART.Rx.Config) (image : Storage.Indexed32)
    (accepted : image.expand = words cfg) (s : UART.Rx.State)
    (resetRequested startRequested : Bool) (inputs : Inputs) (h : UART.Rx.WellFormed cfg s) :
    Fetch.step (image.store (program cfg)) (lift cfg s) resetRequested startRequested inputs =
      lift cfg (UART.Rx.step cfg s resetRequested startRequested inputs[cfg.input.val]) := by
  rw [Fetch.step_eq _ _ (Storage.indexed32_agrees (program cfg) image accepted),
    step_simulation cfg s _ _ _ h]
  done

theorem compact_run (cfg : UART.Rx.Config) (image : Storage.Indexed32)
    (accepted : image.expand = words cfg) (s : UART.Rx.State)
    (incoming : Nat → Inputs) (h : UART.Rx.WellFormed cfg s) (n : Nat) :
    Fetch.run (image.store (program cfg)) (lift cfg s) incoming n =
      lift cfg (UART.Rx.run cfg s (fun t => (incoming t)[cfg.input.val]) n) := by
  rw [Fetch.run_eq _ _ (Storage.indexed32_agrees (program cfg) image accepted),
    run_simulation cfg s incoming h n]
  done

end Pinwheel.Hardware.UARTRx
