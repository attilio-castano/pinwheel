import Pinwheel.Hardware.Reactive.Equations

namespace Pinwheel.Hardware.Reactive.Fetch

/-- Context and registers from one input/pre-edge snapshot. `successor` is replaced
by `resolve`; it cannot affect address selection. No extra execution cycle is added. -/
structure Request where
  context : Inputs
  core : State

abbrev Request.address (r : Request) : BitVec 8 := targetValue r.context r.core

/-- A combinational reader of the selected, pre-edge program image. A synchronous
memory needs a separate availability/prefetch contract before implementing this API. -/
abbrev Reader := BitVec 8 → BitVec 64

abbrev CurrentValid (core : State) (current : BitVec 64) (read : Reader) : Prop :=
  runningValue core = true → current = read core.pc

/-- Resolve the selected word before the scheduler computes this edge's updates. -/
abbrev resolve (context : Inputs) (core : State) (read : Reader) : Inputs :=
  {context with successor := read (Request.address ⟨context, core⟩)}

theorem address_resolved (r : Request) (read : Reader) :
    Request.address ⟨resolve r.context r.core read, r.core⟩ = r.address := by
  rfl

theorem resolve_congr (r : Request) (left right : Reader)
    (h : left r.address = right r.address) :
    resolve r.context r.core left = resolve r.context r.core right := by
  simp only [resolve, h]
  done

theorem branch_uses_terminal_capture (r : Request)
    (hr : runningValue r.core = true) (hm : r.core.mode = 3)
    (hf : (Execution.unpack r.context.current).finish = 2) :
    r.address = if (terminalValues r.context r.core)[(Execution.unpack r.context.current).sample.toNat]
      then (Execution.unpack r.context.current).yes else (Execution.unpack r.context.current).no := by
  simp [Request.address, targetValue, sequentialValue, hr, hm, hf]
  done

end Pinwheel.Hardware.Reactive.Fetch
