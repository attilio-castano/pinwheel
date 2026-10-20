import Pinwheel.Program.BufferedSPI
import Pinwheel.Program.TransferProofs

/-! Equations for the existing buffered source interpreter, used by the SPI
packed-circuit refinement. These lemmas do not introduce an alternative source
machine or assume equality with hardware observations. -/
namespace Pinwheel.Hardware.Buffered.SpiInterpreter
open Pinwheel.Program Pinwheel.Engine.Reactive

theorem advance_stopped (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (reason : Stop)
    (control : s.core.control = .stopped reason) (incoming : Inputs) :
    Program.Buffered.advance p capacity s incoming = s := by
  simp [Program.Buffered.advance, busy, control]

theorem advance_countdown (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (pc : Program.Buffered.PC) (remaining : Fin 256)
    (owner : Program.Buffered.owned s = true)
    (control : s.core.control = .active pc remaining) (positive : 0 < remaining.val)
    (incoming : Inputs) :
    Program.Buffered.advance p capacity s incoming =
      {s with
        core := {s.core with control := .active pc ⟨remaining.val - 1, by omega⟩}
        samplerFirst := incoming
        samplerSecond := s.samplerFirst} := by
  simp [Program.Buffered.advance, owner, busy, control, Fetch.advance,
    Program.Buffered.entryTarget, Program.Buffered.settle, positive,
    show remaining ≠ 0 by omega]

theorem advance_dispatch (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (pc : Program.Buffered.PC)
    (owner : Program.Buffered.owned s = true)
    (control : s.core.control = .active pc 0) (bound : pc.val < p.last.val)
    (incoming : Inputs) :
    Program.Buffered.advance p capacity s incoming =
      let target : Program.Buffered.PC := ⟨pc.val + 1, by have := p.last.isLt; omega⟩
      Program.Buffered.settle p capacity
        (Program.Buffered.entryEffects p capacity
          {s with
            core := Fetch.enter (Program.Buffered.lower p s) target s.core.samples s.samplerSecond
            samplerFirst := incoming
            samplerSecond := s.samplerFirst}
          target s.samplerSecond) := by
  simp [Program.Buffered.advance, owner, busy, control, Fetch.advance, Fetch.next,
    Program.Buffered.entryTarget, Program.Buffered.sequentialTarget, bound,
    Program.Buffered.lower]

theorem enter_low (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (pc : Program.Buffered.PC) (duration : Fin 256) (samples : Vector Bool 16)
    (sampled : Inputs) (fetch : p.fetch pc = some (BufferedSPI.low duration)) :
    Fetch.enter (Program.Buffered.lower p s) pc samples sampled =
      ⟨.active pc duration,
        Program.Buffered.shiftPins ⟨0, 7⟩ 0 false false (Program.Buffered.txBit s), samples⟩ := by
  simp [Fetch.enter, Program.Buffered.lower, fetch, Program.Buffered.normalize,
    BufferedSPI.low, capture]

theorem enter_high (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (pc : Program.Buffered.PC) (duration : Fin 256) (samples : Vector Bool 16)
    (sampled : Inputs) (fetch : p.fetch pc = some (BufferedSPI.high duration)) :
    Fetch.enter (Program.Buffered.lower p s) pc samples sampled =
      ⟨.active pc duration, Program.Buffered.keepPins ⟨2, 7⟩ s.core.pins 1 0, samples⟩ := by
  simp [Fetch.enter, Program.Buffered.lower, fetch, Program.Buffered.normalize,
    BufferedSPI.high, capture]

theorem enter_release (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (pc : Program.Buffered.PC) (duration : Fin 256) (samples : Vector Bool 16)
    (sampled : Inputs) (fetch : p.fetch pc = some (BufferedSPI.release duration)) :
    Fetch.enter (Program.Buffered.lower p s) pc samples sampled =
      ⟨.active pc duration, ⟨0, 7⟩, samples⟩ := by
  simp [Fetch.enter, Program.Buffered.lower, fetch, Program.Buffered.normalize,
    BufferedSPI.release, capture]

theorem enter_halt (p : Program.Buffered.Program) (s : Program.Buffered.State)
    (pc : Program.Buffered.PC) (samples : Vector Bool 16) (sampled : Inputs)
    (fetch : p.fetch pc = some BufferedSPI.halt) :
    Fetch.enter (Program.Buffered.lower p s) pc samples sampled =
      ⟨.stopped .completed, p.idle, samples⟩ := by
  simp [Fetch.enter, Program.Buffered.lower, fetch, Program.Buffered.normalize,
    BufferedSPI.halt, Fetch.stop]

theorem consumed_available (capacity : Transfer.Capacity) (s : Program.Buffered.State)
    (e : Transfer.Execution) (bit : Bool) (running : s.buffers.slot = .running e)
    (owner : e.request.identity = s.owner)
    (available : e.request.tx[e.txConsumed]? = some bit) :
    Program.Buffered.consumed capacity s =
      ({s with buffers := {s.buffers with
        slot := .running {e with txConsumed := e.txConsumed + 1}}}, true) := by
  simp [Program.Buffered.consumed, Transfer.step, Transfer.Command.identity,
    running, Transfer.Slot.identity, owner, Transfer.admittedStep, available]

theorem consumed_exhausted (capacity : Transfer.Capacity) (s : Program.Buffered.State)
    (e : Transfer.Execution) (running : s.buffers.slot = .running e)
    (owner : e.request.identity = s.owner)
    (exhausted : e.request.tx[e.txConsumed]? = none) :
    Program.Buffered.consumed capacity s = (s, false) := by
  simp [Program.Buffered.consumed, Transfer.step, Transfer.Command.identity,
    running, Transfer.Slot.identity, owner, Transfer.admittedStep, exhausted,
    Transfer.reject]

theorem appended_room (capacity : Transfer.Capacity) (s : Program.Buffered.State)
    (e : Transfer.Execution) (input : Fin 2) (sampled : Inputs)
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner)
    (room : e.rx.length < e.request.rxLimit) :
    Program.Buffered.appended capacity s input sampled =
      ({s with buffers := {s.buffers with
        slot := .running {e with rx := e.rx ++ [sampled[input.val]]}}}, true) := by
  simp [Program.Buffered.appended, Transfer.step, Transfer.Command.identity,
    running, Transfer.Slot.identity, owner, Transfer.admittedStep, room]

theorem appended_full (capacity : Transfer.Capacity) (s : Program.Buffered.State)
    (e : Transfer.Execution) (input : Fin 2) (sampled : Inputs)
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner)
    (full : ¬ e.rx.length < e.request.rxLimit) :
    Program.Buffered.appended capacity s input sampled = (s, false) := by
  simp [Program.Buffered.appended, Transfer.step, Transfer.Command.identity,
    running, Transfer.Slot.identity, owner, Transfer.admittedStep, full, Transfer.reject]

theorem terminal_running (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (e : Transfer.Execution) (outcome : Transfer.Outcome)
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner) :
    Program.Buffered.terminal p capacity s outcome =
      {s with
        core := ⟨.stopped (match outcome with
          | .complete => .completed | .fault => .fault | .timeout => .timeout),
          p.idle, s.core.samples⟩
        buffers := {s.buffers with slot := .completed ⟨e, outcome⟩}} := by
  simp [Program.Buffered.terminal, Program.Buffered.lower, Fetch.stop,
    Transfer.step, Transfer.Command.identity, running, Transfer.Slot.identity,
    owner, Transfer.admittedStep]
  rfl

theorem effects_low_available (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (e : Transfer.Execution) (pc : Program.Buffered.PC)
    (duration : Fin 256) (sampled : Inputs) (bit : Bool)
    (healthy : s.core.control ≠ .stopped .fault)
    (fetch : p.fetch pc = some (BufferedSPI.low duration))
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner)
    (available : e.request.tx[e.txConsumed]? = some bit) :
    Program.Buffered.entryEffects p capacity s pc sampled =
      {s with buffers := {s.buffers with
        slot := .running {e with txConsumed := e.txConsumed + 1}}} := by
  simp [Program.Buffered.entryEffects, healthy, fetch, BufferedSPI.low,
    consumed_available capacity s e bit running owner available]

theorem effects_low_exhausted (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (e : Transfer.Execution) (pc : Program.Buffered.PC)
    (duration : Fin 256) (sampled : Inputs)
    (healthy : s.core.control ≠ .stopped .fault)
    (fetch : p.fetch pc = some (BufferedSPI.low duration))
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner)
    (exhausted : e.request.tx[e.txConsumed]? = none) :
    Program.Buffered.entryEffects p capacity s pc sampled =
      Program.Buffered.terminal p capacity s .fault := by
  simp [Program.Buffered.entryEffects, healthy, fetch, BufferedSPI.low,
    consumed_exhausted capacity s e running owner exhausted]

theorem effects_high_room (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (e : Transfer.Execution) (pc : Program.Buffered.PC)
    (duration : Fin 256) (sampled : Inputs)
    (healthy : s.core.control ≠ .stopped .fault)
    (fetch : p.fetch pc = some (BufferedSPI.high duration))
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner)
    (room : e.rx.length < e.request.rxLimit) :
    Program.Buffered.entryEffects p capacity s pc sampled =
      {s with buffers := {s.buffers with
        slot := .running {e with rx := e.rx ++ [sampled[0]]}}} := by
  simp [Program.Buffered.entryEffects, healthy, fetch, BufferedSPI.high,
    appended_room capacity s e 0 sampled running owner room]

theorem effects_high_full (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (e : Transfer.Execution) (pc : Program.Buffered.PC)
    (duration : Fin 256) (sampled : Inputs)
    (healthy : s.core.control ≠ .stopped .fault)
    (fetch : p.fetch pc = some (BufferedSPI.high duration))
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner)
    (full : ¬ e.rx.length < e.request.rxLimit) :
    Program.Buffered.entryEffects p capacity s pc sampled =
      Program.Buffered.terminal p capacity s .fault := by
  simp [Program.Buffered.entryEffects, healthy, fetch, BufferedSPI.high,
    appended_full capacity s e 0 sampled running owner full]

theorem effects_release (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (pc : Program.Buffered.PC) (duration : Fin 256)
    (sampled : Inputs) (fetch : p.fetch pc = some (BufferedSPI.release duration)) :
    Program.Buffered.entryEffects p capacity s pc sampled = s := by
  simp [Program.Buffered.entryEffects, fetch, BufferedSPI.release]

theorem effects_halt (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (pc : Program.Buffered.PC) (sampled : Inputs)
    (fetch : p.fetch pc = some BufferedSPI.halt) :
    Program.Buffered.entryEffects p capacity s pc sampled = s := by
  simp [Program.Buffered.entryEffects, fetch, BufferedSPI.halt]

theorem fetch_zero (c : BufferedSPI.Config) :
    (BufferedSPI.program c).fetch 0 = some (BufferedSPI.low c.halfCyclesMinusOne) := by
  simp [BufferedSPI.fetch_shape]

theorem start_available (c : BufferedSPI.Config) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (e : Transfer.Execution) (bit : Bool)
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner)
    (available : e.request.tx[e.txConsumed]? = some bit) :
    Program.Buffered.start (BufferedSPI.program c) capacity s =
      {s with
        core := ⟨.active 0 c.halfCyclesMinusOne,
          Program.Buffered.shiftPins ⟨0, 7⟩ 0 false false bit, Vector.replicate 16 false⟩
        buffers := {s.buffers with slot := .running {e with txConsumed := e.txConsumed + 1}}} := by
  simp [Program.Buffered.start, Program.Buffered.owned, running, owner,
    Fetch.start, Fetch.enter, Program.Buffered.lower, fetch_zero,
    Program.Buffered.normalize, BufferedSPI.low, Program.Buffered.txBit, available,
    capture, Program.Buffered.entryEffects, Program.Buffered.consumed,
    Transfer.step, Transfer.Command.identity, Transfer.Slot.identity,
    Transfer.admittedStep, Program.Buffered.settle]

theorem start_exhausted (c : BufferedSPI.Config) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (e : Transfer.Execution)
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner)
    (exhausted : e.request.tx[e.txConsumed]? = none) :
    Program.Buffered.start (BufferedSPI.program c) capacity s =
      {s with
        core := ⟨.stopped .fault, (BufferedSPI.program c).idle, Vector.replicate 16 false⟩
        buffers := {s.buffers with slot := .completed ⟨e, .fault⟩}} := by
  simp [Program.Buffered.start, Program.Buffered.owned, running, owner,
    Fetch.start, Fetch.enter, Program.Buffered.lower, fetch_zero,
    Program.Buffered.normalize, BufferedSPI.low, Program.Buffered.txBit, exhausted,
    capture, Program.Buffered.entryEffects, Program.Buffered.consumed,
    Transfer.step, Transfer.Command.identity, Transfer.Slot.identity,
    Transfer.admittedStep, Transfer.reject, Program.Buffered.settle,
    Program.Buffered.terminal, Fetch.stop]

theorem advance_low_available (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (e : Transfer.Execution) (pc next : Program.Buffered.PC)
    (duration : Fin 256) (incoming : Inputs) (bit : Bool)
    (control : s.core.control = .active pc 0) (bound : pc.val < p.last.val)
    (successor : next.val = pc.val + 1)
    (fetch : p.fetch next = some (BufferedSPI.low duration))
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner)
    (available : e.request.tx[e.txConsumed]? = some bit) :
    Program.Buffered.advance p capacity s incoming =
      {s with
        core := ⟨.active next duration,
          Program.Buffered.shiftPins ⟨0, 7⟩ 0 false false bit, s.core.samples⟩
        buffers := {s.buffers with slot := .running {e with txConsumed := e.txConsumed + 1}}
        samplerFirst := incoming
        samplerSecond := s.samplerFirst} := by
  have nextEq : (⟨pc.val + 1, by have := p.last.isLt; omega⟩ : Program.Buffered.PC) = next :=
    Fin.ext successor.symm
  simp [Program.Buffered.advance, Program.Buffered.owned, running, owner, control,
    busy, Fetch.advance, Fetch.next, Fetch.enter, Program.Buffered.lower, bound, nextEq, fetch,
    Program.Buffered.normalize, BufferedSPI.low, Program.Buffered.txBit, available,
    capture, Program.Buffered.entryTarget, Program.Buffered.sequentialTarget,
    Program.Buffered.entryEffects, Program.Buffered.consumed, Transfer.step,
    Transfer.Command.identity, Transfer.Slot.identity, Transfer.admittedStep,
    Program.Buffered.settle]
  done

theorem advance_low_exhausted (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (e : Transfer.Execution) (pc next : Program.Buffered.PC)
    (duration : Fin 256) (incoming : Inputs)
    (control : s.core.control = .active pc 0) (bound : pc.val < p.last.val)
    (successor : next.val = pc.val + 1)
    (fetch : p.fetch next = some (BufferedSPI.low duration))
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner)
    (exhausted : e.request.tx[e.txConsumed]? = none) :
    Program.Buffered.advance p capacity s incoming =
      {s with
        core := ⟨.stopped .fault, p.idle, s.core.samples⟩
        buffers := {s.buffers with slot := .completed ⟨e, .fault⟩}
        samplerFirst := incoming
        samplerSecond := s.samplerFirst} := by
  have nextEq : (⟨pc.val + 1, by have := p.last.isLt; omega⟩ : Program.Buffered.PC) = next :=
    Fin.ext successor.symm
  simp [Program.Buffered.advance, Program.Buffered.owned, running, owner, control,
    busy, Fetch.advance, Fetch.next, Fetch.enter, Program.Buffered.lower, bound, nextEq, fetch,
    Program.Buffered.normalize, BufferedSPI.low, Program.Buffered.txBit, exhausted,
    capture, Program.Buffered.entryTarget, Program.Buffered.sequentialTarget,
    Program.Buffered.entryEffects, Program.Buffered.consumed, Transfer.step,
    Transfer.Command.identity, Transfer.Slot.identity, Transfer.admittedStep,
    Transfer.reject, Program.Buffered.settle, Program.Buffered.terminal, Fetch.stop]
  done

theorem advance_high_room (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (e : Transfer.Execution) (pc next : Program.Buffered.PC)
    (duration : Fin 256) (incoming : Inputs)
    (control : s.core.control = .active pc 0) (bound : pc.val < p.last.val)
    (successor : next.val = pc.val + 1)
    (fetch : p.fetch next = some (BufferedSPI.high duration))
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner)
    (room : e.rx.length < e.request.rxLimit) :
    Program.Buffered.advance p capacity s incoming =
      {s with
        core := ⟨.active next duration,
          Program.Buffered.keepPins ⟨2, 7⟩ s.core.pins 1 0, s.core.samples⟩
        buffers := {s.buffers with slot := .running {e with rx := e.rx ++ [s.samplerSecond[0]]}}
        samplerFirst := incoming
        samplerSecond := s.samplerFirst} := by
  have nextEq : (⟨pc.val + 1, by have := p.last.isLt; omega⟩ : Program.Buffered.PC) = next :=
    Fin.ext successor.symm
  simp [Program.Buffered.advance, Program.Buffered.owned, running, owner, control,
    busy, Fetch.advance, Fetch.next, Fetch.enter, Program.Buffered.lower, bound, nextEq, fetch,
    Program.Buffered.normalize, BufferedSPI.high, capture,
    Program.Buffered.entryTarget, Program.Buffered.sequentialTarget,
    Program.Buffered.entryEffects, Program.Buffered.appended, Transfer.step,
    Transfer.Command.identity, Transfer.Slot.identity, Transfer.admittedStep,
    room, Program.Buffered.settle]
  done

theorem advance_high_full (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (e : Transfer.Execution) (pc next : Program.Buffered.PC)
    (duration : Fin 256) (incoming : Inputs)
    (control : s.core.control = .active pc 0) (bound : pc.val < p.last.val)
    (successor : next.val = pc.val + 1)
    (fetch : p.fetch next = some (BufferedSPI.high duration))
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner)
    (full : ¬ e.rx.length < e.request.rxLimit) :
    Program.Buffered.advance p capacity s incoming =
      {s with
        core := ⟨.stopped .fault, p.idle, s.core.samples⟩
        buffers := {s.buffers with slot := .completed ⟨e, .fault⟩}
        samplerFirst := incoming
        samplerSecond := s.samplerFirst} := by
  have nextEq : (⟨pc.val + 1, by have := p.last.isLt; omega⟩ : Program.Buffered.PC) = next :=
    Fin.ext successor.symm
  simp [Program.Buffered.advance, Program.Buffered.owned, running, owner, control,
    busy, Fetch.advance, Fetch.next, Fetch.enter, Program.Buffered.lower, bound, nextEq, fetch,
    Program.Buffered.normalize, BufferedSPI.high, capture,
    Program.Buffered.entryTarget, Program.Buffered.sequentialTarget,
    Program.Buffered.entryEffects, Program.Buffered.appended, Transfer.step,
    Transfer.Command.identity, Transfer.Slot.identity, Transfer.admittedStep,
    full, Transfer.reject, Program.Buffered.settle, Program.Buffered.terminal, Fetch.stop]
  done

theorem advance_release (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (pc next : Program.Buffered.PC)
    (duration : Fin 256) (incoming : Inputs) (owner : Program.Buffered.owned s = true)
    (control : s.core.control = .active pc 0) (bound : pc.val < p.last.val)
    (successor : next.val = pc.val + 1)
    (fetch : p.fetch next = some (BufferedSPI.release duration)) :
    Program.Buffered.advance p capacity s incoming =
      {s with
        core := ⟨.active next duration, ⟨0, 7⟩, s.core.samples⟩
        samplerFirst := incoming
        samplerSecond := s.samplerFirst} := by
  have nextEq : (⟨pc.val + 1, by have := p.last.isLt; omega⟩ : Program.Buffered.PC) = next :=
    Fin.ext successor.symm
  simp [Program.Buffered.advance, owner, control, busy, Fetch.advance, Fetch.next,
    Fetch.enter, Program.Buffered.lower, bound, nextEq, fetch,
    Program.Buffered.normalize, BufferedSPI.release, capture,
    Program.Buffered.entryTarget, Program.Buffered.sequentialTarget,
    Program.Buffered.entryEffects, Program.Buffered.settle]
  done

theorem advance_halt (p : Program.Buffered.Program) (capacity : Transfer.Capacity)
    (s : Program.Buffered.State) (e : Transfer.Execution) (pc next : Program.Buffered.PC)
    (incoming : Inputs) (control : s.core.control = .active pc 0)
    (bound : pc.val < p.last.val) (successor : next.val = pc.val + 1)
    (fetch : p.fetch next = some BufferedSPI.halt)
    (running : s.buffers.slot = .running e) (owner : e.request.identity = s.owner) :
    Program.Buffered.advance p capacity s incoming =
      {s with
        core := ⟨.stopped .completed, p.idle, s.core.samples⟩
        buffers := {s.buffers with slot := .completed ⟨e, .complete⟩}
        samplerFirst := incoming
        samplerSecond := s.samplerFirst} := by
  have nextEq : (⟨pc.val + 1, by have := p.last.isLt; omega⟩ : Program.Buffered.PC) = next :=
    Fin.ext successor.symm
  simp [Program.Buffered.advance, Program.Buffered.owned, running, owner, control,
    busy, Fetch.advance, Fetch.next, Fetch.enter, Program.Buffered.lower, bound, nextEq, fetch,
    Program.Buffered.normalize, BufferedSPI.halt, Fetch.stop,
    Program.Buffered.entryTarget, Program.Buffered.sequentialTarget,
    Program.Buffered.entryEffects, Program.Buffered.settle, Program.Buffered.terminal,
    Transfer.step, Transfer.Command.identity, Transfer.Slot.identity, Transfer.admittedStep]
  done

end Pinwheel.Hardware.Buffered.SpiInterpreter
