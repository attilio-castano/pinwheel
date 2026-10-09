import Pinwheel.Program.BufferedProofs

/-! Execution congruence for independently decoded buffered images. Equality
of virtual fetch, idle pins and the last virtual address suffices for every
source execution prefix. This includes sampler latency, data consumption,
scratch decisions, waits, faults and retained completions. It is a theorem
about Buffered operational semantics; hardware-register refinement is a
separate obligation. -/
namespace Pinwheel.Hardware.Buffered.DecodedExecution
open Pinwheel.Program

structure Equivalent (p q : Program.Buffered.Program) : Prop where
  fetch : p.fetch = q.fetch
  idle : p.idle = q.idle
  last : p.last = q.last

theorem lower_eq (p q : Program.Buffered.Program) (h : Equivalent p q)
    (s : Program.Buffered.State) : Program.Buffered.lower p s = Program.Buffered.lower q s := by
  simp only [Program.Buffered.lower, h.fetch, h.idle, h.last]

theorem terminal_eq (p q : Program.Buffered.Program) (h : Equivalent p q)
    (capacity : Transfer.Capacity) (s : Program.Buffered.State) (outcome : Transfer.Outcome) :
    Program.Buffered.terminal p capacity s outcome = Program.Buffered.terminal q capacity s outcome := by
  simp only [Program.Buffered.terminal, lower_eq p q h]

theorem settle_eq (p q : Program.Buffered.Program) (h : Equivalent p q)
    (capacity : Transfer.Capacity) (s : Program.Buffered.State) :
    Program.Buffered.settle p capacity s = Program.Buffered.settle q capacity s := by
  simp only [Program.Buffered.settle, terminal_eq p q h]

theorem entryEffects_eq (p q : Program.Buffered.Program) (h : Equivalent p q)
    (capacity : Transfer.Capacity) (s : Program.Buffered.State) (pc : Program.Buffered.PC)
    (sampled : Engine.Reactive.Inputs) :
    Program.Buffered.entryEffects p capacity s pc sampled =
      Program.Buffered.entryEffects q capacity s pc sampled := by
  simp only [Program.Buffered.entryEffects, h.fetch, terminal_eq p q h]

theorem sequentialTarget_eq (p q : Program.Buffered.Program) (h : Equivalent p q)
    (pc : Program.Buffered.PC) :
    Program.Buffered.sequentialTarget p pc = Program.Buffered.sequentialTarget q pc := by
  simp only [Program.Buffered.sequentialTarget, h.last]

theorem finishTarget_eq (p q : Program.Buffered.Program) (h : Equivalent p q)
    (pc : Program.Buffered.PC) (finish : Program.Buffered.Finish) (samples : Vector Bool 16) :
    Program.Buffered.finishTarget p pc finish samples = Program.Buffered.finishTarget q pc finish samples := by
  simp only [Program.Buffered.finishTarget, sequentialTarget_eq p q h, h.last]

theorem entryTarget_eq (p q : Program.Buffered.Program) (h : Equivalent p q)
    (s : Program.Buffered.State) (sampled : Engine.Reactive.Inputs) :
    Program.Buffered.entryTarget p s sampled = Program.Buffered.entryTarget q s sampled := by
  simp only [Program.Buffered.entryTarget, h.fetch, sequentialTarget_eq p q h, finishTarget_eq p q h]

theorem start_eq (p q : Program.Buffered.Program) (h : Equivalent p q)
    (capacity : Transfer.Capacity) (s : Program.Buffered.State) :
    Program.Buffered.start p capacity s = Program.Buffered.start q capacity s := by
  simp only [Program.Buffered.start, lower_eq p q h, entryEffects_eq p q h, settle_eq p q h]

theorem advance_eq (p q : Program.Buffered.Program) (h : Equivalent p q)
    (capacity : Transfer.Capacity) (s : Program.Buffered.State) (incoming : Engine.Reactive.Inputs) :
    Program.Buffered.advance p capacity s incoming = Program.Buffered.advance q capacity s incoming := by
  simp only [Program.Buffered.advance, lower_eq p q h, entryEffects_eq p q h,
    entryTarget_eq p q h, settle_eq p q h]

theorem run_eq (p q : Program.Buffered.Program) (h : Equivalent p q)
    (capacity : Transfer.Capacity) (s : Program.Buffered.State)
    (incoming : Nat → Engine.Reactive.Inputs) (edges : Nat) :
    Program.Buffered.run p capacity s incoming edges = Program.Buffered.run q capacity s incoming edges := by
  induction edges with
  | zero => rfl
  | succ edges ih => simp only [Program.Buffered.run, ih, advance_eq p q h]

end Pinwheel.Hardware.Buffered.DecodedExecution
