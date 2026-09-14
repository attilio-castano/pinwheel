import Pinwheel.Engine.Fetch

namespace Pinwheel.Engine.Reactive.Fetch

structure Agrees (store : Store lastAddress lastSample) (p : Program lastAddress lastSample) : Prop where
  fetch : ∀ pc, store.fetch pc = some (p.fetch pc)
  idle : store.idle = p.idle
  last : store.last = p.last

theorem enter_eq (store : Store lastAddress lastSample) (p : Program lastAddress lastSample) (h : Agrees store p)
    (pc : Fin (lastAddress + 1)) (slots : Vector Bool (lastSample + 1)) (inputs : Inputs) :
    enter store pc slots inputs = Reactive.enter p pc slots inputs := by
  cases hi : p.fetch pc <;> simp [enter, h.fetch, Reactive.enter, hi, stop, Reactive.stop, h.idle]
  done

theorem next_eq (store : Store lastAddress lastSample) (p : Program lastAddress lastSample) (h : Agrees store p)
    (pc : Fin (lastAddress + 1)) (slots : Vector Bool (lastSample + 1)) (inputs : Inputs) :
    next store pc slots inputs = Reactive.next p pc slots inputs := by
  simp [next, Reactive.next, h.last, enter_eq store p h, stop, Reactive.stop, h.idle]
  done

theorem jump_eq (store : Store lastAddress lastSample) (p : Program lastAddress lastSample) (h : Agrees store p)
    (pc : Fin (lastAddress + 1)) (slots : Vector Bool (lastSample + 1)) (inputs : Inputs) :
    jump store pc slots inputs = Reactive.jump p pc slots inputs := by
  simp [jump, Reactive.jump, h.last, enter_eq store p h, stop, Reactive.stop, h.idle]
  done

theorem dispatch_eq (store : Store lastAddress lastSample) (p : Program lastAddress lastSample) (h : Agrees store p)
    (pc : Fin (lastAddress + 1)) (finish : Finish lastAddress lastSample) (slots : Vector Bool (lastSample + 1)) (inputs : Inputs) :
    dispatch store pc finish slots inputs = Reactive.dispatch p pc finish slots inputs := by
  cases finish <;> simp [dispatch, Reactive.dispatch, next_eq store p h, jump_eq store p h]
  done

/-- For agreeing stores the complete machine state agrees, including malformed control states. -/
theorem advance_eq (store : Store lastAddress lastSample) (p : Program lastAddress lastSample) (h : Agrees store p)
    (s : State lastAddress lastSample) (inputs : Inputs) : advance store s inputs = Reactive.advance p s inputs := by
  cases hc : s.control <;> simp only [advance, Reactive.advance, hc, h.fetch,
    next_eq store p h, dispatch_eq store p h, stop, Reactive.stop, h.idle]
  all_goals split <;> simp_all
  done

theorem step_eq (store : Store lastAddress lastSample) (p : Program lastAddress lastSample) (h : Agrees store p)
    (s : State lastAddress lastSample) (resetRequested startRequested : Bool) (inputs : Inputs) :
    step store s resetRequested startRequested inputs =
      Reactive.step p s resetRequested startRequested inputs := by
  simp [step, Reactive.step, advance_eq store p h, start, Reactive.start, enter_eq store p h,
    reset, Reactive.reset, stop, Reactive.stop, h.idle]
  done

theorem run_eq (store : Store lastAddress lastSample) (p : Program lastAddress lastSample) (h : Agrees store p)
    (s : State lastAddress lastSample) (incoming : Nat → Inputs) (n : Nat) :
    run store s incoming n = Reactive.run p s incoming n := by
  induction n <;> simp_all only [run, Reactive.run, advance_eq store p h]
  done

end Pinwheel.Engine.Reactive.Fetch
