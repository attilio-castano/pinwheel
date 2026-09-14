import Pinwheel.Hardware.Storage.Cache

namespace Pinwheel.Hardware.Storage.Cache
open Loader

theorem valid_next (i : Machine.Inputs) (s : State) (h : Valid s) : Valid (next i s) := by
  intro hb
  have hp := step_pc (feed i s) s.machine.core hb
  rw [machine_next i s h] at hb ⊢
  have hs := running_selection i s.machine hb
  have hpc : (Reactive.stepValue (feed i s) s.machine.core).pc = (Machine.next i s.machine).core.pc :=
    congrArg (fun m => m.core.pc) (machine_next i s h)
  simp only [hs.1, Loader.Store.read, Machine.active_memory_preserved, ← hpc, next]
  split <;> rcases hp with hp | ⟨hr, hp⟩
  all_goals simp_all [Valid, Loader.Store.read]
  simp only [← hpc, feed, hs.2, Loader.Store.read]
  rfl
  done

def run (s : State) : List Machine.Inputs → State
  | [] => s | i :: rest => run (next i s) rest

theorem run_correct (s : State) (h : Valid s) (requests : List Machine.Inputs) :
    (run s requests).machine = Machine.run s.machine requests := by
  induction requests generalizing s with
  | nil => rfl
  | cons i rest ih => simpa only [run, Machine.run, machine_next i s h] using ih (next i s) (valid_next i s h)
  done

theorem idle_valid (s : State) (h : Reactive.runningValue s.machine.core = false) : Valid s := by
  simp [Valid, h]
  done

end Pinwheel.Hardware.Storage.Cache
