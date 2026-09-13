import Pinwheel.Hardware.RawProgram
import Pinwheel.Hardware.Countdown

namespace Pinwheel.Hardware.Core

inductive Input : Nat → Type where
  | initialize : Input 1
  | reset : Input 1
  | start : Input 1
  | commit : Input 1
  | sample : Input 1
  | idle : Input 3
  | word : Fin 32 → Input 16

inductive Register : Nat → Type where
  | word : Fin 32 → Register 16
  | idle : Register 3
  | valid : Register 1
  | status : Register 2
  | pc : Register 5
  | remaining : Register 8
  | timerActive : Register 1
  | levels : Register 3
  | sample : Fin 8 → Register 1

inductive Output : Nat → Type where
  | valid : Output 1
  | status : Output 2
  | pc : Output 5
  | remaining : Output 8
  | timerActive : Output 1
  | levels : Output 3
  | sample : Fin 8 → Output 1
  | busy : Output 1
  | completed : Output 1
  | fault : Output 1

structure Inputs where
  init : Bool := false
  reset : Bool := false
  start : Bool := false
  commit : Bool := false
  sample : Bool := false
  image : Raw.Program := ⟨Vector.replicate 32 0x8000, 0⟩
  deriving Repr

def Inputs.values (i : Inputs) : Values Input
  | _, .initialize => BitVec.ofBool i.init
  | _, .reset => BitVec.ofBool i.reset
  | _, .start => BitVec.ofBool i.start
  | _, .commit => BitVec.ofBool i.commit
  | _, .sample => BitVec.ofBool i.sample
  | _, .idle => i.image.idle
  | _, .word slot => i.image.memory[slot.val]

/-- Concrete state: every field below is a register or a bank of registers. -/
structure State where
  program : Raw.Program
  valid : Bool
  status : BitVec 2
  pc : BitVec 5
  timer : Countdown.State
  levels : Engine.Levels
  samples : Engine.Samples
  deriving DecidableEq, Repr

def State.values (s : State) : Values Register
  | _, .word slot => s.program.memory[slot.val]
  | _, .idle => s.program.idle
  | _, .valid => BitVec.ofBool s.valid
  | _, .status => s.status
  | _, .pc => s.pc
  | _, .remaining => s.timer.remaining
  | _, .timerActive => s.timer.active
  | _, .levels => s.levels
  | _, .sample slot => BitVec.ofBool s.samples[slot.val]

def fromValues (v : Values Register) : State where
  program := ⟨Vector.ofFn (fun slot => v (.word slot)), v .idle⟩
  valid := (v .valid)[0]
  status := v .status
  pc := v .pc
  timer := ⟨v .remaining, v .timerActive⟩
  levels := v .levels
  samples := Vector.ofFn (fun slot => (v (.sample slot))[0])

def embed (p : Raw.Program) (s : Engine.State) : State where
  program := p
  valid := true
  status := match s.control with
    | .active .. => 1 | .stopped .ready => 0 | .stopped .completed => 2 | .stopped .fault => 3
  pc := match s.control with | .active pc _ => BitVec.ofFin pc | .stopped _ => 0
  timer := match s.control with
    | .active _ remaining => ⟨BitVec.ofFin remaining, 1⟩ | .stopped _ => ⟨0, 0⟩
  levels := s.levels
  samples := s.samples

/-- Decode physical status; inactive PC/timer bits are not engine observations. -/
def view (s : State) : Engine.State where
  control := if s.status = 1 then .active s.pc.toFin s.timer.remaining.toFin
    else .stopped (if s.status = 2 then .completed else if s.status = 3 then .fault else .ready)
  levels := s.levels
  samples := s.samples

/-- A canonical representation sufficient for exact clock-step refinement. -/
def Represents (c : State) (p : Raw.Program) (s : Engine.State) : Prop := c = embed p s

theorem view_embed (p : Raw.Program) (s : Engine.State) : view (embed p s) = s := by
  cases s with
  | mk control levels samples =>
    cases control with
    | stopped reason => cases reason <;> rfl
    | active pc remaining => rfl

theorem from_values (s : State) : fromValues s.values = s := by
  cases s <;> simp [fromValues, State.values]
  done

end Pinwheel.Hardware.Core
