import Pinwheel.Hardware.Execution.StoreProofs

namespace Pinwheel.Hardware.Reactive

abbrev Model := Engine.Reactive.State 255 15
abbrev Program := Execution.Image
abbrev Samples := Vector Bool 16

inductive Input : Nat → Type where
  | reset : Input 1 | start : Input 1 | incoming : Input 2
  | idleLevels : Input 3 | idleEnabled : Input 3 | last : Input 8
  | current : Input 64 | successor : Input 64

inductive Register : Nat → Type where
  | mode : Register 3 | pc : Register 8 | remaining : Register 8 | waitLeft : Register 8
  | levels : Register 3 | enabled : Register 3 | sample : Fin 16 → Register 1

inductive Output : Nat → Type where
  | state : Register w → Output w
  | readA : Output 8 | readB : Output 8 | busy : Output 1

structure Inputs where
  reset : Bool := false
  start : Bool := false
  incoming : BitVec 2 := 0
  idle : Engine.Reactive.Pins := {}
  last : BitVec 8 := 255
  current : BitVec 64 := 4
  successor : BitVec 64 := 4
  deriving Repr

def Inputs.values (i : Inputs) : Values Input
  | _, .reset => BitVec.ofBool i.reset | _, .start => BitVec.ofBool i.start
  | _, .incoming => i.incoming | _, .idleLevels => i.idle.levels | _, .idleEnabled => i.idle.enabled
  | _, .last => i.last | _, .current => i.current | _, .successor => i.successor

/-- Modes: ready 0, action 1, wait 2, checked 3, qualify 4, complete 5, timeout 6, fault 7. -/
structure State where
  mode : BitVec 3
  pc : BitVec 8
  remaining : BitVec 8
  waitLeft : BitVec 8
  pins : Engine.Reactive.Pins
  samples : Samples
  deriving DecidableEq, Repr

def State.values (s : State) : Values Register
  | _, .mode => s.mode | _, .pc => s.pc | _, .remaining => s.remaining | _, .waitLeft => s.waitLeft
  | _, .levels => s.pins.levels | _, .enabled => s.pins.enabled
  | _, .sample k => BitVec.ofBool s.samples[k.val]

def fromValues (v : Values Register) : State :=
  ⟨v .mode, v .pc, v .remaining, v .waitLeft, ⟨v .levels, v .enabled⟩,
    Vector.ofFn (fun k => (v (.sample k))[0])⟩

def stopMode : Engine.Reactive.Stop → BitVec 3
  | .ready => 0 | .completed => 5 | .timeout => 6 | .fault => 7

def embed (s : Model) : State :=
  let base : State := ⟨0, 0, 0, 0, s.pins, s.samples⟩
  match s.control with
  | .stopped reason => {base with mode := stopMode reason}
  | .active pc left => {base with mode := 1, pc := BitVec.ofFin pc, remaining := BitVec.ofFin left}
  | .waiting pc left => {base with mode := 2, pc := BitVec.ofFin pc, remaining := BitVec.ofFin left}
  | .checked pc left => {base with mode := 3, pc := BitVec.ofFin pc, remaining := BitVec.ofFin left}
  | .qualifying pc left budget =>
    {base with mode := 4, pc := BitVec.ofFin pc, remaining := BitVec.ofFin left, waitLeft := BitVec.ofFin budget}

def view (s : State) : Model :=
  ⟨if s.mode = 1 then .active s.pc.toFin s.remaining.toFin
    else if s.mode = 2 then .waiting s.pc.toFin s.remaining.toFin
    else if s.mode = 3 then .checked s.pc.toFin s.remaining.toFin
    else if s.mode = 4 then .qualifying s.pc.toFin s.remaining.toFin s.waitLeft.toFin
    else .stopped (if s.mode = 5 then .completed else if s.mode = 6 then .timeout else if s.mode = 7 then .fault else .ready),
   s.pins, s.samples⟩

theorem view_embed (s : Model) : view (embed s) = s := by
  rcases s with ⟨control, pins, samples⟩
  cases control with
  | stopped reason => cases reason <;> rfl
  | _ => rfl
  done

theorem from_values (s : State) : fromValues s.values = s := by
  cases s <;> simp [fromValues, State.values]
  done

end Pinwheel.Hardware.Reactive
