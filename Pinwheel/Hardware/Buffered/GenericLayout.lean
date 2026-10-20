import Pinwheel.Hardware.Buffered.GenericEncoding

/-! Static layout coordinates and branch descriptors. The successor arithmetic
here inspects only packed loop metadata and coordinates; it does not execute
the controller or assume a trace relation. -/
namespace Pinwheel.Hardware.Buffered.GenericLayout
open Pinwheel.Hardware Pinwheel.Program
open Pinwheel.Engine.Reactive.Counted

def leaves (code : Schedule α) : List α :=
  match code with
  | .emit i => [i]
  | .seq a b => leaves a ++ leaves b
  | .repeat _ body => leaves body

def address (code : Schedule α) (pc : Nat) : Nat :=
  match code with
  | .emit _ => 0
  | .seq a b => if pc < a.span then address a pc else a.words + address b (pc - a.span)
  | .repeat _ body => address body (pc % body.span)

def depth (code : Schedule α) (pc : Nat) : Nat :=
  match code with
  | .emit _ => 0
  | .seq a b => if pc < a.span then depth a pc else depth b (pc - a.span)
  | .repeat _ body => 1 + depth body (pc % body.span)

theorem span_positive (code : Schedule α) : 0 < code.span := by
  induction code
  all_goals simp_all [Schedule.span]
  omega
  done

structure Coordinates where
  row : BitVec 7
  outer : BitVec 3
  inner : BitVec 3
  deriving DecidableEq, Repr

/-- A structural source map, including the hardware's out-of-bank sentinel.
Source environments put the innermost index first; hardware names the two
indices by their outer/inner roles. -/
def sourceCoordinates (p : Program.Buffered.Program) (pc : Program.Buffered.PC) : Coordinates :=
  if pc.val < p.code.span then
    let d := depth p.code pc.val
    let env := ((p.code.locate (Vector.replicate 2 0) pc.val).map Prod.snd).getD
      (Vector.replicate 2 0)
    ⟨BitVec.ofNat 7 (address p.code pc.val),
     if d = 0 then 0 else BitVec.ofNat 3 (if d = 1 then env[0] else env[1]).val,
     if d = 2 then BitVec.ofNat 3 (env[0]).val else 0⟩
  else ⟨64, 0, 0⟩

def coordinates (r : Values Reactive.Register) : Coordinates :=
  ⟨r .pc, r .outer, r .inner⟩

def sequential (control : BitVec 22) (q : Coordinates) : Coordinates :=
  let depth := control.extractLsb' 0 2
  let innerAgain := depth == 2 && control[21] &&
    decide (q.inner.toNat < (control.extractLsb' 17 3).toNat)
  let outerAgain := !innerAgain && control[20] &&
    decide (q.outer.toNat < (control.extractLsb' 8 3).toNat)
  ⟨if innerAgain then (0 : BitVec 1) ++ control.extractLsb' 11 6
     else if outerAgain then (0 : BitVec 1) ++ control.extractLsb' 2 6 else q.row + 1,
   if outerAgain then q.outer + 1 else if control[20] && !innerAgain then 0 else q.outer,
   if innerAgain then q.inner + 1 else if control[21] then 0 else q.inner⟩

/-- Absolute endpoints retain both virtual and physical coordinates. The low
bit distinguishes absolute targets from the literal-one NEXT descriptor. -/
def endpoint (pc : Program.Buffered.PC) (q : Coordinates) : BitVec 24 :=
  q.inner ++ q.outer ++ q.row ++ BitVec.ofNat 10 pc.val ++ (0 : BitVec 1)

def target (map : Program.Buffered.PC → Coordinates) : Program.Buffered.Target → BitVec 24
  | .next => 1
  | .absolute pc => endpoint pc (map pc)

def finish (map : Program.Buffered.PC → Coordinates) : Program.Buffered.Finish → BitVec 56
  | .sequential => 0
  | .jump pc => (0 : BitVec 2) ++ (0 : BitVec 24) ++ endpoint pc (map pc) ++
      (0 : BitVec 4) ++ (1 : BitVec 2)
  | .branch sample yes no => (0 : BitVec 2) ++ target map no ++ target map yes ++
      BitVec.ofNat 4 sample.val ++ (2 : BitVec 2)

def instructionFinish (map : Program.Buffered.PC → Coordinates)
    (i : Program.Buffered.Instruction) : BitVec 56 :=
  match i.operation with | .checked _ _ _ f => finish map f | _ => 0

def record (map : Program.Buffered.PC → Coordinates) (control : BitVec 24)
    (i : Program.Buffered.Instruction) : BitVec 144 :=
  instructionFinish map i ++ control ++ GenericEncoding.encode i

theorem endpoint_fields (pc : Program.Buffered.PC) (q : Coordinates) :
    (endpoint pc q).extractLsb' 1 10 = BitVec.ofNat 10 pc.val ∧
    (endpoint pc q).extractLsb' 11 7 = q.row ∧
    (endpoint pc q).extractLsb' 18 3 = q.outer ∧
    (endpoint pc q).extractLsb' 21 3 = q.inner ∧
    (endpoint pc q).extractLsb' 0 1 = 0 := by
  simp only [endpoint]
  bv_decide
  done

end Pinwheel.Hardware.Buffered.GenericLayout
