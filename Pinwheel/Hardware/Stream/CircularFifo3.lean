import Pinwheel.Hardware.Stream.Backend

/-! Three stationary payload slots with independent read/write pointers and
occupancy. Reset initializes control only. All proofs are polymorphic in width. -/
namespace Pinwheel.Hardware.Stream.CircularFifo3
open BackendAPI

abbrev ports (w : Nat) : Ports where
  size := 6
  widths k := if k.val < 3 then 2 else w
  names k := #["read_index","write_index","count","slot0","slot1","slot2"][k]
  distinct := by decide +kernel

abbrev Reg (w : Nat) := (ports w).Signal
private abbrev readPtr : Reg w 2 := .at ⟨0,by simp⟩
private abbrev writePtr : Reg w 2 := .at ⟨1,by simp⟩
private abbrev count : Reg w 2 := .at ⟨2,by simp⟩
private abbrev slot0 : Reg w w := .at ⟨3,by simp⟩
private abbrev slot1 : Reg w w := .at ⟨4,by simp⟩
private abbrev slot2 : Reg w w := .at ⟨5,by simp⟩
private abbrev E (w v : Nat) := Expr (In w) (Reg w) v

private def bump (ptr : E w 2) : E w 2 :=
  .mux (.equal ptr (.lit 2)) (.lit 0) (ptr.plus (.lit 1))

private def hasData : E w 1 := .inv (.zero (.reg count))
private def canAccept : E w 1 := (Expr.inv (.equal (.reg count) (.lit 3))).bor (.input ready)
private def push : E w 1 := .band (.input valid) canAccept
private def pop : E w 1 := .band (.input ready) hasData
private def store (index : BitVec 2) (slot : Reg w w) : E w w :=
  .mux (.band (.inv (.input reset)) (.band push (.equal (.reg writePtr) (.lit index))))
    (.input payload) (.reg slot)

def circuit (w : Nat) : Circuit (In w) (Reg w) (Out w) where
  next p := match p with
    | .at ⟨0,_⟩ => .mux (.input reset) (.lit 0) (.mux pop (bump (.reg readPtr)) (.reg readPtr))
    | .at ⟨1,_⟩ => .mux (.input reset) (.lit 0) (.mux push (bump (.reg writePtr)) (.reg writePtr))
    | .at ⟨2,_⟩ => .mux (.input reset) (.lit 0) ((Expr.reg count).plus ((Expr.concat (.lit (0#1)) push).sub (.concat (.lit (0#1)) pop)))
    | .at ⟨3,_⟩ => store 0 slot0
    | .at ⟨4,_⟩ => store 1 slot1
    | .at ⟨5,_⟩ => store 2 slot2
    | .at ⟨k+6,h⟩ => False.elim (by change k+6 < 6 at h; omega)
  output := streamOutputs (.band (.inv (.input reset)) canAccept) (.band (.inv (.input reset)) hasData)
    (.mux (.band (.inv (.input reset)) hasData)
      (.mux (.zero (.reg readPtr)) (.reg slot0)
        (.mux (.equal (.reg readPtr) (.lit 1)) (.reg slot1) (.reg slot2))) (.lit 0))

private inductive Pos | a | b | c deriving DecidableEq
private def Pos.next : Pos → Pos | .a => .b | .b => .c | .c => .a
private def Pos.code : Pos → BitVec 2 | .a => 0 | .b => 1 | .c => 2
private inductive Size | empty | one | two | full deriving DecidableEq
private def Size.code : Size → BitVec 2 | .empty => 0 | .one => 1 | .two => 2 | .full => 3
private def tail (p : Pos) : Size → Pos
  | .empty | .full => p | .one => p.next | .two => p.next.next
private def words (p : Pos) (data : Pos → α) : Size → List α
  | .empty => [] | .one => [data p] | .two => [data p,data p.next]
  | .full => [data p,data p.next,data p.next.next]

private def pack (p : Pos) (n : Size) (data : Pos → BitVec w) : Values (Reg w)
  | _, .at ⟨0,_⟩ => p.code
  | _, .at ⟨1,_⟩ => (tail p n).code
  | _, .at ⟨2,_⟩ => n.code
  | _, .at ⟨3,_⟩ => data .a
  | _, .at ⟨4,_⟩ => data .b
  | _, .at ⟨5,_⟩ => data .c
  | _, .at ⟨k+6,h⟩ => False.elim (by change k+6 < 6 at h; omega)

private def Rel (r : Values (Reg w)) (q : List (BitVec w)) : Prop :=
  ∃ p n data, @r = @pack w p n data ∧ q = words p data n

-- Preserve arbitrary idle input data when enumerating the three control bits.
private def input (rst v rd : Bool) (x : BitVec w) : Values (In w)
  | _, .at ⟨0,_⟩ => BitVec.ofBool rst
  | _, .at ⟨1,_⟩ => BitVec.ofBool v
  | _, .at ⟨2,_⟩ => BitVec.ofBool rd
  | _, .at ⟨3,_⟩ => x
  | _, .at ⟨k+4,h⟩ => False.elim (by change k+4 < 4 at h; omega)

private theorem expand (i : Values (In w)) : @i =
    @input w (i reset == 1) (i valid == 1) (i ready == 1) (i payload) :=
  input_ext (bit_roundtrip _).symm (bit_roundtrip _).symm (bit_roundtrip _).symm rfl

private theorem allInputs (P : Values (In w) → Prop)
    (cases : ∀ rst v rd x, P (input rst v rd x)) (i : Values (In w)) : P i :=
  Eq.mpr (congrArg P (expand i)) (cases _ _ _ _)

private def nextSize (n : Size) (take put : Bool) : Size :=
  match take,put,n with
  | false,true,.empty => .one | false,true,.one => .two | false,true,.two => .full
  | true,false,.full => .two | true,false,.two => .one | true,false,.one => .empty
  | _,_,n => n

set_option maxHeartbeats 8000000 in
private theorem step_case (rst v rd : Bool) (x : BitVec w) (p : Pos) (n : Size) (data : Pos → BitVec w) :
    Rel ((circuit w).step (input rst v rd x) (pack p n data))
      ((pins (queue 3)).step (input rst v rd x) (words p data n)) := by
  let take := rd && n != .empty
  let put := v && (n != .full || rd)
  refine ⟨if rst then .a else if take then p.next else p,
    if rst then .empty else nextSize n take put,
    fun k => if !rst && put && k == tail p n then x else data k, ?_, ?_⟩
  · funext b r
    match r with
    | .at ⟨0,_⟩ | .at ⟨1,_⟩ | .at ⟨2,_⟩ | .at ⟨3,_⟩ | .at ⟨4,_⟩ | .at ⟨5,_⟩ =>
      cases rst <;> cases v <;> cases rd <;> cases p <;> cases n <;>
        simp +ground [take, put, nextSize, tail, Pos.next, Pos.code, Size.code, circuit, Circuit.step,
          store, push, pop, hasData, canAccept, bump, Expr.eval, pack, input, reset, valid, ready, payload]
    | .at ⟨k+6,h⟩ => exact False.elim (by change k+6 < 6 at h; omega)
  · cases rst <;> cases v <;> cases rd <;> cases p <;> cases n <;> rfl

private theorem output_case (rst v rd : Bool) (x : BitVec w) (p : Pos) (n : Size) (data : Pos → BitVec w) :
    @Eq (Values (Out w)) ((circuit w).observe (input rst v rd x) (pack p n data))
      ((pins (queue 3)).observe (input rst v rd x) (words p data n)) := by
  funext b o
  match o with
  | .at ⟨0,_⟩ | .at ⟨1,_⟩ | .at ⟨2,_⟩ =>
    cases rst <;> cases rd <;> cases p <;> cases n <;>
      simp +ground [Circuit.observe,circuit,streamOutputs,hasData,canAccept,Expr.eval,pack,input,
        pins,Machine.component,queue,words,decodeInput,outputValues,Pos.code,Size.code,Pos.next,
        reset,ready,valid,payload]
  | .at ⟨k+3,h⟩ => exact False.elim (by change k+3 < 3 at h; omega)

private theorem cold_reset (i : Values (In w)) (r : Values (Reg w)) (hr : i reset = 1) :
    Rel ((circuit w).step i r) [] := by
  let data : Pos → BitVec w
    | .a => r slot0 | .b => r slot1 | .c => r slot2
  refine ⟨.a,.empty,data,?_,rfl⟩
  funext b reg
  match reg with
  | .at ⟨0,_⟩ | .at ⟨1,_⟩ | .at ⟨2,_⟩ | .at ⟨3,_⟩ | .at ⟨4,_⟩ | .at ⟨5,_⟩ =>
    simp +ground [Circuit.step,circuit,Expr.eval,store,hr,pack,data,Pos.code,Size.code,tail]
  | .at ⟨k+6,h⟩ => exact False.elim (by change k+6 < 6 at h; omega)

def backend (w : Nat) : Fifo w 3 where
  Register := Reg w
  registers := (ports w).interface
  circuit := circuit w
  proof := {
    Rel := Rel
    step := by
      intro i r q h
      obtain ⟨p,n,data,rfl,rfl⟩ := h
      exact allInputs (fun j => Rel ((circuit w).step j (pack p n data))
        ((pins (queue 3)).step j (words p data n))) (fun rst v rd x => step_case rst v rd x p n data) i
    observe := by
      intro i r q h
      obtain ⟨p,n,data,rfl,rfl⟩ := h
      exact allInputs (fun j => @Eq (Values (Out w)) ((circuit w).observe j (pack p n data))
        ((pins (queue 3)).observe j (words p data n))) (fun rst v rd x => output_case rst v rd x p n data) i }
  recover := cold_reset

end Pinwheel.Hardware.Stream.CircularFifo3
