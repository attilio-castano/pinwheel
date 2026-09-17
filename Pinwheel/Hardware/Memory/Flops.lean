import Pinwheel.Hardware.Memory
import Pinwheel.Hardware.Enable
import Pinwheel.Hardware.Execution.Memory

/-! The flip-flop implementation of the memory contract, for any address width,
word width and number of read ports: one register per word, loaded under a
decoded write enable, and one balanced multiplexer tree per read port. It refines
`Memory.spec _ _ _ 0`. Every word is a certified `Update`, which is what a
clock-gating plan needs. A latch array with registered write data has the same
edge-level behaviour; its obligations are electrical, not functional. -/
namespace Pinwheel.Hardware.Memory.Flops

inductive Register (a w : Nat) : Nat → Type where
  | word (k : BitVec a) : Register a w w

inductive Input (a w p : Nat) : Nat → Type where
  | enable : Input a w p 1
  | address : Input a w p a
  | data : Input a w p w
  | read (port : Fin p) : Input a w p a

inductive Output (w p : Nat) : Nat → Type where
  | data (port : Fin p) : Output w p w

def requestValues (i : Request a w p) : Values (Input a w p)
  | _, .enable => BitVec.ofBool i.write.enable
  | _, .address => i.write.address
  | _, .data => i.write.data
  | _, .read port => i.read port

def contentsValues (c : Contents a w) : Values (Register a w)
  | _, .word k => c k

/-- The write port, decoded at one word. -/
def update (a w p : Nat) (k : BitVec a) : Update (Input a w p) (Register a w) w :=
  ⟨.band (.input .enable) (.equal (.input .address) (.lit k)), .input .data⟩

def readExpr (address : Expr I (Register a w) a) : Expr I (Register a w) w :=
  Execution.readTree a (fun k => .reg (.word k)) address

def circuit (a w p : Nat) : Circuit (Input a w p) (Register a w) (Output w p) where
  next := fun r => match r with
    | .word k => (update a w p k).next (.word k)
  output := fun o => match o with
    | .data port => readExpr (.input (.read port))

theorem next_correct (i : Request a w p) (c : Contents a w) (k : BitVec a) :
    (circuit a w p).step (requestValues i) (contentsValues c) (.word k) = c.write i.write k := by
  simp only [circuit, Circuit.step, Update.next, update, Expr.eval, requestValues, contentsValues,
    Contents.write, BitVec.ofBool_and_ofBool]
  by_cases he : i.write.enable = true <;> by_cases ha : i.write.address = k <;>
    simp [he, ha]

theorem step_correct (i : Request a w p) (c : Contents a w) :
    ((circuit a w p).step (requestValues i) (contentsValues c) : Values (Register a w)) =
      (fun {_} r => contentsValues (c.write i.write) r) := by
  funext _ r
  cases r
  exact next_correct i c _

theorem observe_correct (i : Request a w p) (c : Contents a w) (port : Fin p) :
    (circuit a w p).observe (requestValues i) (contentsValues c) (.data port) = c (i.read port) := by
  simp [circuit, Circuit.observe, readExpr, Execution.readTree_correct, Expr.eval,
    requestValues, contentsValues]

def component (a w p : Nat) :
    Timed.Component (Request a w p) (Values (Register a w)) (Fin p → BitVec w) :=
  ⟨fun i r => (circuit a w p).step (requestValues i) r,
    fun i r port => (circuit a w p).observe (requestValues i) r (.data port)⟩

/-- Flip-flops are a memory of latency zero. -/
def refinement (a w p : Nat) : Timed.Refinement (component a w p) (spec a w p 0) where
  Rel := fun r s => @r = @contentsValues a w s.contents
  step := fun i r s h => by
    subst r
    simpa only [component, spec, State.step] using step_correct i s.contents
  observe := fun i r s h => by
    subst r
    funext port
    simp only [component, spec, observe_correct, observe_zero, Contents.reads]

theorem trace_correct (a w p : Nat) (c : Contents a w) (inputs : List (Request a w p)) :
    (component a w p).trace (@contentsValues a w c) inputs =
      (spec a w p 0).trace ⟨c, fun k => k.elim0⟩ inputs :=
  (refinement a w p).trace_eq (@contentsValues a w c) ⟨c, fun k => k.elim0⟩ rfl inputs

/-- Every word is a certified enable: `load data when enable ∧ address = k`. -/
def enables (a w p : Nat) : (circuit a w p).Enables where
  update := fun r => match r with
    | .word k => some (update a w p k)
  sound := by
    intro _ r u h
    cases r
    simp only [Option.some.injEq] at h
    subst h
    exact Update.describes_next _ _

end Pinwheel.Hardware.Memory.Flops
