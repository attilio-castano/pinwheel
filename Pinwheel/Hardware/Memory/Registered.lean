import Pinwheel.Hardware.Memory.Flops

/-! A memory whose read ports are registered: the model of a synchronous macro,
or of flip-flops behind an output register. It refines `Memory.spec _ _ _ 1`. The
read data at an edge is the word addressed on the previous edge, from the
contents as they were then. -/
namespace Pinwheel.Hardware.Memory.Registered

inductive Register (a w p : Nat) : Nat → Type where
  | word (k : BitVec a) : Register a w p w
  | out (port : Fin p) : Register a w p w

abbrev Input := Flops.Input
abbrev Output := Flops.Output

def words (a w p : Nat) : {v : Nat} → Register a w p v → Expr (Input a w p) (Register a w p) v
  | _, .word k => .reg (.word k)
  | _, .out port => .reg (.out port)

def circuit (a w p : Nat) : Circuit (Input a w p) (Register a w p) (Output w p) where
  next := fun r => match r with
    | .word k => .mux (.band (.input .enable) (.equal (.input .address) (.lit k)))
        (.input .data) (.reg (.word k))
    | .out port => Execution.readTree a (fun k => .reg (.word k)) (.input (.read port))
  output := fun o => match o with
    | .data port => .reg (.out port)

def stateValues (s : State a w p 1) : Values (Register a w p)
  | _, .word k => s.contents k
  | _, .out port => s.pending 0 port

theorem word_correct (i : Request a w p) (s : State a w p 1) (k : BitVec a) :
    (circuit a w p).step (Flops.requestValues i) (stateValues s) (.word k) = (s.step i).contents k := by
  simp only [circuit, Circuit.step, Expr.eval, Flops.requestValues, stateValues, State.step,
    Contents.write, BitVec.ofBool_and_ofBool]
  by_cases he : i.write.enable = true <;> by_cases ha : i.write.address = k <;>
    simp [he, ha]

theorem out_correct (i : Request a w p) (s : State a w p 1) (port : Fin p) :
    (circuit a w p).step (Flops.requestValues i) (stateValues s) (.out port) = (s.step i).pending 0 port := by
  simp [circuit, Circuit.step, Execution.readTree_correct, Expr.eval, Flops.requestValues,
    stateValues, State.step, Contents.reads]

theorem step_correct (i : Request a w p) (s : State a w p 1) :
    ((circuit a w p).step (Flops.requestValues i) (stateValues s) : Values (Register a w p)) =
      (fun {_} r => stateValues (s.step i) r) := by
  funext _ r
  cases r with
  | word k => exact word_correct i s k
  | out port => exact out_correct i s port

theorem observe_correct (i : Request a w p) (s : State a w p 1) (port : Fin p) :
    (circuit a w p).observe (Flops.requestValues i) (stateValues s) (.data port) = s.observe i port := by
  simp [circuit, Circuit.observe, Expr.eval, stateValues, State.observe]

def component (a w p : Nat) :
    Timed.Component (Request a w p) (Values (Register a w p)) (Fin p → BitVec w) :=
  ⟨fun i r => (circuit a w p).step (Flops.requestValues i) r,
    fun i r port => (circuit a w p).observe (Flops.requestValues i) r (.data port)⟩

/-- Registered read ports are a memory of latency one. -/
def refinement (a w p : Nat) : Timed.Refinement (component a w p) (spec a w p 1) where
  Rel := fun r s => @r = @stateValues a w p s
  step := fun i r s h => by
    subst r
    simpa only [component, spec] using step_correct i s
  observe := fun i r s h => by
    subst r
    funext port
    simp only [component, spec, observe_correct]

theorem trace_correct (a w p : Nat) (s : State a w p 1) (inputs : List (Request a w p)) :
    (component a w p).trace (@stateValues a w p s) inputs = (spec a w p 1).trace s inputs :=
  (refinement a w p).trace_eq (@stateValues a w p s) s rfl inputs

end Pinwheel.Hardware.Memory.Registered
