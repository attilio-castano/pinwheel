import Pinwheel.Hardware.Library

/-! Independent ready/valid increment lanes. The FIFO backend is a client
parameter. Each lane has its own synchronous reset and downstream readiness. -/
namespace LaneClient

open Pinwheel.Hardware Stream Stream.BackendAPI

abbrev lane (fifo : Fifo w d) (extra : Nat) := bufferedMap fifo (increment w) extra

abbrev Input (count width : Nat) := Bank count (In width)
abbrev Output (count width : Nat) := Bank count (Out width)
abbrev Register (count : Nat) (fifo : Fifo w d) (extra : Nat) :=
  Bank count (lane fifo extra).Register

def circuit (count : Nat) (fifo : Fifo w d) (extra : Nat) :
    Circuit (Input count w) (Register count fifo extra) (Output count w) :=
  Bank.circuit count (lane fifo extra).circuit

def model (count width depth extra : Nat) :=
  Bank.model count (pins (buffered (increment width).function depth extra))

def empty (count width extra : Nat) : Fin count → List (BitVec width) × PipelineState (BitVec width) extra :=
  fun _ => ([], pipelineEmpty extra)

private def project (k : Fin n) (s : Values (Bank n P)) : Values P :=
  fun p => s (.at k p)

private theorem step_lane (c : Circuit I R O) (i : Values (Bank n I)) (s : Values (Bank n R))
    (k : Fin n) : @Eq (Values R) (project k ((Bank.circuit n c).step i s))
      (c.step (project k i) (project k s)) := by
  funext width port
  simp only [project, Bank.circuit, Circuit.step, Expr.eval_bind, Expr.eval]
  rfl

def refinement (count : Nat) (fifo : Fifo w d) (extra : Nat) :
    Timed.Refinement (circuit count fifo extra).component (model count w d extra) where
  Rel := fun raw logical => ∀ k, (lane fifo extra).proof.Rel (project k raw) (logical k)
  step := by
    intro i s t rel k
    change (lane fifo extra).proof.Rel (project k ((circuit count fifo extra).step i s)) _
    rw [circuit, step_lane]
    exact (lane fifo extra).proof.step (project k i) (project k s) (t k) (rel k)
  observe := by
    intro i s t rel
    funext width port
    cases port with
    | «at» k p =>
      have observed := (lane fifo extra).proof.observe
        (fun q => i (.at k q)) (fun q => s (.at k q)) (t k) (rel k)
      simpa only [circuit, Circuit.component, Bank.circuit, Circuit.observe,
        Expr.eval_bind, Expr.eval, model, Bank.model, Bank.values, project] using
        congrFun (congrFun observed width) p

theorem initialized_trace (count : Nat) (fifo : Fifo w d) (extra : Nat)
    (s : Values (Register count fifo extra)) (i : Values (Input count w))
    (resetAll : ∀ k, i (.at k reset) = 1) (traffic : List (Values (Input count w))) :
    (circuit count fifo extra).component.trace ((circuit count fifo extra).step i s) traffic =
      (model count w d extra).trace (empty count w extra) traffic := by
  apply (refinement count fifo extra).trace_eq
  intro k
  rw [circuit, step_lane]
  exact (lane fifo extra).recover (project k i) (project k s) (resetAll k)

/-- The shift and circular fixtures instantiate this same client. -/
def selectFifo (width : Nat) (circular : Bool) : Fifo width 3 :=
  if circular then CircularFifo3.backend width else shift width 3 (by decide +kernel)

private def prefixed (stem : String) (d : Interface P) : Interface P :=
  d.rename (fun p => stem ++ d.label p)
    (fun a b h => d.unique a b (by simpa only [String.append_right_inj] using h))

def inputs (count width : Nat) : Interface (Input count width) :=
  prefixed "in_" (Bank.interface count (inputPorts width).interface)

def outputs (count width : Nat) : Interface (Output count width) :=
  prefixed "out_" (Bank.interface count (outputPorts width).interface)

def registers (count : Nat) (fifo : Fifo w d) (extra : Nat) :
    Interface (Register count fifo extra) :=
  Bank.interface count (lane fifo extra).registers

def design (count width extra : Nat) (circular : Bool) :
    TypedModule (Input count width) (Register count (selectFifo width circular) extra) (Output count width) :=
  let fifo := selectFifo width circular
  ⟨"independent_lanes", circuit count fifo extra, inputs count width, registers count fifo extra,
    outputs count width⟩

end LaneClient
