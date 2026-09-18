import Pinwheel.Hardware.Structure
import Pinwheel.Hardware.PinBoundary
import Pinwheel.Hardware.Loader.Machine
import Pinwheel.Hardware.TimedPairs

/-! The proposed two-register input pipeline, inserted in front of any netlist
with the loader machine's ports. Digital samples only: no metastability,
threshold or asynchronous-arrival claim follows from these theorems. -/
namespace Pinwheel.Hardware.PinSampler
open Loader

inductive Stage : Nat → Type where
  | first : Stage 2
  | second : Stage 2

def stageValues (p : PinBoundary.Samples 2) : Values Stage
  | _, .first => p.first
  | _, .second => p.second

/-- The engine-side `incoming` is the second stage. Host ports pass through. -/
def input : {w : Nat} → Machine.Input w → Expr Machine.Input (Extended R Stage) w
  | _, .init => .input .init
  | _, .reset => .input .reset
  | _, .command => .input .command
  | _, .data => .input .data
  | _, .incoming => .reg (.extra .second)

/-- The pipeline never resets. Nothing sits between the two stages, and only
the second stage reaches engine logic. -/
def stage : {w : Nat} → Stage w → Expr Machine.Input (Extended R Stage) w
  | _, .first => .input .incoming
  | _, .second => .reg (.extra .first)

def netlist (n : Netlist R Machine.Output Machine.Input) :
    Netlist (Extended R Stage) Machine.Output Machine.Input :=
  n.extend input stage

/-- What the wrapped netlist consumes on an edge where the pins show `i.incoming`. -/
def engineInputs (i : Machine.Inputs) (p : PinBoundary.Samples 2) : Machine.Inputs :=
  { i with incoming := PinBoundary.engineInput p }

/-- The reset argument of the boundary contract is tied low. -/
def advance (i : Machine.Inputs) (p : PinBoundary.Samples 2) : PinBoundary.Samples 2 :=
  PinBoundary.sampleStep 0 false i.incoming p

def component (n : Netlist R Machine.Output Machine.Input) :
    Timed.Component Machine.Inputs (Values R) (Values Machine.Output) :=
  ⟨fun i r => n.step i.values r, fun i r => n.observe i.values r⟩

/-- The engine-side history produced by a pin-side history. After an edge the
second stage already holds its next value, so an output that depends
combinationally on `incoming` observes that value; host ports are held. -/
def delayed : PinBoundary.Samples 2 → List Machine.Inputs → List (Machine.Inputs × Machine.Inputs)
  | _, [] => []
  | p, i :: rest => (engineInputs i p, engineInputs i (advance i p)) :: delayed (advance i p) rest

theorem input_values (i : Machine.Inputs) (s : Values R) (p : PinBoundary.Samples 2) :
    (fun {w} (q : Machine.Input w) =>
      (input q).eval i.values (Extended.values s (stageValues p))) =
      ((engineInputs i p).values : Values Machine.Input) := by
  funext w q
  cases q <;> rfl

theorem step_eq (n : Netlist R Machine.Output Machine.Input) (i : Machine.Inputs)
    (s : Values R) (p : PinBoundary.Samples 2) :
    ((netlist n).step i.values (Extended.values s (stageValues p)) : Values (Extended R Stage)) =
      (fun {_} r => Extended.values (n.step (engineInputs i p).values s) (stageValues (advance i p)) r) := by
  funext w r
  cases r with
  | inner r =>
    simp only [netlist, Netlist.extend_inner, input_values]
    rfl
  | extra x =>
    simp only [netlist, Netlist.extend_extra]
    cases x <;> rfl

theorem observe_eq (n : Netlist R Machine.Output Machine.Input) (i : Machine.Inputs)
    (s : Values R) (p : PinBoundary.Samples 2) :
    ((netlist n).observe i.values (Extended.values s (stageValues p)) : Values Machine.Output) =
      (fun {_} o => n.observe (engineInputs i p).values s o) := by
  funext w o
  simp only [netlist, Netlist.extend_observe, input_values]
  rfl

/-- Every edge of the wrapped netlist is one edge of the inner netlist on the
delayed input history: no edge is added, removed or reordered. -/
theorem trace_eq (n : Netlist R Machine.Output Machine.Input) (s : Values R)
    (p : PinBoundary.Samples 2) (inputs : List Machine.Inputs) :
    (component (netlist n)).trace (Extended.values s (stageValues p)) inputs =
      (component n).pairTrace s (delayed p inputs) := by
  induction inputs generalizing s p with
  | nil => rfl
  | cons i rest ih =>
    have hs := step_eq n i s p
    have ho := observe_eq n i s p
    have hn := observe_eq n i (n.step (engineInputs i p).values s) (advance i p)
    simp only [Timed.Component.trace, Timed.Component.pairTrace, Timed.Component.edge,
      component, delayed] at ih ⊢
    rw [hs, ho, hn]
    exact congrArg _ (ih _ _)

/-- The inner netlist consumes on edge n+2 the pin value presented on edge n,
for every history and every power-up content of the pipeline. -/
theorem delayed_two_edges (p : PinBoundary.Samples 2) (a b c : Machine.Inputs)
    (rest : List Machine.Inputs) :
    ((delayed p (a :: b :: c :: rest))[2]?).map (·.1.incoming) = some a.incoming := rfl

/-- The pipeline contents follow the boundary contract with its reset tied low. -/
theorem advance_contract (i : Machine.Inputs) (p : PinBoundary.Samples 2) :
    advance i p = PinBoundary.sampleStep 0 false i.incoming p := rfl

/-- Host ports are never delayed or altered, before or after the edge. -/
theorem delayed_host (p : PinBoundary.Samples 2) (i : Machine.Inputs) (rest : List Machine.Inputs) :
    ((delayed p (i :: rest)).head?).map
        (fun e => ((e.1.init, e.1.reset, e.1.command, e.1.data), (e.2.init, e.2.reset, e.2.command, e.2.data))) =
      some ((i.init, i.reset, i.command, i.data), (i.init, i.reset, i.command, i.data)) := rfl

/-- A condition on the data port of every input holds of every input the delayed
history lets an edge consume: the pipeline never touches host ports. -/
theorem delayed_data (Q : BitVec 64 → Prop) (p : PinBoundary.Samples 2) (inputs : List Machine.Inputs)
    (h : ∀ i ∈ inputs, Q i.data) : ∀ e ∈ delayed p inputs, Q e.1.data := by
  induction inputs generalizing p with
  | nil =>
    intro e he
    simp [delayed] at he
  | cons i rest ih =>
    intro e he
    simp only [delayed, List.mem_cons] at he
    rcases he with rfl | he
    · exact h i (List.mem_cons_self ..)
    · exact ih (advance i p) (fun j hj => h j (List.mem_cons_of_mem i hj)) e he

/-- Transitions launched only at the pin port. -/
def pinLaunch : Launch Machine.Input
  | _, .incoming => some 0
  | _, .init => none
  | _, .reset => none
  | _, .command => none
  | _, .data => none

theorem input_arrival_none (pick : Pick) (cost : Cost) {w : Nat} (q : Machine.Input w) :
    (input (R := R) q).arrival pick cost pinLaunch (fun _ => none) = none := by
  cases q <;> rfl

/-- No combinational path leads from a pin to any inner register, whatever the
inner netlist is: the pin port's external delay budget reaches one flip-flop. -/
theorem no_path_from_pins (pick : Pick) (cost : Cost)
    (n : Netlist R Machine.Output Machine.Input) (r : R w) :
    (netlist n).arrivalNext pick cost pinLaunch (fun _ => none) (.inner r) = none := by
  rw [netlist, Netlist.arrivalNext_extend]
  exact Netlist.arrivalNext_none pick cost n _ _
    (fun q => input_arrival_none pick cost q) (fun _ => rfl) r

/-- Nor to any output. -/
theorem no_output_path_from_pins (pick : Pick) (cost : Cost)
    (n : Netlist R Machine.Output Machine.Input) (o : Machine.Output w) :
    (netlist n).arrivalOutput pick cost pinLaunch (fun _ => none) o = none := by
  rw [netlist, Netlist.arrivalOutput_extend]
  exact Netlist.arrivalOutput_none pick cost n _ _
    (fun q => input_arrival_none pick cost q) (fun _ => rfl) o

/-- The pin reaches exactly the first stage, through no logic at all. -/
theorem pins_reach_first_stage (pick : Pick) (cost : Cost)
    (n : Netlist R Machine.Output Machine.Input) :
    (netlist n).arrivalNext pick cost pinLaunch (fun _ => none) (.extra .first) = some 0 ∧
    (netlist n).arrivalNext pick cost pinLaunch (fun _ => none) (.extra .second) = none := by
  constructor <;> rw [netlist, Netlist.arrivalNext_extend_extra] <;> rfl

end Pinwheel.Hardware.PinSampler
