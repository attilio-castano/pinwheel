import Lean

/-! Conditional availability for the revised, full-capacity paired layout.
The parameter table is a combinational FF array. Memory returns one 64-bit
response after the edge. Closed is a compiler/image premise, not a proof of
the Python compiler, E64 execution, admission, package RTL or physical timing. -/
namespace PairedSchedule

abbrev Word := BitVec 32
abbrev Row := BitVec 8
abbrev Index := BitVec 5
abbrev Memory := Row → BitVec 64
abbrev Parameters := Index → BitVec 20

def select (pair : BitVec 64) (choice : Bool) : Word :=
  if choice then pair.extractLsb' 32 32 else pair.extractLsb' 0 32

def row (word : Word) : Row := word.extractLsb' 22 8
def index (word : Word) : Index := word.extractLsb' 17 5

structure State where
  current : Word
  parameter : BitVec 20
  response : BitVec 64

def enter (memory : Memory) (parameters : Parameters) (word : Word) : State :=
  ⟨word, parameters (index word), memory (row word)⟩

def step (memory : Memory) (parameters : Parameters) (s : State) (choice : Bool) : State :=
  -- Parameter lookup and the next SRAM address both use the selected OLD Q.
  -- The SRAM response produced here serves the following dispatch.
  enter memory parameters (select s.response choice)

variable {Node : Type} (encode : Node → Word) (successor : Node → Bool → Node)

def Closed (memory : Memory) : Prop :=
  ∀ node choice, select (memory (row (encode node))) choice = encode (successor node choice)

def Related (memory : Memory) (parameters : Parameters) (s : State) (node : Node) : Prop :=
  s.current = encode node ∧ s.parameter = parameters (index (encode node)) ∧
    s.response = memory (row (encode node))

theorem step_related (memory : Memory) (parameters : Parameters) (s : State)
    (node : Node) (choice : Bool) (closed : Closed encode successor memory)
    (h : Related encode memory parameters s node) :
    Related encode memory parameters (step memory parameters s choice) (successor node choice) := by
  simp [Related, step, enter, h.2.2, closed node choice]
  done

def run (memory : Memory) (parameters : Parameters) (s : State) : List Bool → State
  | [] => s
  | choice :: rest => run memory parameters (step memory parameters s choice) rest

def referenceRun (node : Node) : List Bool → Node
  | [] => node
  | choice :: rest => referenceRun (successor node choice) rest

theorem trace_related (memory : Memory) (parameters : Parameters) (s : State)
    (node : Node) (choices : List Bool) (closed : Closed encode successor memory)
    (h : Related encode memory parameters s node) :
    Related encode memory parameters (run memory parameters s choices)
      (referenceRun successor node choices) := by
  induction choices generalizing s node with
  | cons choice rest ih => exact ih _ _ (step_related encode successor memory parameters s node choice closed h)
  | nil => exact h
  done

end PairedSchedule

open Lean Elab Command in
elab "#audit_paired_schedule" : command => do
  let env ← getEnv
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "PairedSchedule." then
      if info.isTheorem then theorems := theorems + 1
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax =>
        ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
      unless unexpected.isEmpty do
        throwError "Unapproved paired schedule axioms: {unexpected}"
  unless [``PairedSchedule.step_related, ``PairedSchedule.trace_related].all env.contains do
    throwError "Missing paired schedule theorem"
  logInfo m!"Paired schedule: {theorems} theorems; standard axioms only."

#audit_paired_schedule
