import Lean

/-! An isolated study of paired 32-bit successors in one synchronous 64-bit
read. This is not imported by the chip. Closed is an explicit compiler/image
premise, not a proved property of the Python encoder or arbitrary E64 programs.
No gate/wire delay, capture, loader, payload or whole-chip proof is implied. -/
namespace CompactSchedule

abbrev Word := BitVec 32
abbrev Row := BitVec 5
abbrev Memory := Row → BitVec 64

def select (pair : BitVec 64) (choice : Bool) : Word :=
  if choice then pair.extractLsb' 32 32 else pair.extractLsb' 0 32

def row (word : Word) : Row := word.extractLsb' 22 5

structure State where
  current : Word
  response : BitVec 64

def step (memory : Memory) (s : State) (choice : Bool) : State :=
  let entered := select s.response choice
  -- Both expressions use the old response. The one read returns after this
  -- edge and serves the NEXT selection, even for consecutive dispatches.
  ⟨entered, memory (row entered)⟩

variable {Node : Type} (encode : Node → Word) (successor : Node → Bool → Node)

def Closed (memory : Memory) : Prop :=
  ∀ node choice, select (memory (row (encode node))) choice = encode (successor node choice)

def Related (memory : Memory) (s : State) (node : Node) : Prop :=
  s.current = encode node ∧ s.response = memory (row (encode node))

theorem step_related (memory : Memory) (s : State) (node : Node) (choice : Bool)
    (closed : Closed encode successor memory) (h : Related encode memory s node) :
    Related encode memory (step memory s choice) (successor node choice) := by
  simp [Related, step, h.2, closed node choice]
  done

def run (memory : Memory) (s : State) : List Bool → State
  | [] => s
  | choice :: rest => run memory (step memory s choice) rest

def referenceRun (node : Node) : List Bool → Node
  | [] => node
  | choice :: rest => referenceRun (successor node choice) rest

theorem trace_related (memory : Memory) (s : State) (node : Node) (choices : List Bool)
    (closed : Closed encode successor memory) (h : Related encode memory s node) :
    Related encode memory (run memory s choices) (referenceRun successor node choices) := by
  induction choices generalizing s node with
  | cons choice rest ih => exact ih _ _ (step_related encode successor memory s node choice closed h)
  | nil => exact h
  done

end CompactSchedule

open Lean Elab Command in
elab "#audit_compact_schedule" : command => do
  let env ← getEnv
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "CompactSchedule." then
      if info.isTheorem then theorems := theorems + 1
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax =>
        ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
      unless unexpected.isEmpty do
        throwError "Unapproved compact schedule axioms: {unexpected}"
  unless [``CompactSchedule.step_related, ``CompactSchedule.trace_related].all env.contains do
    throwError "Missing compact schedule theorem"
  logInfo m!"Compact schedule: {theorems} theorems; standard axioms only."

#audit_compact_schedule
