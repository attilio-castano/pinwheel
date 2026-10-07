import Pinwheel.Engine.Fetch

/-! Counted instruction storage: two nested loop indices, two data bytes, no expansion at run time.
The execution PC counts semantic slots; fetch decodes it into a stored template and loop indices. -/
namespace Pinwheel.Engine.Reactive.Counted

abbrev Environment := Vector (Fin 8) 2

inductive Index where
  | literal (value : Fin 8)
  | loop (depth : Fin 2)
  deriving DecidableEq, Repr

def Index.eval (i : Index) (env : Environment) : Fin 8 := match i with
  | .literal v => v
  | .loop d => env[d.val]

structure Serial where
  byte : Index
  bit : Index
  msbFirst : Bool := true
  invert : Bool := false
  deriving DecidableEq, Repr

/-- Selection can affect a value bit or a drive-enable bit, supporting push-pull or open-drain use. -/
inductive PinExpr where
  | literal (pins : Pins)
  | serial (base : Pins) (pin : Fin 3) (enable : Bool) (source : Serial)
  deriving DecidableEq, Repr

def PinExpr.eval (expr : PinExpr) (data : Vector (BitVec 8) 2) (env : Environment) : Option Pins :=
  match expr with
  | .literal pins => some pins
  | .serial base pin enable source => do
    let byte ← data.toArray[source.byte.eval env |>.val]?
    let index := (source.bit.eval env).val
    let value := byte.getLsbD (if source.msbFirst then 7 - index else index) != source.invert
    let mask : Levels := BitVec.ofNat 3 (2 ^ pin.val)
    let old := if enable then base.enabled else base.levels
    let new := if value then old ||| mask else old &&& ~~~mask
    return if enable then {base with enabled := new} else {base with levels := new}

structure Sample where
  input : Fin 2
  destination : Index
  deriving DecidableEq, Repr

def Sample.eval (c : Sample) (env : Environment) : Capture := ⟨c.input, c.destination.eval env⟩

inductive Target where
  | absolute (pc : Fin 128)
  | next
  deriving DecidableEq, Repr

def Target.eval (t : Target) (pc : Fin 128) : Option (Fin 128) := match t with
  | .absolute target => some target
  | .next => if h : pc.val + 1 < 128 then some ⟨pc.val + 1, h⟩ else none

inductive Transfer where
  | sequential
  | jump (target : Target)
  | branch (sample : Index) (whenTrue whenFalse : Target)
  deriving DecidableEq, Repr

def Transfer.eval (f : Transfer) (env : Environment) (pc : Fin 128) : Option Finish :=
  match f with
  | .sequential => some .sequential
  | .jump target => return .jump (← target.eval pc)
  | .branch sample yes no => return .branch (sample.eval env) (← yes.eval pc) (← no.eval pc)

/-- At most one loop-index comparison per successor; this is a bounded selector, not an AST. -/
inductive Successor where
  | sequential
  | jump (target : Target)
  | branch (sample : Index) (whenTrue whenFalse : Target)
  | select (index : Index) (value : Fin 8) (whenEqual otherwise : Transfer)
  deriving DecidableEq, Repr

def Successor.eval (f : Successor) (env : Environment) (pc : Fin 128) : Option Finish :=
  match f with
  | .sequential => Transfer.sequential.eval env pc
  | .jump target => (Transfer.jump target).eval env pc
  | .branch sample yes no => (Transfer.branch sample yes no).eval env pc
  | .select index value yes no => (if index.eval env == value then yes else no).eval env pc

inductive Template where
  | action (pins : PinExpr) (durationMinusOne : Fin 256) (capture : Option Sample := none)
  | wait (pins : PinExpr) (condition : Condition) (budgetMinusOne : Fin 256)
  | checked (pins : PinExpr) (durationMinusOne : Fin 256) (guard : Check)
      (entryCapture terminalCapture : Option Sample := none) (finish : Successor := .sequential)
  | qualify (pins : PinExpr) (condition : Check) (durationMinusOne budgetMinusOne : Fin 256)
  | halt
  deriving DecidableEq, Repr

def Template.eval (t : Template) (data : Vector (BitVec 8) 2) (env : Environment)
    (pc : Fin 128) : Option Instruction := do
  match t with
  | .action pins d c => return .action ⟨← pins.eval data env, d, c.map (·.eval env)⟩
  | .wait pins cond w => return .wait ⟨← pins.eval data env, cond, w⟩
  | .checked pins d guard entry terminal finish =>
    return .checked ⟨⟨← pins.eval data env, d, entry.map (·.eval env)⟩, guard,
      terminal.map (·.eval env), ← finish.eval env pc⟩
  | .qualify pins cond d w => return .qualify ⟨← pins.eval data env, cond, d, w⟩
  | .halt => return .halt

inductive Code where
  | emit (instruction : Template)
  | seq (first rest : Code)
  | repeat (countMinusOne : Fin 8) (body : Code)
  deriving DecidableEq, Repr

/-- Number of execution addresses, including repeated iterations. -/
def Code.span : Code → Nat
  | .emit _ => 1
  | .seq a b => a.span + b.span
  | .repeat n body => (n.val + 1) * body.span

/-- Number of stored instructions; loop descriptors are counted separately. -/
def Code.words : Code → Nat
  | .emit _ => 1
  | .seq a b => a.words + b.words
  | .repeat _ body => body.words

def Code.loops : Code → Nat
  | .emit _ => 0
  | .seq a b => a.loops + b.loops
  | .repeat _ body => 1 + body.loops

/-- Bound the full stored syntax, including sequence and loop descriptors. -/
def Code.nodes : Code → Nat
  | .emit _ => 1
  | .seq a b => 1 + a.nodes + b.nodes
  | .repeat _ body => 1 + body.nodes

def Code.nesting : Code → Nat
  | .emit _ => 0
  | .seq a b => max a.nesting b.nesting
  | .repeat _ body => 1 + body.nesting

/-- Depth zero names the innermost loop. Loaded programs allow at most two nested loops. -/
def Code.locate : Code → Environment → Nat → Option (Template × Environment)
  | .emit t, env, pc => if pc = 0 then some (t, env) else none
  | .seq a b, env, pc => if pc < a.span then a.locate env pc else b.locate env (pc - a.span)
  | .repeat n body, env, pc =>
    if pc < (n.val + 1) * body.span then
      body.locate #v[Fin.ofNat 8 (pc / body.span), env[0]] (pc % body.span)
    else none

/-- The counted address decoder generalized over its stored leaf type. This
shares the existing two-index environment and geometry; a new leaf type does
not require materializing its repeated virtual execution addresses. -/
inductive Schedule (α : Type) where
  | emit (instruction : α)
  | seq (first rest : Schedule α)
  | repeat (countMinusOne : Fin 8) (body : Schedule α)
  deriving DecidableEq, Repr

def Schedule.span : Schedule α → Nat
  | .emit _ => 1
  | .seq a b => a.span + b.span
  | .repeat n body => (n.val + 1) * body.span

def Schedule.words : Schedule α → Nat
  | .emit _ => 1
  | .seq a b => a.words + b.words
  | .repeat _ body => body.words

def Schedule.loops : Schedule α → Nat
  | .emit _ => 0
  | .seq a b => a.loops + b.loops
  | .repeat _ body => 1 + body.loops

def Schedule.nodes : Schedule α → Nat
  | .emit _ => 1
  | .seq a b => 1 + a.nodes + b.nodes
  | .repeat _ body => 1 + body.nodes

def Schedule.nesting : Schedule α → Nat
  | .emit _ => 0
  | .seq a b => max a.nesting b.nesting
  | .repeat _ body => 1 + body.nesting

def Schedule.locate : Schedule α → Environment → Nat → Option (α × Environment)
  | .emit t, env, pc => if pc = 0 then some (t, env) else none
  | .seq a b, env, pc => if pc < a.span then a.locate env pc else b.locate env (pc - a.span)
  | .repeat n body, env, pc =>
    if pc < (n.val + 1) * body.span then
      body.locate #v[Fin.ofNat 8 (pc / body.span), env[0]] (pc % body.span)
    else none

/-- The old two-byte template schedule embeds without changing its limits or
its instruction/data semantics. -/
def Code.schedule : Code → Schedule Template
  | .emit t => .emit t
  | .seq a b => .seq a.schedule b.schedule
  | .repeat n body => .repeat n body.schedule

theorem Code.schedule_span (code : Code) : code.schedule.span = code.span := by
  induction code <;> simp_all [Code.schedule, Schedule.span, Code.span]
  done

theorem Code.schedule_locate (code : Code) (env : Environment) (pc : Nat) :
    code.schedule.locate env pc = code.locate env pc := by
  induction code generalizing env pc <;> simp_all [Code.schedule, Schedule.locate, Code.locate, Code.schedule_span]
  done

structure Program where
  code : Code
  data : Vector (BitVec 8) 2
  idle : Pins
  fits : code.span ≤ 128
  nodesFit : code.nodes ≤ 64
  nestingFit : code.nesting ≤ 2
  deriving Repr

/-- Padding is halt, just like the explicit image. Bad data/target operands fetch a fault. -/
def Program.fetch (p : Program) (pc : Fin 128) : Option Instruction :=
  match p.code.locate (Vector.replicate 2 0) pc.val with
  | none => some .halt
  | some (t, env) => t.eval p.data env pc

def Program.store (p : Program) : Fetch.Store :=
  ⟨p.fetch, p.idle, ⟨p.code.span - 1, by have := p.fits; omega⟩⟩

end Pinwheel.Engine.Reactive.Counted
