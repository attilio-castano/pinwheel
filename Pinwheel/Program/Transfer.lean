import Init

/-! A single finite-transfer ownership contract. This is a parametric model,
not an implementation of storage, protocol timing, or the package command bus.
Preparing copies the complete TX value atomically. Counts measure bits consumed
by the engine and bits appended to RX, not electrical effects on a peer.
Identities use unbounded naturals; a finite hardware encoding needs a separate
wraparound and reset-persistence contract. -/
namespace Pinwheel.Program.Transfer

structure Capacity where
  txBits : Nat
  rxBits : Nat
  deriving DecidableEq, Repr

structure Identity where
  epoch : Nat
  sequence : Nat
  deriving DecidableEq, Repr

/-- Bit lists are in engine-consumption order; protocols choose wire ordering. -/
structure Request where
  identity : Identity
  programGeneration : Nat
  tx : List Bool
  rxLimit : Nat
  deriving DecidableEq, Repr

structure Execution where
  request : Request
  txConsumed : Nat := 0
  rx : List Bool := []
  deriving DecidableEq, Repr

inductive Outcome where
  /-- Engine testimony of normal completion; this does not establish peer
  effects or that every reserved RX bit was filled. -/
  | complete | timeout | fault
  deriving DecidableEq, Repr

/-- Failure retains the observed prefix for diagnostics. Protocol decoders
must separately decide whether that prefix is a usable application result. -/
structure Completion where
  execution : Execution
  outcome : Outcome
  deriving DecidableEq, Repr

inductive Slot where
  | free
  | preparing (request : Request)
  | running (execution : Execution)
  | completed (completion : Completion)
  deriving DecidableEq, Repr

def Slot.identity : Slot → Option Identity
  | .free => none
  | .preparing r => some r.identity
  | .running e => some e.request.identity
  | .completed c => some c.execution.request.identity

structure State where
  epoch : Nat := 0
  nextSequence : Nat := 1
  slot : Slot := .free
  deriving DecidableEq, Repr

inductive Command where
  | prepare (programGeneration : Nat) (tx : List Bool) (rxLimit : Nat)
  | start (identity : Identity) (programGeneration : Nat)
  | consumeTx (identity : Identity)
  | appendRx (identity : Identity) (bit : Bool)
  | finish (identity : Identity) (outcome : Outcome)
  | read (identity : Identity)
  | release (identity : Identity)
  | reset
  deriving DecidableEq, Repr

def Command.identity : Command → Option Identity
  | .prepare _ _ _ | .reset => none
  | .start id _ | .consumeTx id | .appendRx id _ | .finish id _
    | .read id | .release id => some id

inductive Rejection where
  | wrongIdentity | wrongPhase | capacity | programGeneration | txExhausted | rxFull
  deriving DecidableEq, Repr

inductive Reply where
  | prepared (identity : Identity)
  | started
  | txBit (bit : Bool)
  | rxStored
  | finished
  | result (completion : Completion)
  | released
  | reset
  | rejected (reason : Rejection)
  deriving DecidableEq, Repr

structure Transition where
  state : State
  reply : Reply
  deriving DecidableEq, Repr

def reject (s : State) (reason : Rejection) : Transition := ⟨s, .rejected reason⟩

/-- Operations after identity admission. No host wait operation exists here:
stopping a wait neither finishes the engine nor releases its storage. A prepared
slot may be abandoned only through reset in this first contract. -/
def admittedStep (capacity : Capacity) (s : State) : Command → Transition
  | .prepare generation tx rxLimit =>
    match s.slot with
    | .free =>
      if tx.length ≤ capacity.txBits ∧ rxLimit ≤ capacity.rxBits then
        let id : Identity := ⟨s.epoch, s.nextSequence⟩
        let request : Request := ⟨id, generation, tx, rxLimit⟩
        ⟨{s with nextSequence := s.nextSequence + 1, slot := .preparing request}, .prepared id⟩
      else reject s .capacity
    | _ => reject s .wrongPhase
  | .start _ generation =>
    match s.slot with
    | .preparing request =>
      if generation = request.programGeneration then
        ⟨{s with slot := .running ⟨request, 0, []⟩}, .started⟩
      else reject s .programGeneration
    | _ => reject s .wrongPhase
  | .consumeTx _ =>
    match s.slot with
    | .running execution =>
      match execution.request.tx[execution.txConsumed]? with
      | some bit =>
        ⟨{s with slot := .running {execution with txConsumed := execution.txConsumed + 1}}, .txBit bit⟩
      | none => reject s .txExhausted
    | _ => reject s .wrongPhase
  | .appendRx _ bit =>
    match s.slot with
    | .running execution =>
      if execution.rx.length < execution.request.rxLimit then
        ⟨{s with slot := .running {execution with rx := execution.rx ++ [bit]}}, .rxStored⟩
      else reject s .rxFull
    | _ => reject s .wrongPhase
  | .finish _ outcome =>
    match s.slot with
    | .running execution =>
      ⟨{s with slot := .completed ⟨execution, outcome⟩}, .finished⟩
    | _ => reject s .wrongPhase
  | .read _ =>
    match s.slot with
    | .completed completion => ⟨s, .result completion⟩
    | _ => reject s .wrongPhase
  | .release _ =>
    match s.slot with
    | .completed _ => ⟨{s with slot := .free}, .released⟩
    | _ => reject s .wrongPhase
  | .reset => ⟨⟨s.epoch + 1, 1, .free⟩, .reset⟩

/-- Wrong identities are rejected before any access or mutation. -/
def step (capacity : Capacity) (s : State) (command : Command) : Transition :=
  match command.identity with
  | none => admittedStep capacity s command
  | some id =>
    if s.slot.identity = some id then admittedStep capacity s command
    else reject s .wrongIdentity

def Request.Bounded (capacity : Capacity) (r : Request) : Prop :=
  r.tx.length ≤ capacity.txBits ∧ r.rxLimit ≤ capacity.rxBits

def Execution.Bounded (capacity : Capacity) (e : Execution) : Prop :=
  e.request.Bounded capacity ∧ e.txConsumed ≤ e.request.tx.length ∧
    e.rx.length ≤ e.request.rxLimit

def Slot.Bounded (capacity : Capacity) : Slot → Prop
  | .free => True
  | .preparing request => request.Bounded capacity
  | .running execution => execution.Bounded capacity
  | .completed completion => completion.execution.Bounded capacity

def State.Valid (capacity : Capacity) (s : State) : Prop :=
  s.slot.Bounded capacity ∧ ∀ id, s.slot.identity = some id →
    id.epoch = s.epoch ∧ id.sequence < s.nextSequence

structure Trace where
  state : State
  replies : List Reply
  deriving DecidableEq, Repr

def run (capacity : Capacity) (s : State) : List Command → Trace
  | [] => ⟨s, []⟩
  | command :: rest =>
    let edge := step capacity s command
    let tail := run capacity edge.state rest
    ⟨tail.state, edge.reply :: tail.replies⟩

end Pinwheel.Program.Transfer
