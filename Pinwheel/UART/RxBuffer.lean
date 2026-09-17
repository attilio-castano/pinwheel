import Pinwheel.UART.RxSpec

namespace Pinwheel.UART.Rx.Buffer

/-- One retained outcome; proof traces below are not additional stored state. -/
structure State where
  pending : Option Outcome := none
  overrun : Bool := false
  deriving DecidableEq, Repr

inductive Command where
  | reset
  | cycle (arrival : Option Outcome) (take clearOverrun : Bool)
  deriving DecidableEq, Repr

def Command.arrival : Command → Option Outcome
  | .reset => none
  | .cycle arrival _ _ => arrival

/-- Edge observations used for ownership and loss accounting. -/
structure Receipt where
  accepted : Option Outcome := none
  delivered : Option Outcome := none
  dropped : Option Outcome := none
  flushed : Option Outcome := none
  deriving DecidableEq, Repr

structure Transition where
  state : State
  receipt : Receipt
  deriving DecidableEq, Repr

/-- Consume the old slot first, then admit or drop the new outcome. No empty-slot bypass. -/
def step (s : State) : Command → Transition
  | .reset => ⟨{}, {flushed := s.pending}⟩
  | .cycle arrival take clear =>
    let delivered := if take then s.pending else none
    let retained := if take then none else s.pending
    match retained with
    | none => ⟨⟨arrival, s.overrun && !clear⟩, {accepted := arrival, delivered := delivered}⟩
    | some old =>
      ⟨⟨some old, (s.overrun && !clear) || arrival.isSome⟩,
        {delivered := delivered, dropped := arrival}⟩

structure Trace where
  state : State
  receipts : List Receipt
  deriving DecidableEq, Repr

def run (s : State) : List Command → Trace
  | [] => ⟨s, []⟩
  | command :: rest =>
    let edge := step s command
    let tail := run edge.state rest
    ⟨tail.state, edge.receipt :: tail.receipts⟩

def accepted (rs : List Receipt) : List Outcome := rs.flatMap (fun r => r.accepted.toList)
def delivered (rs : List Receipt) : List Outcome := rs.flatMap (fun r => r.delivered.toList)
def dropped (rs : List Receipt) : List Outcome := rs.flatMap (fun r => r.dropped.toList)
def flushed (rs : List Receipt) : List Outcome := rs.flatMap (fun r => r.flushed.toList)
def retired (rs : List Receipt) : List Outcome :=
  rs.flatMap (fun r => r.delivered.toList ++ r.flushed.toList)
def arrivals (cs : List Command) : List Outcome := cs.flatMap (fun c => c.arrival.toList)

end Pinwheel.UART.Rx.Buffer
