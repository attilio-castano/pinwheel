import Pinwheel.Hardware.HostResult
import Pinwheel.UART.RxBufferProofs
import Init.Data.Vector.OfFn
import Init.Data.BitVec.Lemmas

/-! The actual result observer refines a one-entry queue on its consumed edge.
Receipts and histories are proof observations, not additional circuit state. -/
namespace Pinwheel.Hardware.HostResultBuffer

namespace Retained

structure State (α : Type) where
  pending : Option α := none
  overrun : Bool := false
  deriving DecidableEq, Repr

inductive Command (α : Type) where
  | reset
  | cycle (arrival : Option α) (take clearOverrun : Bool)
  deriving DecidableEq, Repr

def Command.arrival : Command α → Option α
  | .reset => none
  | .cycle arrival _ _ => arrival

structure Receipt (α : Type) where
  accepted : Option α := none
  delivered : Option α := none
  dropped : Option α := none
  flushed : Option α := none
  deriving DecidableEq, Repr

structure Transition (α : Type) where
  state : State α
  receipt : Receipt α
  deriving DecidableEq, Repr

/-- Consume the old slot before admitting a new occurrence; an empty take does not bypass it. -/
def step (s : State α) : Command α → Transition α
  | .reset => ⟨{}, {flushed := s.pending}⟩
  | .cycle arrival take clear =>
    let delivered := if take then s.pending else none
    let retained := if take then none else s.pending
    match retained with
    | none => ⟨⟨arrival, s.overrun && !clear⟩, {accepted := arrival, delivered := delivered}⟩
    | some old => ⟨⟨some old, (s.overrun && !clear) || arrival.isSome⟩,
        {delivered := delivered, dropped := arrival}⟩

structure Trace (α : Type) where
  state : State α
  receipts : List (Receipt α)
  deriving DecidableEq, Repr

def run (s : State α) : List (Command α) → Trace α
  | [] => ⟨s, []⟩
  | command :: rest =>
    let edge := step s command
    let tail := run edge.state rest
    ⟨tail.state, edge.receipt :: tail.receipts⟩

def accepted (rs : List (Receipt α)) : List α := rs.flatMap (fun r => r.accepted.toList)
def delivered (rs : List (Receipt α)) : List α := rs.flatMap (fun r => r.delivered.toList)
def dropped (rs : List (Receipt α)) : List α := rs.flatMap (fun r => r.dropped.toList)
def flushed (rs : List (Receipt α)) : List α := rs.flatMap (fun r => r.flushed.toList)
def retired (rs : List (Receipt α)) : List α :=
  rs.flatMap (fun r => r.delivered.toList ++ r.flushed.toList)
def arrivals (cs : List (Command α)) : List α := cs.flatMap (fun c => c.arrival.toList)

theorem accepted_cons (r : Receipt α) (rs : List (Receipt α)) :
    accepted (r :: rs) = r.accepted.toList ++ accepted rs := rfl

theorem retired_cons (r : Receipt α) (rs : List (Receipt α)) :
    retired (r :: rs) = (r.delivered.toList ++ r.flushed.toList) ++ retired rs := rfl

theorem step_order (s : State α) (command : Command α) :
    s.pending.toList ++ (step s command).receipt.accepted.toList =
      (step s command).receipt.delivered.toList ++ (step s command).receipt.flushed.toList ++
        (step s command).state.pending.toList := by
  cases command
  case reset => simp [step]
  case cycle arrival take clear =>
    cases take
    all_goals cases hp : s.pending
    all_goals simp [step, hp]
    done

theorem step_partition (s : State α) (command : Command α) :
    command.arrival.toList = (step s command).receipt.accepted.toList ++
      (step s command).receipt.dropped.toList := by
  cases command
  all_goals grind [step, Command.arrival]
  done

theorem run_order (s : State α) (commands : List (Command α)) :
    s.pending.toList ++ accepted (run s commands).receipts =
      retired (run s commands).receipts ++ (run s commands).state.pending.toList := by
  induction commands generalizing s
  case nil => simp [run, accepted, retired]
  case cons command rest ih =>
    simp only [run, accepted_cons, retired_cons, ← List.append_assoc]
    rw [step_order, List.append_assoc, List.append_assoc, ih]
    simp only [List.append_assoc]
    done

/-- Occurrences, including identical packets, are delivered, dropped, flushed or pending exactly once. -/
theorem run_accounting (s : State α) (commands : List (Command α)) :
    s.pending.toList.length + (arrivals commands).length =
      (delivered (run s commands).receipts).length +
      (dropped (run s commands).receipts).length +
      (flushed (run s commands).receipts).length +
      (run s commands).state.pending.toList.length := by
  induction commands generalizing s
  case nil => simp [run, arrivals, delivered, dropped, flushed]
  case cons command rest ih =>
    have order := congrArg List.length (step_order s command)
    have partition := congrArg List.length (step_partition s command)
    have tail := ih (step s command).state
    simp only [run, arrivals, delivered, dropped, flushed, List.flatMap_cons,
      List.length_append] at order partition tail ⊢
    omega
    done

end Retained

structure Packet where
  samples : BitVec 16
  outcome : BitVec 3
  deriving DecidableEq, Repr

/-- Invalid physical payload bits are not occupied logical state. -/
def project (s : HostResult.State) : Retained.State Packet :=
  ⟨if s.valid then some ⟨s.samples, s.outcome⟩ else none, s.overrun⟩

def arrival (o : Values Loader.Machine.Output) (s : HostResult.State) : Option Packet :=
  if HostResult.arriving o s then some ⟨HostResult.sampleValues o, o (.core (.state .mode))⟩ else none

/-- Synchronizer/edge-detector controls, rather than raw pin levels, own the logical edge. -/
def command (i : Chip.Pins) (o : Values Loader.Machine.Output) (s : HostResult.State) : Retained.Command Packet :=
  if HostResult.resetting i s then .reset
  else .cycle (arrival o s) (HostResult.consuming s) (HostResult.clearing s)

def receipt (i : Chip.Pins) (o : Values Loader.Machine.Output) (s : HostResult.State) : Retained.Receipt Packet :=
  (Retained.step (project s) (command i o s)).receipt

/-- Exact observer transition for arbitrary stored packet bits, observed results and controls. -/
theorem next_refines (i : Chip.Pins) (o : Values Loader.Machine.Output) (s : HostResult.State) :
    project (HostResult.next i o s) = (Retained.step (project s) (command i o s)).state := by
  grind [project, command, HostResult.next, Retained.step, HostResult.occupied, arrival]

/-- Both physical state and ghost ownership observations refine on the same pre-step output. -/
theorem transition_refines (i : Chip.Pins) (o : Values Loader.Machine.Output) (s : HostResult.State) :
    (⟨project (HostResult.next i o s), receipt i o s⟩ : Retained.Transition Packet) =
      Retained.step (project s) (command i o s) := by
  rw [next_refines]
  rfl

structure Edge where
  pins : Chip.Pins
  observed : Values Loader.Machine.Output

structure Trace where
  state : HostResult.State
  receipts : List (Retained.Receipt Packet)

def run (s : HostResult.State) : List Edge → Trace
  | [] => ⟨s, []⟩
  | edge :: rest =>
    let tail := run (HostResult.next edge.pins edge.observed s) rest
    ⟨tail.state, receipt edge.pins edge.observed s :: tail.receipts⟩

def commands (s : HostResult.State) : List Edge → List (Retained.Command Packet)
  | [] => []
  | edge :: rest => command edge.pins edge.observed s ::
      commands (HostResult.next edge.pins edge.observed s) rest

def projectTrace (t : Trace) : Retained.Trace Packet := ⟨project t.state, t.receipts⟩

/-- Arbitrary actual observer histories, without an assumed arrival or consumer schedule. -/
theorem run_refines (s : HostResult.State) (edges : List Edge) :
    projectTrace (run s edges) = Retained.run (project s) (commands s edges) := by
  induction edges generalizing s
  case nil => rfl
  case cons edge rest ih =>
    have tail := congrArg (fun t : Retained.Trace Packet =>
      (⟨t.state, receipt edge.pins edge.observed s :: t.receipts⟩ : Retained.Trace Packet))
      (ih (HostResult.next edge.pins edge.observed s))
    simpa only [projectTrace, run, commands, Retained.run, receipt, next_refines] using tail
    done

/-- Every packet accepted by the actual observer is retired in order or remains pending. -/
theorem history_order (s : HostResult.State) (edges : List Edge) :
    (project s).pending.toList ++ Retained.accepted (run s edges).receipts =
      Retained.retired (run s edges).receipts ++ (project (run s edges).state).pending.toList := by
  simpa only [← run_refines, projectTrace] using Retained.run_order (project s) (commands s edges)

/-- No occurrence disappears across actual observer edges, including duplicates and reset flushes. -/
theorem history_accounting (s : HostResult.State) (edges : List Edge) :
    (project s).pending.toList.length + (Retained.arrivals (commands s edges)).length =
      (Retained.delivered (run s edges).receipts).length +
      (Retained.dropped (run s edges).receipts).length +
      (Retained.flushed (run s edges).receipts).length +
      (project (run s edges).state).pending.toList.length := by
  simpa only [← run_refines, projectTrace] using Retained.run_accounting (project s) (commands s edges)

def sampleVector (bits : BitVec 16) : Vector Bool 16 := Vector.ofFn fun k => bits.getLsbD k.val

/-- A UART value projection, independent of engine outcome. Applying it as a
protocol interpretation requires a completed UART/core correspondence premise. -/
def uartOutcome (packet : Packet) : UART.Rx.Outcome := UART.Rx.outcome (sampleVector packet.samples)

def uartProject (s : HostResult.State) : UART.Rx.Buffer.State :=
  ⟨(project s).pending.map uartOutcome, s.overrun⟩

def uartCommand : Retained.Command Packet → UART.Rx.Buffer.Command
  | .reset => .reset
  | .cycle arrival take clear => .cycle (arrival.map uartOutcome) take clear

def uartReceipt (r : Retained.Receipt Packet) : UART.Rx.Buffer.Receipt :=
  ⟨r.accepted.map uartOutcome, r.delivered.map uartOutcome,
    r.dropped.map uartOutcome, r.flushed.map uartOutcome⟩

/-- Specialization is a value map, retaining occurrence ownership even for identical bytes. -/
theorem uart_next_refines (i : Chip.Pins) (o : Values Loader.Machine.Output) (s : HostResult.State) :
    (⟨uartProject (HostResult.next i o s), uartReceipt (receipt i o s)⟩ : UART.Rx.Buffer.Transition) =
      UART.Rx.Buffer.step (uartProject s) (uartCommand (command i o s)) := by
  grind [uartProject, uartReceipt, uartCommand, project, receipt, command, arrival,
    HostResult.next, HostResult.occupied, Retained.step, UART.Rx.Buffer.step]

theorem uart_received (bits : BitVec 16) :
    UART.Rx.received (sampleVector bits) = bits.extractLsb' 0 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have bound : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases bound with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [UART.Rx.received, sampleVector, Vector.getElem_ofFn, BitVec.getLsbD_ofBoolListBE]
  all_goals simp
  done

/-- Protocol errors remain completed engine packets; stop sample9 decides UART framing. -/
theorem uartOutcome_stop (packet : Packet) :
    uartOutcome packet = if packet.samples.getLsbD 9 then .byte (packet.samples.extractLsb' 0 8)
      else .framingError (packet.samples.extractLsb' 0 8) := by
  simp only [uartOutcome, UART.Rx.outcome, uart_received]
  simp only [sampleVector, Vector.getElem_ofFn]
  done

end Pinwheel.Hardware.HostResultBuffer
