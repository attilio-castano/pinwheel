import Pinwheel.Program.TransferProofs

/-! Executable adversarial ownership checks. These are model traces, not
package, RTL or peer simulations. Universal safety is checked by the kernel
proofs imported above; finite traces exercise observable replies and bit order. -/
open Pinwheel.Program.Transfer

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def invariant (capacity : Capacity) (s : State) : Bool :=
  let requestOK (r : Request) :=
    r.tx.length ≤ capacity.txBits && r.rxLimit ≤ capacity.rxBits &&
      r.identity.epoch == s.epoch && r.identity.sequence < s.nextSequence
  let executionOK (e : Execution) :=
    requestOK e.request && e.txConsumed ≤ e.request.tx.length && e.rx.length ≤ e.request.rxLimit
  match s.slot with
  | .free => true
  | .preparing r => requestOK r
  | .running e => executionOK e
  | .completed c => executionOK c.execution

private def edge (capacity : Capacity) (s : State) (command : Command)
    (reply : Reply) (label : String) : IO State := do
  let result := step capacity s command
  ensure (result.reply == reply) s!"{label}: unexpected reply {repr result.reply}"
  ensure (invariant capacity result.state) s!"{label}: ownership invariant failed"
  return result.state

private def unchanged (capacity : Capacity) (s : State) (command : Command)
    (reason : Rejection) (label : String) : IO Unit := do
  let actual ← edge capacity s command (.rejected reason) label
  ensure (actual == s) s!"{label}: rejection modified storage"

private def dataCase (length : Nat) (outcome : Outcome) : IO Nat := do
  let capacity : Capacity := ⟨length, length⟩
  let tx := (List.range length).map fun n => n % 3 == 1
  let incoming := (List.range length).map fun n => decide (n % 5 < 2)
  let id : Identity := ⟨0, 1⟩
  let wrong : Identity := ⟨0, 2⟩
  let mut s ← edge capacity {} (.prepare 17 tx length) (.prepared id) "prepare copy"
  unchanged capacity s (.start id 18) .programGeneration "stale program generation"
  unchanged capacity s (.release id) .wrongPhase "prepared cannot release"
  s ← edge capacity s (.start id 17) .started "START"
  unchanged capacity s (.prepare 17 tx length) .wrongPhase "active cannot overwrite"
  unchanged capacity s (.release id) .wrongPhase "active cannot release"
  let consumed := if outcome == .complete then length else length / 2
  for n in [:consumed] do
    s ← edge capacity s (.consumeTx id) (.txBit tx[n]!) "consume wire-order TX bit"
    s ← edge capacity s (.appendRx id incoming[n]!) .rxStored "append independent RX bit"
  if outcome == .complete then
    unchanged capacity s (.consumeTx id) .txExhausted "TX exhaustion"
    unchanged capacity s (.appendRx id false) .rxFull "RX reservation exhaustion"
  let .running execution := s.slot | throw (IO.userError "engine is not running")
  ensure (execution.request.tx == tx && execution.txConsumed == consumed && execution.rx == incoming.take consumed)
    "consumption changed TX or lost/reordered RX prefix"
  let completion : Completion := ⟨execution, outcome⟩
  s ← edge capacity s (.finish id outcome) .finished "finish with retained prefix"
  for _ in [:3] do
    let read ← edge capacity s (.read id) (.result completion) "repeat non-destructive read"
    ensure (read == s) "read consumed result storage"
  unchanged capacity s (.prepare 17 tx length) .wrongPhase "unread cannot overwrite"
  unchanged capacity s (.consumeTx id) .wrongPhase "terminal TX cannot advance"
  unchanged capacity s (.appendRx id true) .wrongPhase "terminal RX cannot change"
  unchanged capacity s (.finish id .fault) .wrongPhase "terminal outcome cannot change"
  unchanged capacity s (.release wrong) .wrongIdentity "stale release"
  s ← edge capacity s (.release id) .released "matching release"
  s ← edge capacity s (.prepare 18 tx length) (.prepared wrong) "slot reuse allocates fresh identity"
  unchanged capacity s (.release id) .wrongIdentity "old acknowledgement cannot free reused slot"
  unchanged capacity s (.start id 18) .wrongIdentity "old start cannot restart reused slot"
  s ← edge capacity s .reset .reset "reset invalidates identities"
  let afterReset : Identity := ⟨1, 1⟩
  s ← edge capacity s (.prepare 18 tx length) (.prepared afterReset) "reset uses fresh epoch"
  unchanged capacity s (.start wrong 18) .wrongIdentity "pre-reset request cannot start"
  unchanged capacity s (.release wrong) .wrongIdentity "pre-reset request cannot release"
  return 2 * consumed

private def commands (s : State) : List Command :=
  let current := s.slot.identity.getD ⟨s.epoch, s.nextSequence⟩
  let stale : Identity := ⟨s.epoch + 1, current.sequence⟩
  [.prepare 0 [] 0, .prepare 0 [false, true] 2, .prepare 1 [true, false, true] 3,
    .start current 0, .start current 1, .consumeTx current,
    .appendRx current false, .appendRx current true, .finish current .complete,
    .finish current .timeout, .finish current .fault, .read current, .release current,
    .consumeTx stale, .appendRx stale true, .release stale, .reset]

private def walk (capacity : Capacity) (s : State) : Nat → IO Nat
  | 0 => pure 0
  | depth + 1 => do
    let mut count := 0
    for command in commands s do
      let actual := step capacity s command
      ensure (invariant capacity actual.state) "adversarial trace broke bounds or identity provenance"
      match actual.reply with
      | .rejected _ => ensure (actual.state == s) "rejected command changed state"
      | _ => pure ()
      if let some id := command.identity then
        if s.slot.identity != some id then
          ensure (actual == reject s .wrongIdentity) "wrong identity reached storage"
      if let .completed _ := s.slot then
        if command != .reset && command != .release (s.slot.identity.getD ⟨0, 0⟩) then
          ensure (actual.state == s) "unread completion was overwritten"
      count := count + 1 + (← walk capacity actual.state depth)
    return count

def main : IO Unit := do
  let mut directed := 0
  for length in [0, 1, 7, 8, 13, 32, 64] do
    for outcome in [Outcome.complete, .timeout, .fault] do
      directed := directed + (← dataCase length outcome)
  let mut traces := 0
  for txCapacity in [:3] do
    for rxCapacity in [:3] do
      traces := traces + (← walk ⟨txCapacity, rxCapacity⟩ {} 4)
  IO.println s!"Finite transfer ownership: 21 directed lifecycle cases ({directed} engine bit operations), {traces} adversarial command edges; exact non-byte bit order, frozen TX, retained complete/failure prefixes, capacity/exhaustion rejection, unread retention, generation/identity admission, release/reuse/reset passed. Parametric model only; no hardware storage or protocol timing claim."

#print axioms Pinwheel.Program.Transfer.admittedStep_valid
#print axioms Pinwheel.Program.Transfer.step_valid
#print axioms Pinwheel.Program.Transfer.run_valid
#print axioms Pinwheel.Program.Transfer.wrong_identity_rejected
#print axioms Pinwheel.Program.Transfer.wrong_epoch_rejected
#print axioms Pinwheel.Program.Transfer.read_nondestructive
#print axioms Pinwheel.Program.Transfer.completed_retained
#print axioms Pinwheel.Program.Transfer.consume_tx_exact
#print axioms Pinwheel.Program.Transfer.append_rx_exact
#print axioms Pinwheel.Program.Transfer.finish_retains_execution
#print axioms Pinwheel.Program.Transfer.start_freezes_request
#print axioms Pinwheel.Program.Transfer.running_release_rejected
#print axioms Pinwheel.Program.Transfer.release_then_prepare_rejects_old_identity
#print axioms Pinwheel.Program.Transfer.reset_then_prepare_rejects_old_identity
