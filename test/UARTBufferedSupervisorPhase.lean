import Pinwheel.UART.BufferedSupervisorPhase

open Pinwheel Pinwheel.Hardware
open Pinwheel.UART.Rx.BufferedSupervisor

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def config : IO UART.Rx.Config :=
  match UART.Rx.Config.ofCycles 8 0 with
  | some cfg => pure cfg
  | none => throw (IO.userError "Invalid UART period")

private def rawArm : IO Unit := do
  let old : HostResultBuffer.Packet := ⟨0x5a, 6⟩
  let host : HostResult.State :=
    {resetFirst := true, resetSecond := true, controlSecond := 3,
      samples := old.samples, outcome := old.outcome, valid := true, overrun := true}
  let observed : Values Loader.Machine.Output := fun {w} o => match w, o with
    | _, .control .start => 1
    | _, _ => 0
  let pins : Chip.Pins := {}
  let receipt := HostResultBuffer.receipt pins observed host
  let next := HostResult.next pins observed host
  ensure (receipt.delivered == some old && receipt.accepted.isNone && receipt.dropped.isNone &&
    receipt.flushed.isNone && !next.valid && !next.overrun && next.wasActive)
    "ARM lost the generic pending packet's consume/clear event"

private def phaseBoundary : IO Unit := do
  let cfg ← config
  let old : UART.Rx.Outcome := .framingError 0x7d
  let buffer : UART.Rx.Buffer.State := ⟨some old, true⟩
  let incoming : Nat → Input := fun n =>
    {line := UART.Rx.Stream.wire ⟨7⟩ 4 [0xa5, 0xa5] n,
      start := n == 81 || n == 161, take := n == 1 || n == 165,
      clearOverrun := n == 1 || n == 161}
  let first := warmup buffer incoming
  ensure (first.receipt.delivered == some old && first.state == {})
    "First warm-up consumer event was suppressed"
  let mut actual : State := ⟨UART.Rx.initial, buffer, true⟩
  let mut compiled := lift cfg actual
  let mut post : UART.Rx.Stream.State := ⟨UART.Rx.initial, first.state⟩
  let mut previous : UART.Rx.Buffer.Receipt := {}
  let mut accepted := 0
  let mut dropped := 0
  let mut delivered := 0
  for n in [1:166] do
    let edge := step cfg actual (incoming n)
    let reference := UART.Rx.Stream.step cfg post (phaseInput incoming n)
    let machine := decodedStep cfg compiled (incoming n) (n % 2 == 0)
    ensure (edge.state.receiver == reference.state.receiver && edge.state.buffer == post.buffer &&
      edge.state.wasActive) s!"Pulse START/state phase at {n}"
    ensure (edge.receipt == if n == 1 then first.receipt else previous)
      s!"Receipt/control phase at {n}"
    ensure (machine.state == lift cfg edge.state && machine.receipt == edge.receipt)
      s!"Compiled phase at {n}"
    if edge.receipt.accepted.isSome then accepted := accepted + 1
    if edge.receipt.dropped.isSome then dropped := dropped + 1
    if edge.receipt.delivered.isSome then delivered := delivered + 1
    if n == 161 then
      ensure (edge.receipt.dropped == some (.byte 0xa5) && edge.state.buffer.overrun)
        "Fresh duplicate drop did not dominate simultaneous clear"
    actual := edge.state
    compiled := machine.state
    post := reference.state
    previous := reference.receipt
  ensure (accepted == 1 && dropped == 1 && delivered == 2 && actual.buffer.pending.isNone)
    "Initial delivery and repeated byte occurrences were not accounted for"

def main : IO Unit := do
  rawArm
  phaseBoundary
  IO.println "UART phase: generic ARM ownership, first consume/clear, pulse START, shifted receipts, duplicate clear/drop and compiled correspondence passed."

#print axioms arm_step
#print axioms step_not_ready
#print axioms stopped_finished
#print axioms mode_not_failure
#print axioms mode_finished
#print axioms execution_samples
#print axioms execution_coreCorresponds
#print axioms phase_run
#print axioms phase_receipt
#print axioms raw_arm_transition
#print axioms phase_receive_series
#print axioms phase_decoded_receive_series
