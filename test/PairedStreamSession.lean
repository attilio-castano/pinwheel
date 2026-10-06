import Pinwheel.Hardware.Storage.PairedStreamProgram

/-! Receipt and session-boundary regressions. These exercise the independent
receiver and generic mailbox without simulating the full controller expression
graph; the kernel session theorem supplies their link to certified hardware. -/
open Pinwheel Pinwheel.Hardware Storage.PairedStreamSession

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def config (cycles : Nat) : IO UART.Rx.Config :=
  match UART.Rx.Config.ofCycles cycles 0 with
  | some cfg => pure cfg
  | none => throw (IO.userError s!"Invalid UART period {cycles}")

private def finished (byte : BitVec 8) : UART.Rx.State :=
  {phase := .finished, samples := Vector.ofFn fun k =>
    if k.val < 8 then byte.getLsbD k.val else k.val == 9}

private def state (receiver : UART.Rx.State) (mailbox : Mailbox) (control : BitVec 2)
    (epoch : Nat) : ReferenceState :=
  let raw := erase mailbox
  let packet := raw.pending.getD ⟨0, 0⟩
  let storage : Storage.PairedCoverage.Tracked := {
    registers := fun {w} r => match w, r with
      | _, .valid => 1
      | _, _ => 0
    memory := ⟨fun _ => 0, 0⟩
    ledger := {}}
  let host : HostResult.State := {
    resetFirst := true
    resetSecond := true
    controlSecond := control
    samples := packet.samples
    outcome := packet.outcome
    valid := raw.pending.isSome
    overrun := raw.overrun
    wasActive := true}
  ⟨storage, true, receiver, {}, host, mailbox, true, epoch⟩

private def offer (s : ReferenceState) (command : BitVec 3) (data : BitVec 64) : ReferenceState :=
  {s with adapters := {s.adapters with
    receiver := {s.adapters.receiver with fire := true, command := command, shift := data}}}

private def reserved (enabled : Bool) (input : Loader.Machine.Inputs) : Bool :=
  @decide (Storage.PairedStreamOwnership.ReservedInput enabled input)
    (by unfold Storage.PairedStreamOwnership.ReservedInput; infer_instance)

private def boundaries (cfg : UART.Rx.Config) : IO Unit := do
  let old : OwnedPacket := ⟨⟨0xdead, 7⟩, .unknown⟩
  let full := state (finished 0xa5) ⟨some old, true⟩ 3 23
  let fresh : OwnedPacket := ⟨receiverPacket cfg full.receiver, .uart 23 cfg⟩
  let pins : Chip.Pins := {}
  let receipt := ownedReceipt cfg pins full
  ensure (receipt.delivered == some old && receipt.accepted == some fresh &&
    receipt.dropped.isNone && receipt.flushed.isNone)
    "Consume/completion retagged the old packet or lost the new epoch"
  ensure (HostResultBuffer.uartOutcome fresh.packet == .byte 0xa5 && fresh.packet.outcome == 5)
    "Independent completion packet did not retain the UART samples"
  let clearing := {full with result := {full.result with controlSecond := 2}}
  let drop := HostResultBuffer.Retained.step clearing.mailbox (mailboxCommand cfg pins clearing)
  ensure (drop.receipt.dropped == some fresh && drop.state.pending == some old && drop.state.overrun)
    "Clear/drop replaced the unknown old packet or cleared fresh overrun"
  let stopped := offer full 6 0
  let reset := offer full 7 0
  ensure ((policy cfg stopped).effective.command == 7 && !(policy cfg stopped).state.enabled &&
    (effective cfg reset).reset && !(policy cfg reset).state.enabled)
    "Delivered STOP/RESET did not abort and disarm"
  ensure (ownedReceipt cfg pins stopped == receipt && ownedReceipt cfg pins reset == receipt)
    "STOP/RESET suppressed the coincident old completion or consumer event"
  let flush := ownedReceipt cfg {pins with rstN := false} full
  ensure (flush.flushed == some old && flush.delivered.isNone && flush.accepted.isNone && flush.dropped.isNone)
    "External reset failed to dominate consume/completion"
  ensure ((policy cfg full).effective.command == 5)
    "Unread packet blocked quiet automatic rearm"
  let nonquiet := offer full 5 0
  ensure ((policy cfg nonquiet).effective.command == 6 && (policy cfg nonquiet).state.enabled &&
    !(UART.Rx.busy nonquiet.receiver || ((effective cfg nonquiet).command == 5)))
    "Nonquiet rearm delay was incorrectly admitted as continuous START"
  let commit : Loader.Machine.Inputs := {command := 3}
  ensure (reserved true commit && !reserved false commit &&
    !reserved true {commit with init := true})
    "Resident segment boundary excluded rejected COMMIT or admitted external init/replacement"

private def duplicateOrigins (firstCfg secondCfg : UART.Rx.Config) : IO Unit := do
  let raw := receiverPacket firstCfg (finished 0xa5)
  let first : OwnedPacket := ⟨raw, .uart 41 firstCfg⟩
  let second : OwnedPacket := ⟨raw, .uart 42 secondCfg⟩
  let trace := HostResultBuffer.Retained.run (⟨some first, false⟩ : Mailbox)
    [.cycle (some second) false true, .cycle (some second) true false, .reset]
  ensure (HostResultBuffer.Retained.dropped trace.receipts == [second] &&
    HostResultBuffer.Retained.delivered trace.receipts == [first] &&
    HostResultBuffer.Retained.flushed trace.receipts == [second] && trace.state.pending.isNone)
    "Equal raw packets lost their distinct epoch/config ownership"
  ensure ((trace.receipts.map eraseReceipt).map HostResultBuffer.Retained.Receipt.delivered ==
    [none, some raw, none]) "Erasing ownership changed physical delivery"

private def reloadOrigins (firstCfg secondCfg : UART.Rx.Config) : IO Unit := do
  let raw := receiverPacket firstCfg (finished 0xa5)
  let old : OwnedPacket := ⟨raw, .uart 41 firstCfg⟩
  let previous := state UART.Rx.reset ⟨some old, true⟩ 2 41
  let actual : Storage.PairedStreamPackage.State Unit :=
    ⟨⟨previous.storage.registers, ()⟩, false, previous.adapters, previous.result⟩
  let installed : Storage.PairedStreamOwnership.Tracked := ⟨previous.storage, false⟩
  let rebased := Storage.PairedStreamLifecycle.rebase secondCfg actual installed 42 previous.mailbox
  ensure (rebased.mailbox == previous.mailbox && rebased.epoch == 42 &&
    rebased.receiver == UART.Rx.reset && !rebased.enabled && rebased.result == actual.result)
    "Installing a new certified epoch relabeled or discarded the pending old packet"
  let clear := ownedReceipt secondCfg {} rebased
  ensure (clear.accepted.isNone && clear.dropped.isNone && clear.delivered.isNone &&
    (HostResultBuffer.Retained.step rebased.mailbox (mailboxCommand secondCfg {} rebased)).state.pending == some old)
    "Dormant clear minted an arrival or changed the old pending packet"
  let completing := {rebased with receiver := finished 0xa5, active := true, result := {rebased.result with controlSecond := 3}}
  let fresh : OwnedPacket := ⟨receiverPacket secondCfg completing.receiver, .uart 42 secondCfg⟩
  let delivered := ownedReceipt secondCfg {} completing
  ensure (delivered.delivered == some old && delivered.accepted == some fresh &&
    old.packet == fresh.packet && old.origin != fresh.origin)
    "A new completion confused equal payloads from the old and new epochs"
  let clearingHost := previous.result
  let takingHost := {previous.result with controlSecond := 3, clearPrev := true}
  let silent : List (HostResultBuffer.Retained.Command OwnedPacket) :=
    [Storage.PairedStreamDormant.silentCommand {} clearingHost,
      Storage.PairedStreamDormant.silentCommand {} takingHost,
      Storage.PairedStreamDormant.silentCommand {rstN := false} takingHost]
  let trace := HostResultBuffer.Retained.run previous.mailbox silent
  ensure (HostResultBuffer.Retained.arrivals silent == [] &&
    HostResultBuffer.Retained.accepted trace.receipts == [] &&
    HostResultBuffer.Retained.dropped trace.receipts == [] &&
    HostResultBuffer.Retained.retired trace.receipts == [old] && trace.state.pending.isNone)
    "Reload observer controls minted, duplicated or retagged an old occurrence"

private def samplerDelay (cfg : UART.Rx.Config) : IO Unit := do
  let initial := state UART.Rx.reset {} 0 0
  let stages : Chip.State := {first := {incoming := 1}, second := {incoming := 0}}
  let initial := {initial with adapters := stages}
  let incoming (n : Nat) : Chip.Pins := {uioIn := if n % 3 == 0 then 1 else 0}
  let mut stages := initial.adapters
  for n in [1:10] do
    let expected := match n with
      | 0 | 1 => initial.adapters.second.incoming.getLsbD cfg.input.val
      | 2 => initial.adapters.first.incoming.getLsbD cfg.input.val
      | k + 3 => (incoming (k + 1)).uioIn.getLsbD cfg.input.val
    ensure ((Storage.PairedPackage.decoded stages).incoming.getLsbD cfg.input.val == expected)
      s!"Receiver line lost the initial sampler stages or two-edge delay at {n}"
    stages := Storage.PairedPackage.adaptersNext (incoming n) stages

def main : IO Unit := do
  let firstCfg ← config 8
  let secondCfg ← config 16
  boundaries firstCfg
  duplicateOrigins firstCfg secondCfg
  reloadOrigins firstCfg secondCfg
  samplerDelay firstCfg
  IO.println "Paired UART session: packet origins, duplicate occurrences, consume/completion, clear/drop, STOP/reset completion, external flush, epoch rebase, dormant reload controls and two-edge sampler prefix passed."

#print axioms owned_arrival_origin
#print axioms receipts_agree
#print axioms ownership_order
#print axioms ownership_accounting
#print axioms retained_initialized_session
#print axioms Storage.PairedStreamLifecycle.qualified_reload
#print axioms Storage.PairedStreamLifecycle.stop_dormant
#print axioms Storage.PairedStreamOrigin.no_minted
#print axioms Storage.PairedStreamOrigin.no_arrival_order
#print axioms Storage.PairedStreamOrigin.no_arrival_accounting
#print axioms Storage.PairedStreamOrigin.actualReceipts_append
#print axioms Storage.PairedStreamOrigin.ownedReceipts_append
#print axioms Storage.PairedStreamOrigin.dormant_receipt_order
#print axioms Storage.PairedStreamOrigin.rebase_mailbox
#print axioms Storage.PairedStreamOrigin.rebased_arrival_origin
#print axioms logical_runN
#print axioms line_delayed
#print axioms quiet_wire_receive_series
#print axioms idle_wire_receive_series
#print axioms Storage.PairedStreamProgram.restart_receipts
#print axioms Storage.PairedStreamProgram.Replacement.correct
#print axioms Storage.PairedStreamProgram.Replacement.receipts_agree
#print axioms Storage.PairedStreamProgram.Path.correct
#print axioms Storage.PairedStreamProgram.initialized_lifecycle
#print axioms Storage.PairedStreamProgram.initialized_lifecycle_prefix
#print axioms Storage.PairedStreamProgram.retained_initialized_lifecycle
