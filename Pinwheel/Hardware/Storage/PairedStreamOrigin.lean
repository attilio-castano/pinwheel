import Pinwheel.Hardware.Storage.PairedStreamLifecycle

/-! Reload controls cannot mint packets. The exact old occurrence is retired
or retained, and rebasing changes only the epoch of later execution arrivals. -/
namespace Pinwheel.Hardware.Storage.PairedStreamOrigin
open Pinwheel.Hardware
open PairedStreamSession (OwnedPacket Mailbox Origin)
open HostResultBuffer

/-- Empty arrival history excludes both admissions and drops, for every
initial slot and every consume, clear or flush history. -/
theorem no_minted (mailbox : Retained.State α) (commands : List (Retained.Command α))
    (silent : Retained.arrivals commands = []) :
    Retained.accepted (Retained.run mailbox commands).receipts = [] ∧
      Retained.dropped (Retained.run mailbox commands).receipts = [] := by
  induction commands generalizing mailbox with
  | nil => simp [Retained.run, Retained.accepted, Retained.dropped]
  | cons command rest ih =>
    change command.arrival.toList ++ Retained.arrivals rest = [] at silent
    have empty := List.append_eq_nil_iff.mp silent
    have edge := Retained.step_partition mailbox command
    have head := List.append_eq_nil_iff.mp (edge.symm.trans empty.1)
    have tail := ih (Retained.step mailbox command).state empty.2
    simpa only [Retained.run, Retained.accepted_cons, Retained.dropped, List.flatMap_cons,
      head.1, head.2, List.nil_append] using tail
    done
  done

/-- Exact packet equality retains all origin data and occurrence order. -/
theorem no_arrival_order (mailbox : Retained.State α) (commands : List (Retained.Command α))
    (silent : Retained.arrivals commands = []) :
    mailbox.pending.toList = Retained.retired (Retained.run mailbox commands).receipts ++
      (Retained.run mailbox commands).state.pending.toList := by
  simpa only [(no_minted mailbox commands silent).1, List.append_nil] using
    Retained.run_order mailbox commands
  done

theorem no_arrival_accounting (mailbox : Retained.State α) (commands : List (Retained.Command α))
    (silent : Retained.arrivals commands = []) :
    mailbox.pending.toList.length =
      (Retained.delivered (Retained.run mailbox commands).receipts).length +
      (Retained.flushed (Retained.run mailbox commands).receipts).length +
      (Retained.run mailbox commands).state.pending.toList.length := by
  simpa only [silent, (no_minted mailbox commands silent).2, List.length_nil,
    Nat.add_zero] using Retained.run_accounting mailbox commands
  done

theorem actualReceipts_append (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) (first second : List Chip.Pins) :
    PairedStreamSession.actualReceipts memory s (first ++ second) =
      PairedStreamSession.actualReceipts memory s first ++
        PairedStreamSession.actualReceipts memory
          ((PairedStreamPackage.interpreted memory).run s first) second := by
  induction first generalizing s with
  | nil => rfl
  | cons pin rest ih =>
    simp only [List.cons_append, PairedStreamSession.actualReceipts,
      Timed.Component.run, ih, List.cons_append]
    done
  done

theorem ownedReceipts_append (cfg : UART.Rx.Config) (s : PairedStreamSession.ReferenceState)
    (first second : List Chip.Pins) :
    PairedStreamSession.ownedReceipts cfg s (first ++ second) =
      PairedStreamSession.ownedReceipts cfg s first ++
        PairedStreamSession.ownedReceipts cfg
          ((PairedStreamSession.reference cfg).run s first) second := by
  induction first generalizing s with
  | nil => rfl
  | cons pin rest ih =>
    simp only [List.cons_append, PairedStreamSession.ownedReceipts,
      Timed.Component.run, ih, List.cons_append]
    done
  done

/-- Actual dormant controls conserve the exact old slot. The relation is
required once at the boundary; preservation supplies the subsequent receipts. -/
theorem dormant_receipt_order (memory : Memory.SinglePort.Contract S 9 64)
    (actual : PairedStreamPackage.State S) (storage : PairedStreamOwnership.Tracked)
    (dormant : PairedStreamDormant.Dormant memory actual storage) (mailbox : Mailbox)
    (erased : PairedStreamSession.erase mailbox = HostResultBuffer.project actual.result)
    (pins : List Chip.Pins)
    (commands : PairedStreamDormant.LoaderHistory (Chip.consumed actual.adapters pins)) :
    let trace := Retained.run mailbox (PairedStreamDormant.controls memory actual pins)
    PairedStreamSession.actualReceipts memory actual pins =
      trace.receipts.map PairedStreamSession.eraseReceipt ∧
      Retained.accepted trace.receipts = [] ∧ Retained.dropped trace.receipts = [] ∧
      mailbox.pending.toList = Retained.retired trace.receipts ++ trace.state.pending.toList := by
  have silent := PairedStreamDormant.controls_no_arrivals (α := OwnedPacket) memory actual pins
  exact ⟨(PairedStreamLifecycle.silent_run memory actual storage dormant mailbox erased pins commands).2,
    (no_minted mailbox _ silent).1, (no_minted mailbox _ silent).2,
    no_arrival_order mailbox _ silent⟩
  done

theorem rebase_mailbox (cfg : UART.Rx.Config) (actual : PairedStreamPackage.State S)
    (storage : PairedStreamOwnership.Tracked) (epoch : Nat) (mailbox : Mailbox) :
    (PairedStreamLifecycle.rebase cfg actual storage epoch mailbox).mailbox = mailbox := rfl

theorem reference_epoch (cfg : UART.Rx.Config) (s : PairedStreamSession.ReferenceState)
    (pins : List Chip.Pins) :
    ((PairedStreamSession.reference cfg).run s pins).epoch = s.epoch := by
  induction pins generalizing s with
  | nil => rfl
  | cons pin rest ih =>
    exact ih ((PairedStreamSession.reference cfg).step pin s)
  done

/-- A later arrival uses the new configuration and epoch. This does not
reinterpret any packet retained by `rebase_mailbox`. -/
theorem rebased_arrival_origin (cfg : UART.Rx.Config) (actual : PairedStreamPackage.State S)
    (storage : PairedStreamOwnership.Tracked) (epoch : Nat) (mailbox : Mailbox)
    (pins : List Chip.Pins) (packet : OwnedPacket)
    (arrival : PairedStreamSession.ownedArrival cfg
      ((PairedStreamSession.reference cfg).run
        (PairedStreamLifecycle.rebase cfg actual storage epoch mailbox) pins) = some packet) :
    packet.origin = .uart epoch cfg ∧ packet.packet.outcome = 5 ∧
      HostResultBuffer.uartOutcome packet.packet = UART.Rx.outcome
        ((PairedStreamSession.reference cfg).run
          (PairedStreamLifecycle.rebase cfg actual storage epoch mailbox) pins).receiver.samples := by
  have origin := PairedStreamSession.owned_arrival_origin cfg _ packet arrival
  simpa only [reference_epoch, PairedStreamLifecycle.rebase, PairedStreamSession.initialReference] using
    (⟨origin.1, origin.2.1, origin.2.2.1⟩ : _ ∧ _ ∧ _)
  done

end Pinwheel.Hardware.Storage.PairedStreamOrigin
