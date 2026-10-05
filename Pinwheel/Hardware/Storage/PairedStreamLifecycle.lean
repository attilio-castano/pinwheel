import Pinwheel.Hardware.Storage.PairedStreamSession
import Pinwheel.Hardware.Storage.PairedStreamDormant
import Pinwheel.Hardware.Storage.PairedStreamMailboxInit

/-! Certified replacement boundaries retain the old packet's origin. Loader
delivery cannot manufacture an execution arrival while the engine is dormant;
the real observer controls retire or flush old occurrences as usual. -/
namespace Pinwheel.Hardware.Storage.PairedStreamLifecycle
open Pinwheel.Hardware
open PairedStreamSession (Mailbox Receipt Origin OwnedPacket erase eraseReceipt eraseCommand)
open PairedStreamDormant (Dormant LoaderHistory silentCommand controls)
set_option backward.isDefEq.respectTransparency false

theorem erase_silent (pins : Chip.Pins) (host : HostResult.State) :
    eraseCommand (silentCommand pins host : HostResultBuffer.Retained.Command OwnedPacket) =
      (silentCommand pins host : HostResultBuffer.Retained.Command HostResultBuffer.Packet) := by
  simp only [silentCommand]
  split <;> rfl
  done

theorem silent_state (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) (storage : PairedStreamOwnership.Tracked)
    (h : Dormant memory s storage) (mailbox : Mailbox)
    (hm : erase mailbox = HostResultBuffer.project s.result) (pins : Chip.Pins) :
    erase (HostResultBuffer.Retained.step mailbox (silentCommand pins s.result)).state =
      HostResultBuffer.project ((PairedStreamPackage.interpreted memory).step pins s).result := by
  have erased := congrArg HostResultBuffer.Retained.Transition.state
    (PairedStreamSession.erase_step mailbox (silentCommand pins s.result))
  simpa only [erase_silent, hm, ← PairedStreamDormant.dormant_command memory s storage h pins,
    ← HostResultBuffer.next_refines, PairedStreamPackage.interpreted] using erased
  done

theorem silent_receipt (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) (storage : PairedStreamOwnership.Tracked)
    (h : Dormant memory s storage) (mailbox : Mailbox)
    (hm : erase mailbox = HostResultBuffer.project s.result) (pins : Chip.Pins) :
    eraseReceipt (HostResultBuffer.Retained.step mailbox (silentCommand pins s.result)).receipt =
      HostResultBuffer.receipt pins (PairedStreamPackage.coreOutput memory s) s.result := by
  have erased := congrArg HostResultBuffer.Retained.Transition.receipt
    (PairedStreamSession.erase_step mailbox (silentCommand pins s.result))
  simpa only [erase_silent, hm, ← PairedStreamDormant.dormant_command memory s storage h pins,
    HostResultBuffer.receipt] using erased
  done

theorem silent_run (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) (storage : PairedStreamOwnership.Tracked)
    (h : Dormant memory s storage) (mailbox : Mailbox)
    (hm : erase mailbox = HostResultBuffer.project s.result) (pins : List Chip.Pins)
    (commands : LoaderHistory (Chip.consumed s.adapters pins)) :
    erase (HostResultBuffer.Retained.run mailbox (controls memory s pins)).state =
      HostResultBuffer.project ((PairedStreamPackage.interpreted memory).run s pins).result ∧
    PairedStreamSession.actualReceipts memory s pins =
      (HostResultBuffer.Retained.run mailbox (controls memory s pins)).receipts.map eraseReceipt := by
  induction pins generalizing s storage mailbox with
  | nil => exact ⟨hm, rfl⟩
  | cons i rest ih =>
    simp only [PairedHost.consumed_cons, LoaderHistory, List.forall_mem_cons] at commands
    have next := ih ((PairedStreamPackage.interpreted memory).step i s)
      (PairedStreamOwnership.advance storage (PairedStreamPackage.rawInput s))
      (PairedStreamDormant.dormant_next memory s storage h i commands.1.1 commands.1.2)
      (HostResultBuffer.Retained.step mailbox (silentCommand i s.result)).state
      (silent_state memory s storage h mailbox hm i) commands.2
    simp only [controls, HostResultBuffer.Retained.run, Timed.Component.run,
      PairedStreamSession.actualReceipts, List.map_cons,
      silent_receipt memory s storage h mailbox hm i, next.1, next.2]
    trivial
    done
  done

def rebase (cfg : UART.Rx.Config) (actual : PairedStreamPackage.State S)
    (storage : PairedStreamOwnership.Tracked) (epoch : Nat) (mailbox : Mailbox) :
    PairedStreamSession.ReferenceState :=
  {PairedStreamSession.initialReference cfg actual storage epoch with mailbox := mailbox}

theorem rebase_related (cfg : UART.Rx.Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (storage : PairedStreamOwnership.Tracked) (physical : PairedStreamBootstrap.Related memory actual storage)
    (execution : PairedTimed.Related (Compile.UARTRx.program cfg) image storage.inner
      (Engine.Reactive.reset (Compile.UARTRx.program cfg)))
    (epoch : Nat) (mailbox : Mailbox) (hm : erase mailbox = HostResultBuffer.project actual.result) :
    PairedStreamSession.Related cfg image memory actual (rebase cfg actual storage epoch mailbox) := by
  have seed := PairedStreamSession.initial_related cfg image memory actual storage physical execution epoch
  exact ⟨seed.storage, seed.enabled, seed.adapters, seed.result,
    ⟨seed.certified.execution, seed.certified.wellFormed, hm, seed.certified.active⟩⟩

theorem qualified_reload (cfg : UART.Rx.Config) (image : PairedImage.Image)
    (cert : PairedImage.Corresponds (Compile.UARTRx.program cfg) image)
    (memory : Memory.SinglePort.Contract S 9 64) (s : PairedStreamPackage.State S)
    (storage : PairedStreamOwnership.Tracked) (dormant : Dormant memory s storage)
    (invariant : PairedRuntime.Invariant storage.inner)
    (mailbox : Mailbox) (hm : erase mailbox = HostResultBuffer.project s.result)
    (count : s.adapters.receiver.count = 0) (fire : s.adapters.receiver.fire = false)
    (first : Serial.Idle s.adapters.first) (second : Serial.Idle s.adapters.second)
    (d₀ d₁ : BitVec 64) (pins : List Chip.Pins) (a b : Chip.Pins)
    (delivery : Serial.Session (pins.map Chip.wired)
      (Loader.Machine.uploadCommands (PairedImage.upload image) d₀ d₁)) (epoch : Nat) :
    let after := (PairedStreamPackage.interpreted memory).run s (pins ++ [a, b])
    let packets := HostResultBuffer.Retained.run mailbox (controls memory s (pins ++ [a, b]))
    ∃ next : PairedStreamOwnership.Tracked,
      PairedStreamSession.Related cfg image memory after (rebase cfg after next epoch packets.state) ∧
      next.enabled = false ∧
      PairedStreamSession.actualReceipts memory s (pins ++ [a, b]) = packets.receipts.map eraseReceipt ∧
      HostResultBuffer.Retained.arrivals (controls memory s (pins ++ [a, b]) :
        List (HostResultBuffer.Retained.Command OwnedPacket)) = [] := by
  have delivered := Chip.session_delivers _ count fire first second pins a b _ delivery
  have inputs := PairedStreamDormant.upload_history image d₀ d₁ _ delivered
  have owned := silent_run memory s storage dormant mailbox hm (pins ++ [a, b]) inputs
  have stopped : PairedSession.Stopped storage.inner :=
    ⟨invariant, by simp [PairedRunning.Running, dormant.2.2]⟩
  obtain ⟨next, physical, execution, disabled⟩ :=
    PairedStreamBootstrap.qualified_upload (Compile.UARTRx.program cfg) image cert memory s storage
      dormant.1 stopped dormant.2.1 count fire first second d₀ d₁ pins a b delivery
  exact ⟨next, rebase_related cfg image memory _ next physical execution epoch _ owned.1,
    disabled, owned.2, PairedStreamDormant.controls_no_arrivals memory s _⟩
  done

/-- STOP creates the dormant reload boundary, including an old completion
arriving on that same edge. It is not a no-arrival mailbox reset. -/
theorem stop_dormant (cfg : UART.Rx.Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : PairedStreamSession.ReferenceState) (h : PairedStreamSession.Related cfg image memory actual s)
    (pins : Chip.Pins) (init : (PairedPackage.decoded s.adapters).init = false)
    (command : (PairedPackage.decoded s.adapters).command = 6)
    (data : (PairedPackage.decoded s.adapters).data = 0) :
    Dormant memory ((PairedStreamPackage.interpreted memory).step pins actual)
      (PairedStreamSession.tracked ((PairedStreamSession.reference cfg).step pins s)) := by
  have next := PairedStreamSession.related_next cfg image memory actual s h pins
    (PairedStreamSession.effective_rule cfg image s h.certified
      ⟨init, Or.inl (by simp [command])⟩)
  have stop := PairedStreamSession.stop_transition cfg s pins command data
  refine ⟨⟨next.storage, next.enabled⟩, stop.2.1, ?_⟩
  have mode := congrArg Reactive.State.mode next.certified.execution.2.2
  simpa only [PairedStreamSession.tracked, PairedEntry.view, stop.1,
    Compile.UARTRx.lift, Compile.UARTRx.liftControl, UART.Rx.reset, Reactive.embed,
    Reactive.stopMode] using mode
  done

theorem reset_flush_receipts (memory : Memory.SinglePort.Contract S 9 64)
    (initial : PairedStreamPackage.State S) (reset idle : Chip.Pins)
    (hr : reset.rstN = false) (hi : idle.rstN = true) :
    PairedStreamSession.actualReceipts memory initial [reset, reset, reset, idle, idle] =
      ({flushed := (HostResultBuffer.project initial.result).pending} ::
        List.replicate 4 ({} : HostResultBuffer.Retained.Receipt HostResultBuffer.Packet)) := by
  simp [PairedStreamSession.actualReceipts, PairedStreamPackage.interpreted,
    HostResultBuffer.receipt, HostResultBuffer.command, HostResultBuffer.Retained.step,
    HostResultBuffer.project, HostResult.next, HostResult.resetting, hr, hi]
  done

theorem dormant_of_ready (cfg : UART.Rx.Config) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : PairedStreamSession.ReferenceState) (h : PairedStreamSession.Related cfg image memory actual s)
    (disabled : s.enabled = false) (ready : s.receiver = UART.Rx.reset) :
    Dormant memory actual (PairedStreamSession.tracked s) := by
  refine ⟨⟨h.storage, h.enabled⟩, disabled, ?_⟩
  have mode := congrArg Reactive.State.mode h.certified.execution.2.2
  simpa only [PairedStreamSession.tracked, PairedEntry.view, ready,
    Compile.UARTRx.lift, Compile.UARTRx.liftControl, UART.Rx.reset, Reactive.embed,
    Reactive.stopMode] using mode
  done

theorem reload_related (oldCfg cfg : UART.Rx.Config) (oldImage image : PairedImage.Image)
    (cert : PairedImage.Corresponds (Compile.UARTRx.program cfg) image)
    (memory : Memory.SinglePort.Contract S 9 64) (actual : PairedStreamPackage.State S)
    (s : PairedStreamSession.ReferenceState)
    (h : PairedStreamSession.Related oldCfg oldImage memory actual s)
    (disabled : s.enabled = false) (ready : s.receiver = UART.Rx.reset)
    (count : actual.adapters.receiver.count = 0) (fire : actual.adapters.receiver.fire = false)
    (first : Serial.Idle actual.adapters.first) (second : Serial.Idle actual.adapters.second)
    (d₀ d₁ : BitVec 64) (pins : List Chip.Pins) (a b : Chip.Pins)
    (delivery : Serial.Session (pins.map Chip.wired)
      (Loader.Machine.uploadCommands (PairedImage.upload image) d₀ d₁)) (epoch : Nat) :
    let history := pins ++ [a, b]
    let after := (PairedStreamPackage.interpreted memory).run actual history
    let storage := PairedStreamBootstrap.run (PairedStreamSession.tracked s)
      (Chip.consumed actual.adapters history)
    let packets := HostResultBuffer.Retained.run s.mailbox (controls memory actual history)
    PairedStreamSession.Related cfg image memory after (rebase cfg after storage epoch packets.state) := by
  have dormant := dormant_of_ready oldCfg oldImage memory actual s h disabled ready
  have delivered := Chip.session_delivers _ count fire first second pins a b _ delivery
  have owned := silent_run memory actual (PairedStreamSession.tracked s) dormant s.mailbox
    (by simpa only [h.result] using h.certified.mailbox) (pins ++ [a, b])
    (PairedStreamDormant.upload_history image d₀ d₁ _ delivered)
  have stopped : PairedSession.Stopped s.storage :=
    ⟨h.certified.execution.1.invariant, by
      have mode : s.storage.registers .mode = 0 := dormant.2.2
      simp [PairedRunning.Running, mode]⟩
  have installed := PairedStreamOwnership.upload_admitted (Compile.UARTRx.program cfg) image cert d₀ d₁ _
    (PairedStreamSession.tracked s) stopped disabled delivered
  exact rebase_related cfg image memory _ _
    (PairedStreamBootstrap.run_storage memory actual (PairedStreamSession.tracked s) dormant.1 _)
    installed.1 epoch _ owned.1
  done

/-- The external delivery contract of an initialization/restart episode. -/
structure Restart (cfg : UART.Rx.Config) (image : PairedImage.Image) where
  certificate : PairedImage.Corresponds (Compile.UARTRx.program cfg) image
  reset : Chip.Pins
  idle : Chip.Pins
  resetLow : reset.rstN = false
  idleReleased : idle.rstN = true
  idleSerial : idle.uiIn.getLsbD 2 = true
  beginData : BitVec 64
  commitData : BitVec 64
  upload : List Chip.Pins
  drainFirst : Chip.Pins
  drainSecond : Chip.Pins
  delivery : Serial.Session (upload.map Chip.wired)
    (Loader.Machine.uploadCommands (PairedImage.upload image) beginData commitData)

def Restart.prepared (r : Restart cfg image) (memory : Memory.SinglePort.Contract S 9 64)
    (initial : PairedStreamPackage.State S) : PairedStreamPackage.State S :=
  (PairedStreamPackage.interpreted memory).run initial [r.reset, r.reset, r.reset, r.idle, r.idle]

def Restart.after (r : Restart cfg image) (memory : Memory.SinglePort.Contract S 9 64)
    (initial : PairedStreamPackage.State S) : PairedStreamPackage.State S :=
  (PairedStreamPackage.interpreted memory).run (r.prepared memory initial)
    (r.upload ++ [r.drainFirst, r.drainSecond])

noncomputable def Restart.storage (r : Restart cfg image) (memory : Memory.SinglePort.Contract S 9 64)
    (initial : PairedStreamPackage.State S) : PairedStreamOwnership.Tracked :=
  Classical.choose (PairedStreamMailboxInit.initialized_upload (Compile.UARTRx.program cfg)
    image r.certificate memory initial r.reset r.idle r.resetLow r.idleReleased r.idleSerial
    r.beginData r.commitData r.upload r.drainFirst r.drainSecond r.delivery)

noncomputable def Restart.reference (r : Restart cfg image) (memory : Memory.SinglePort.Contract S 9 64)
    (initial : PairedStreamPackage.State S) (epoch : Nat) : PairedStreamSession.ReferenceState :=
  rebase cfg (r.after memory initial) (r.storage memory initial) epoch {}

theorem Restart.storage_spec (r : Restart cfg image) (memory : Memory.SinglePort.Contract S 9 64)
    (initial : PairedStreamPackage.State S) :
    PairedStreamBootstrap.Related memory (r.after memory initial) (r.storage memory initial) ∧
      PairedTimed.Related (Compile.UARTRx.program cfg) image (r.storage memory initial).inner
        (Engine.Reactive.reset (Compile.UARTRx.program cfg)) ∧
      (r.storage memory initial).enabled = false ∧
      (r.storage memory initial).inner.registers .pending = 0 ∧
      PairedStreamMailboxInit.Empty (r.after memory initial).result := by
  exact Classical.choose_spec (PairedStreamMailboxInit.initialized_upload (Compile.UARTRx.program cfg)
    image r.certificate memory initial r.reset r.idle r.resetLow r.idleReleased r.idleSerial
    r.beginData r.commitData r.upload r.drainFirst r.drainSecond r.delivery)

theorem Restart.initialized (r : Restart cfg image) (memory : Memory.SinglePort.Contract S 9 64)
    (initial : PairedStreamPackage.State S) (epoch : Nat) :
    (r.reference memory initial epoch).enabled = false ∧
      (r.reference memory initial epoch).receiver = UART.Rx.reset ∧
      (r.reference memory initial epoch).storage.registers .pending = 0 ∧
      PairedStreamMailboxInit.Empty (r.after memory initial).result := by
  exact ⟨(r.storage_spec memory initial).2.2.1, rfl,
    (r.storage_spec memory initial).2.2.2.1, (r.storage_spec memory initial).2.2.2.2⟩

theorem Restart.correct (r : Restart cfg image) (memory : Memory.SinglePort.Contract S 9 64)
    (initial : PairedStreamPackage.State S) (epoch : Nat) :
    PairedStreamSession.Related cfg image memory (r.after memory initial) (r.reference memory initial epoch) := by
  have accepted := Classical.choose_spec (PairedStreamMailboxInit.initialized_upload (Compile.UARTRx.program cfg)
    image r.certificate memory initial r.reset r.idle r.resetLow r.idleReleased r.idleSerial
    r.beginData r.commitData r.upload r.drainFirst r.drainSecond r.delivery)
  exact rebase_related cfg image memory _ _ accepted.1 accepted.2.1 epoch {} accepted.2.2.2.2.1.symm

theorem empty_receipt (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) (storage : PairedStreamOwnership.Tracked)
    (h : Dormant memory s storage) (empty : PairedStreamMailboxInit.Empty s.result) (pins : Chip.Pins) :
    HostResultBuffer.receipt pins (PairedStreamPackage.coreOutput memory s) s.result = {} := by
  simp only [HostResultBuffer.receipt, PairedStreamDormant.dormant_command memory s storage h pins,
    empty.1, silentCommand]
  cases HostResult.resetting pins s.result <;>
    simp [HostResultBuffer.Retained.step]
  done

theorem empty_receipts (memory : Memory.SinglePort.Contract S 9 64)
    (s : PairedStreamPackage.State S) (storage : PairedStreamOwnership.Tracked)
    (h : Dormant memory s storage) (empty : PairedStreamMailboxInit.Empty s.result)
    (pins : List Chip.Pins) (commands : LoaderHistory (Chip.consumed s.adapters pins)) :
    PairedStreamSession.actualReceipts memory s pins =
      List.replicate pins.length ({} : HostResultBuffer.Retained.Receipt HostResultBuffer.Packet) := by
  induction pins generalizing s storage with
  | nil => rfl
  | cons i rest ih =>
    simp only [PairedHost.consumed_cons, LoaderHistory, List.forall_mem_cons] at commands
    have inactive := PairedStreamMailboxInit.dormant_inactive memory s storage h commands.1.1 commands.1.2
    have nextEmpty := PairedStreamMailboxInit.observer_empty_next i
      (PairedStreamPackage.coreOutput memory s) s.result empty inactive.1 inactive.2
    have tail := ih ((PairedStreamPackage.interpreted memory).step i s)
      (PairedStreamOwnership.advance storage (PairedStreamPackage.rawInput s))
      (PairedStreamDormant.dormant_next memory s storage h i commands.1.1 commands.1.2)
      nextEmpty commands.2
    simp only [PairedStreamSession.actualReceipts, empty_receipt memory s storage h empty i,
      tail, List.length_cons, List.replicate_succ]
    done
  done

end Pinwheel.Hardware.Storage.PairedStreamLifecycle
