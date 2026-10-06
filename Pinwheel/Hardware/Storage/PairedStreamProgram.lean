import Pinwheel.Hardware.Storage.PairedStreamOrigin

/-! Finite UART lifecycles, including the loader and external-reset boundaries.
Each installed receiver relation is derived from the delivered certified upload;
no execution correspondence is supplied again at a later epoch. -/
namespace Pinwheel.Hardware.Storage.PairedStreamProgram
open Pinwheel.Hardware
open PairedStreamSession (ReferenceState Mailbox Receipt OwnedPacket Origin eraseReceipt)
open PairedStreamLifecycle (Restart)
set_option backward.isDefEq.respectTransparency false
variable {S : Type} {memory : Memory.SinglePort.Contract S 9 64}
  {oldCfg cfg : UART.Rx.Config} {image oldImage : PairedImage.Image}
  {actual : PairedStreamPackage.State S} {s : ReferenceState}

theorem run_append (component : Timed.Component I T O) (s : T) (first second : List I) :
    component.run s (first ++ second) = component.run (component.run s first) second := by
  induction first generalizing s with
  | nil => rfl
  | cons input rest ih => exact ih (component.step input s)
  done

/-- A replacement starts with the actually decoded STOP. Serial settling and
the certified upload are external delivery boundaries, not execution premises. -/
structure Replacement (memory : Memory.SinglePort.Contract S 9 64)
    (oldCfg cfg : UART.Rx.Config) (image : PairedImage.Image)
    (actual : PairedStreamPackage.State S) (s : ReferenceState) where
  certificate : PairedImage.Corresponds (Compile.UARTRx.program cfg) image
  stop : Chip.Pins
  noInit : (PairedPackage.decoded s.adapters).init = false
  command : (PairedPackage.decoded s.adapters).command = 6
  data : (PairedPackage.decoded s.adapters).data = 0
  count : ((PairedStreamPackage.interpreted memory).step stop actual).adapters.receiver.count = 0
  fire : ((PairedStreamPackage.interpreted memory).step stop actual).adapters.receiver.fire = false
  first : Serial.Idle ((PairedStreamPackage.interpreted memory).step stop actual).adapters.first
  second : Serial.Idle ((PairedStreamPackage.interpreted memory).step stop actual).adapters.second
  beginData : BitVec 64
  commitData : BitVec 64
  upload : List Chip.Pins
  drainFirst : Chip.Pins
  drainSecond : Chip.Pins
  delivery : Serial.Session (upload.map Chip.wired)
    (Loader.Machine.uploadCommands (PairedImage.upload image) beginData commitData)
  epoch : Nat
  fresh : s.epoch < epoch

def Replacement.loadPins (r : Replacement memory oldCfg cfg image actual s) : List Chip.Pins :=
  r.upload ++ [r.drainFirst, r.drainSecond]

def Replacement.pins (r : Replacement memory oldCfg cfg image actual s) : List Chip.Pins :=
  r.stop :: r.loadPins

def Replacement.stoppedActual (r : Replacement memory oldCfg cfg image actual s) :
    PairedStreamPackage.State S := (PairedStreamPackage.interpreted memory).step r.stop actual

def Replacement.stoppedReference (r : Replacement memory oldCfg cfg image actual s) : ReferenceState :=
  (PairedStreamSession.reference oldCfg).step r.stop s

def Replacement.after (r : Replacement memory oldCfg cfg image actual s) : PairedStreamPackage.State S :=
  (PairedStreamPackage.interpreted memory).run r.stoppedActual r.loadPins

def Replacement.reference (r : Replacement memory oldCfg cfg image actual s) : ReferenceState :=
  PairedStreamLifecycle.rebase cfg r.after
    (PairedStreamBootstrap.run (PairedStreamSession.tracked r.stoppedReference)
      (Chip.consumed r.stoppedActual.adapters r.loadPins)) r.epoch
    (HostResultBuffer.Retained.run r.stoppedReference.mailbox
      (PairedStreamDormant.controls memory r.stoppedActual r.loadPins)).state

def Replacement.trace (r : Replacement memory oldCfg cfg image actual s) :
    List (Values Chip.Output × Values Chip.Output) :=
  (PairedStreamSession.reference oldCfg).edge r.stop s ::
    (PairedStreamPackage.interpreted memory).trace r.stoppedActual r.loadPins

def Replacement.receipts (r : Replacement memory oldCfg cfg image actual s) : List Receipt :=
  PairedStreamSession.ownedReceipt oldCfg r.stop s ::
    (HostResultBuffer.Retained.run r.stoppedReference.mailbox
      (PairedStreamDormant.controls memory r.stoppedActual r.loadPins)).receipts

theorem Replacement.stopped_related (r : Replacement memory oldCfg cfg image actual s)
    (h : PairedStreamSession.Related oldCfg oldImage memory actual s) :
    PairedStreamSession.Related oldCfg oldImage memory r.stoppedActual r.stoppedReference := by
  exact PairedStreamSession.related_next oldCfg oldImage memory actual s h r.stop
    (PairedStreamSession.effective_rule oldCfg oldImage s h.certified
      ⟨r.noInit, Or.inl (by simp [r.command])⟩)
  done

theorem trace_append (component : Timed.Component I T O) (s : T) (first second : List I) :
    component.trace s (first ++ second) = component.trace s first ++
      component.trace (component.run s first) second := by
  induction first generalizing s with
  | nil => rfl
  | cons input rest ih =>
    simp only [List.cons_append, Timed.Component.trace, Timed.Component.run, ih, List.cons_append]
    done
  done

def restartPins (restart : Restart cfg image) : List Chip.Pins :=
  [restart.reset, restart.reset, restart.reset, restart.idle, restart.idle] ++
    (restart.upload ++ [restart.drainFirst, restart.drainSecond])

def restartReceipts (restart : Restart cfg image) (mailbox : Mailbox) : List Receipt :=
  {flushed := mailbox.pending} :: List.replicate (4 + restart.upload.length + 2) {}

theorem restart_run (restart : Restart cfg image) (memory : Memory.SinglePort.Contract S 9 64)
    (actual : PairedStreamPackage.State S) :
    (PairedStreamPackage.interpreted memory).run actual (restartPins restart) =
      restart.after memory actual := by
  exact run_append _ _ _ _
  done

theorem restart_receipts (restart : Restart cfg image) (memory : Memory.SinglePort.Contract S 9 64)
    (actual : PairedStreamPackage.State S) (mailbox : Mailbox)
    (erased : PairedStreamSession.erase mailbox = HostResultBuffer.project actual.result) :
    PairedStreamSession.actualReceipts memory actual (restartPins restart) =
      (restartReceipts restart mailbox).map eraseReceipt := by
  obtain ⟨storage, physical, stopped, disabled, count, fire, first, second⟩ :=
    PairedStreamBootstrap.reset_prepares memory actual restart.reset restart.idle
      restart.resetLow restart.idleReleased restart.idleSerial
  have dormant : PairedStreamDormant.Dormant memory (restart.prepared memory actual) storage :=
    ⟨physical, disabled, (congrArg
      (fun pair : Values PairedController.Register × Memory.Sram.State 9 64 => pair.1 .mode)
      physical.1).symm.trans
      (PairedStreamMailboxInit.reset_mode memory actual restart.reset restart.idle restart.resetLow)⟩
  have delivered := Chip.session_delivers _ count fire first second restart.upload
    restart.drainFirst restart.drainSecond _ restart.delivery
  have empty := PairedStreamLifecycle.empty_receipts memory _ storage dormant
    (PairedStreamMailboxInit.reset_empty memory actual restart.reset restart.idle
      restart.resetLow restart.idleReleased) _
    (PairedStreamDormant.upload_history image restart.beginData restart.commitData _ delivered)
  rw [restartPins, PairedStreamOrigin.actualReceipts_append,
    PairedStreamLifecycle.reset_flush_receipts memory actual restart.reset restart.idle
      restart.resetLow restart.idleReleased]
  simp only [Restart.prepared] at empty
  rw [empty]
  simp [restartReceipts, eraseReceipt, ← erased, PairedStreamSession.erase,
    ← List.replicate_append_replicate]
  done

theorem Replacement.correct (r : Replacement memory oldCfg cfg image actual s)
    (h : PairedStreamSession.Related oldCfg oldImage memory actual s) :
    PairedStreamSession.Related cfg image memory r.after r.reference := by
  have stop := PairedStreamSession.stop_transition oldCfg s r.stop r.command r.data
  exact PairedStreamLifecycle.reload_related oldCfg cfg oldImage image r.certificate memory
    r.stoppedActual r.stoppedReference (r.stopped_related h) stop.2.1 stop.1
    r.count r.fire r.first r.second r.beginData r.commitData r.upload
    r.drainFirst r.drainSecond r.delivery r.epoch
  done

theorem Replacement.trace_agrees (r : Replacement memory oldCfg cfg image actual s)
    (h : PairedStreamSession.Related oldCfg oldImage memory actual s) :
    (PairedStreamPackage.interpreted memory).trace actual r.pins = r.trace := by
  exact congrArg (fun edge => edge ::
    (PairedStreamPackage.interpreted memory).trace r.stoppedActual r.loadPins)
    (Prod.ext (PairedStreamSession.observe_agrees oldCfg oldImage memory actual s h r.stop)
      (PairedStreamSession.observe_agrees oldCfg oldImage memory _ _ (r.stopped_related h) r.stop))
  done

theorem Replacement.receipts_agree (r : Replacement memory oldCfg cfg image actual s)
    (h : PairedStreamSession.Related oldCfg oldImage memory actual s) :
    PairedStreamSession.actualReceipts memory actual r.pins = r.receipts.map eraseReceipt := by
  have dormant := PairedStreamLifecycle.stop_dormant oldCfg oldImage memory actual s h
    r.stop r.noInit r.command r.data
  have delivered := Chip.session_delivers _ r.count r.fire r.first r.second r.upload
    r.drainFirst r.drainSecond _ r.delivery
  have owned := PairedStreamLifecycle.silent_run memory r.stoppedActual
    (PairedStreamSession.tracked r.stoppedReference) dormant r.stoppedReference.mailbox
    (by simpa only [(r.stopped_related h).result] using (r.stopped_related h).certified.mailbox)
    r.loadPins (PairedStreamDormant.upload_history image r.beginData r.commitData _ delivered)
  simpa only [Replacement.pins, Replacement.stoppedActual,
    PairedStreamSession.actualReceipts, Replacement.receipts,
    List.map_cons, PairedStreamSession.receipt_agrees oldCfg oldImage memory actual s h r.stop] using
    congrArg (List.cons (eraseReceipt (PairedStreamSession.ownedReceipt oldCfg r.stop s))) owned.2
  done

/-- A finite delivery domain. Resident command admission is checked against
the independent reference. Replacement derives its dormant boundary from STOP;
external reset always enters a fresh, certified initialization episode. -/
inductive Path (memory : Memory.SinglePort.Contract S 9 64) :
    UART.Rx.Config → PairedImage.Image → PairedStreamPackage.State S → ReferenceState → Type where
  | done {cfg : UART.Rx.Config} {image : PairedImage.Image}
      {actual : PairedStreamPackage.State S} {s : ReferenceState} : Path memory cfg image actual s
  | resident {cfg : UART.Rx.Config} {image : PairedImage.Image}
      {actual : PairedStreamPackage.State S} {s : ReferenceState}
      (pins : List Chip.Pins) (admissible : PairedStreamSession.Admissible cfg s pins)
      (next : Path memory cfg image ((PairedStreamPackage.interpreted memory).run actual pins)
        ((PairedStreamSession.reference cfg).run s pins)) : Path memory cfg image actual s
  | replace {cfg nextCfg : UART.Rx.Config} {image nextImage : PairedImage.Image}
      {actual : PairedStreamPackage.State S} {s : ReferenceState}
      (replacement : Replacement memory cfg nextCfg nextImage actual s)
      (next : Path memory nextCfg nextImage replacement.after replacement.reference) :
      Path memory cfg image actual s
  | restart {cfg nextCfg : UART.Rx.Config} {image nextImage : PairedImage.Image}
      {actual : PairedStreamPackage.State S} {s : ReferenceState}
      (restart : Restart nextCfg nextImage) (epoch : Nat)
      (fresh : s.epoch < epoch)
      (next : Path memory nextCfg nextImage (restart.after memory actual)
        (restart.reference memory actual epoch)) : Path memory cfg image actual s

noncomputable def Path.pins {cfg : UART.Rx.Config} {image : PairedImage.Image}
    {actual : PairedStreamPackage.State S} {s : ReferenceState}
    (path : Path memory cfg image actual s) : List Chip.Pins :=
  match path with
  | .done => []
  | .resident inputs _ next => inputs ++ next.pins
  | .replace replacement next => replacement.pins ++ next.pins
  | .restart boot _ _ next => restartPins boot ++ next.pins

/-- Only the resident portions use the UART interpretation. Reset and loader
observations retain the generic package reference on their original edges. -/
noncomputable def Path.trace {cfg : UART.Rx.Config} {image : PairedImage.Image}
    {actual : PairedStreamPackage.State S} {s : ReferenceState}
    (path : Path memory cfg image actual s) :
    List (Values Chip.Output × Values Chip.Output) :=
  match path with
  | .done => []
  | .resident pins _ next => (PairedStreamSession.reference cfg).trace s pins ++ next.trace
  | .replace replacement next => replacement.trace ++ next.trace
  | .restart boot _ _ next =>
      (PairedStreamPackage.interpreted memory).trace actual (restartPins boot) ++ next.trace

noncomputable def Path.receipts {cfg : UART.Rx.Config} {image : PairedImage.Image}
    {actual : PairedStreamPackage.State S} {s : ReferenceState}
    (path : Path memory cfg image actual s) : List Receipt :=
  match path with
  | .done => []
  | .resident pins _ next => PairedStreamSession.ownedReceipts cfg s pins ++ next.receipts
  | .replace replacement next => replacement.receipts ++ next.receipts
  | .restart boot _ _ next => restartReceipts boot s.mailbox ++ next.receipts

theorem Replacement.run (r : Replacement memory oldCfg cfg image actual s) :
    (PairedStreamPackage.interpreted memory).run actual r.pins = r.after := rfl

theorem Path.correct (path : Path memory cfg image actual s)
    (related : PairedStreamSession.Related cfg image memory actual s) :
    (PairedStreamPackage.interpreted memory).trace actual path.pins = path.trace ∧
      PairedStreamSession.actualReceipts memory actual path.pins = path.receipts.map eraseReceipt := by
  induction path with
  | done => exact ⟨rfl, rfl⟩
  | @resident cfg₀ image₀ before state₀ pins admissible next ih =>
    have tail := ih (PairedStreamSession.related_run cfg₀ image₀ memory before state₀ related pins admissible)
    simp only [Path.pins, Path.trace, Path.receipts, trace_append,
      PairedStreamOrigin.actualReceipts_append,
      PairedStreamSession.interpreted_trace cfg₀ image₀ memory before state₀ related pins admissible,
      PairedStreamSession.receipts_agree cfg₀ image₀ memory before state₀ related pins admissible,
      tail.1, tail.2, List.map_append, and_self]
    done
  | replace replacement next ih =>
    have tail := ih (replacement.correct related)
    simp only [Path.pins, Path.trace, Path.receipts, trace_append,
      PairedStreamOrigin.actualReceipts_append, replacement.run,
      replacement.trace_agrees related, replacement.receipts_agree related,
      tail.1, tail.2, List.map_append, and_self]
    done
  | @restart cfg₀ nextCfg image₀ nextImage before state₀ boot epoch fresh next ih =>
    have tail := ih (boot.correct memory before epoch)
    have receipts := restart_receipts boot memory before state₀.mailbox
      (by simpa only [related.result] using related.certified.mailbox)
    simp only [Path.pins, Path.trace, Path.receipts, trace_append,
      PairedStreamOrigin.actualReceipts_append, restart_run, receipts,
      tail.1, tail.2, List.map_append, and_self]
    done
  done

/-- Arbitrary represented power-up packets receive no UART interpretation. -/
def initialMailbox (actual : PairedStreamPackage.State S) : Mailbox :=
  ⟨(HostResultBuffer.project actual.result).pending.map (fun packet => ⟨packet, .unknown⟩),
    actual.result.overrun⟩

theorem erase_initialMailbox (actual : PairedStreamPackage.State S) :
    PairedStreamSession.erase (initialMailbox actual) = HostResultBuffer.project actual.result := by
  simp [initialMailbox, PairedStreamSession.erase, HostResultBuffer.project]
  done

/-- One actual reset/upload establishes the first relation. Every subsequent
relation is derived by the finite path, including certified reloads and resets. -/
theorem initialized_lifecycle (restart : Restart cfg image)
    (memory : Memory.SinglePort.Contract S 9 64) (initial : PairedStreamPackage.State S) (epoch : Nat)
    (path : Path memory cfg image (restart.after memory initial) (restart.reference memory initial epoch)) :
    (PairedStreamPackage.interpreted memory).trace initial (restartPins restart ++ path.pins) =
      (PairedStreamPackage.interpreted memory).trace initial (restartPins restart) ++ path.trace ∧
      PairedStreamSession.actualReceipts memory initial (restartPins restart ++ path.pins) =
        (restartReceipts restart (initialMailbox initial) ++ path.receipts).map eraseReceipt := by
  have tail := path.correct (restart.correct memory initial epoch)
  simp only [trace_append, PairedStreamOrigin.actualReceipts_append, restart_run,
    restart_receipts restart memory initial (initialMailbox initial) (erase_initialMailbox initial),
    tail.1, tail.2, List.map_append, and_self]
  done

theorem trace_take (component : Timed.Component I T O) (s : T) (pins : List I) (n : Nat) :
    component.trace s (pins.take n) = (component.trace s pins).take n := by
  induction n generalizing s pins with
  | zero => rfl
  | succ n ih =>
    cases pins with
    | nil => rfl
    | cons pin rest =>
      exact congrArg (List.cons (component.edge pin s)) (ih (component.step pin s) rest)
  done

theorem actualReceipts_take (memory : Memory.SinglePort.Contract S 9 64)
    (actual : PairedStreamPackage.State S) (pins : List Chip.Pins) (n : Nat) :
    PairedStreamSession.actualReceipts memory actual (pins.take n) =
      (PairedStreamSession.actualReceipts memory actual pins).take n := by
  induction n generalizing actual pins with
  | zero => rfl
  | succ n ih =>
    cases pins with
    | nil => rfl
    | cons pin rest =>
      exact congrArg (List.cons (HostResultBuffer.receipt pin
        (PairedStreamPackage.coreOutput memory actual) actual.result))
        (ih ((PairedStreamPackage.interpreted memory).step pin actual) rest)
  done

/-- Every edge prefix is covered, including prefixes inside reset or upload.
The emitted circuit has the same complete pad observations; raw receipts are
the erasure of the exact occurrence history, with fresh epoch labels. -/
theorem retained_initialized_lifecycle (restart : Restart cfg image)
    (memory : Memory.SinglePort.Contract S 9 64) (initial : PairedStreamPackage.State S) (epoch : Nat)
    (path : Path memory cfg image (restart.after memory initial) (restart.reference memory initial epoch))
    (n : Netlist PairedStream.Register PairedStream.Output PairedStream.Input)
    (hn : PairedStream.core = .ok n) (edges : Nat) :
    (PairedStreamPackage.executable (PairedStream.package n).component memory).trace initial.physical
        ((restartPins restart ++ path.pins).take edges) =
      ((PairedStreamPackage.interpreted memory).trace initial (restartPins restart) ++ path.trace).take edges ∧
      PairedStreamSession.actualReceipts memory initial ((restartPins restart ++ path.pins).take edges) =
        ((restartReceipts restart (initialMailbox initial) ++ path.receipts).take edges).map eraseReceipt := by
  have all := initialized_lifecycle restart memory initial epoch path
  simp only [PairedStreamPackage.retained_trace n hn, trace_take, actualReceipts_take,
    all.1, all.2, List.map_take, and_self]
  done

theorem initialized_lifecycle_prefix (restart : Restart cfg image)
    (memory : Memory.SinglePort.Contract S 9 64) (initial : PairedStreamPackage.State S) (epoch : Nat)
    (path : Path memory cfg image (restart.after memory initial) (restart.reference memory initial epoch))
    (edges : Nat) :
    (PairedStreamPackage.interpreted memory).trace initial ((restartPins restart ++ path.pins).take edges) =
      ((PairedStreamPackage.interpreted memory).trace initial (restartPins restart) ++ path.trace).take edges ∧
      PairedStreamSession.actualReceipts memory initial ((restartPins restart ++ path.pins).take edges) =
        ((restartReceipts restart (initialMailbox initial) ++ path.receipts).take edges).map eraseReceipt := by
  have all := initialized_lifecycle restart memory initial epoch path
  simp only [trace_take, actualReceipts_take, all.1, all.2, List.map_take, and_self]
  done

end Pinwheel.Hardware.Storage.PairedStreamProgram
