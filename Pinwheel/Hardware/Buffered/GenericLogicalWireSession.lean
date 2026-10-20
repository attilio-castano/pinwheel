import Pinwheel.Hardware.Buffered.GenericLogicalWireDelivery

/-! Runtime wire events for any certified source program.  Initialization and
reset/reload are supplied by separate concrete loader proofs. -/
namespace Pinwheel.Hardware.Buffered.GenericLogicalWire
open Pinwheel.Hardware Pinwheel.Program Refinement Serial.Frames
open SerialSourceSession (Delivery Attempt Frontend)
variable {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}

inductive Event (p : Program.Buffered.Program) :
    SerialPackage.State → Cursor → Frontend → List SerialPackage.Pins →
      SerialPackage.State → Cursor → Frontend → Type where
  | padding (pins : List SerialPackage.Pins) (cursor : Cursor) (frontend : Frontend)
      (physical : SerialSourceSession.IdlePins pins) :
      Event (p := p) before cursor frontend pins (before.run pins) (cursor.advance (p := p) pins) frontend
  | start (delivery : Delivery before) (logical : Transfer.State) (offset : Nat)
      (opcode : delivery.request.word.extractLsb' 144 4 = 3#4)
      (starting : Reactive.starting.eval (delivery.framed.coreInputs delivery.dispatch)
        delivery.framed.controller.core = 1) :
      Event (p := p) before (.free logical offset) .available delivery.pins delivery.after
        (.owned (delivery.request.word.extractLsb' 0 32) (Delivery.localStarted (p := p) delivery logical) offset) .ready
  | administrative (delivery : Delivery before) (payload : BitVec 32)
      (source : Program.Buffered.State) (offset : Nat)
      (opcode : SerialSourceRequest.ExecutionOpcode delivery.request.word)
      (notRelease : Reactive.releasing.eval (delivery.framed.coreInputs delivery.dispatch)
        delivery.framed.controller.core = 0) :
      Event (p := p) before (.owned payload source offset) .available delivery.pins delivery.after
        (.owned payload (Delivery.localAdvanced (p := p) delivery source) offset) .ready
  | release (delivery : Delivery before) (payload : BitVec 32)
      (source : Program.Buffered.State) (offset : Nat)
      (opcode : delivery.request.word.extractLsb' 144 4 = 4#4)
      (valid : codeOf delivery.request.word = 0#4)
      (retained : delivery.framed.controller.core .retained = 1)
      (generation : delivery.request.word.extractLsb' 0 16 = delivery.framed.controller.core .generation)
      (transfer : delivery.request.word.extractLsb' 16 16 = delivery.framed.controller.core .transfer) :
      Event (p := p) before (.owned payload source offset) .available delivery.pins delivery.after
        (.free (Delivery.localReleased (p := p) delivery source) offset) .ready
  | read (attempt : Attempt before) (cursor : Cursor) (length : attempt.bits.length = 192) :
      Event (p := p) before cursor .ready attempt.pins attempt.after (cursor.advance (p := p) attempt.pins) .available
  | retry (attempt : Attempt before) (cursor : Cursor) (length : attempt.bits.length ≠ 192) :
      Event (p := p) before cursor .ready attempt.pins attempt.after (cursor.advance (p := p) attempt.pins) .ready
/-- Any finite sampled SCK/MOSI/raw history can pad either frontend boundary
by holding physical CS high and cold low. -/
def Event.deselected (samples : List SerialPackage.Pins) (cursor : Cursor) (frontend : Frontend) :
    Event (p := p) before cursor frontend (SerialSourceSession.deselected samples)
      (before.run (SerialSourceSession.deselected samples))
      (cursor.advance (p := p) (SerialSourceSession.deselected samples)) frontend :=
  .padding _ cursor frontend (SerialSourceSession.deselected_idle samples)

theorem Event.run_pins (event : Event (p := p) before cursor frontend pins after next nextFrontend) :
    before.run pins = after := by
  cases event with
  | padding => rfl
  | start delivery _ _ _ _ => exact delivery.run_pins
  | administrative delivery _ _ _ _ _ => exact delivery.run_pins
  | release delivery _ _ _ _ _ _ _ _ => exact delivery.run_pins
  | read => rfl
  | retry => rfl

theorem Event.preserves (event : Event (p := p) before cursor frontend pins after next nextFrontend)
    (initial : Valid (p := p) (layout := layout) before cursor frontend) : Valid (p := p) (layout := layout) after next nextFrontend := by
  cases event with
  | padding pins cursor frontend physical =>
    have idle := SerialSourceSession.Frontend.idle_run initial.1 pins physical
    exact ⟨idle.1, Cursor.quiet_run initial.2 pins idle.2.2⟩
  | start delivery logical offset opcode starting =>
    exact ⟨delivery.ready,Delivery.start_owned delivery logical offset initial.2.1 initial.2.2 opcode starting⟩
  | administrative delivery payload source offset opcode notRelease =>
    exact ⟨delivery.ready,Delivery.administrative_owned delivery payload source offset initial.2 opcode notRelease⟩
  | release delivery payload source offset opcode valid retained generation transfer =>
    exact ⟨delivery.ready,Delivery.release_free delivery payload source offset initial.2
      opcode valid retained generation transfer⟩
  | read attempt cursor length => exact ⟨(attempt.exact length).1,Cursor.quiet_run initial.2 _ attempt.quiet⟩
  | retry attempt cursor length => exact ⟨(attempt.retry length).1,Cursor.quiet_run initial.2 _ attempt.quiet⟩

def Event.Observed (event : Event (p := p) before cursor frontend pins after next nextFrontend) : Prop :=
  match event with
  | .padding pins _ _ _ =>
    (before.run pins).record.response = before.record.response ∧
      (∀ input ∈ before.commands pins, SpiCircuit.Quiet input) ∧
      (before.commands pins).length = pins.length
  | .start delivery logical offset _ _ =>
    SerialSourceReceipt.Meaning delivery.after.record.response delivery.delivered.record
      (Lifecycle.IdentityView.buffered offset
        (LogicalSession.started p delivery.framed.controller
          (delivery.framed.coreInputs delivery.dispatch) logical))
  | .administrative delivery _ source offset _ _ =>
    SerialSourceReceipt.Meaning delivery.after.record.response delivery.delivered.record
      (Lifecycle.IdentityView.buffered offset (Delivery.localDispatched (p := p) delivery source))
  | .release delivery _ source _ _ _ _ _ _ =>
    SerialSourceRelease.Receipt delivery.after.record.response delivery.request.word ∧
      (let current := SerialSourceRead.sourceRun p source delivery.request.pins
       ∃ e outcome, current.buffers.slot = .completed ⟨e,outcome⟩ ∧
         e.request.identity = current.owner ∧
         Transfer.step capacity current.buffers (.release current.owner) =
           ⟨Delivery.localReleased (p := p) delivery source,.released⟩)
  | .read attempt _ _ => attempt.ExactMeaning
  | .retry attempt _ _ => attempt.RetryMeaning

theorem Event.observed (event : Event (p := p) before cursor frontend pins after next nextFrontend)
    (initial : Valid (p := p) (layout := layout) before cursor frontend) : event.Observed := by
  cases event with
  | padding pins cursor frontend physical =>
    have idle := SerialSourceSession.Frontend.idle_run initial.1 pins physical
    exact ⟨idle.2.1, idle.2.2, before.commands_length pins⟩
  | start delivery logical offset opcode starting =>
    exact Delivery.start_receipt delivery logical offset initial.2.1 initial.2.2 opcode starting
  | administrative delivery payload source offset opcode notRelease =>
    exact Delivery.administrative_receipt delivery payload source offset initial.2 opcode notRelease
  | release delivery payload source offset opcode valid retained generation transfer =>
    exact Delivery.release_observed delivery payload source offset initial.2 opcode valid retained generation transfer
  | read attempt cursor length => exact attempt.exact length
  | retry attempt cursor length => exact attempt.retry length

inductive Trace (p : Program.Buffered.Program) :
    SerialPackage.State → Cursor → Frontend → List SerialPackage.Pins →
      SerialPackage.State → Cursor → Frontend → Type where
  | nil : Trace (p := p) before cursor frontend [] before cursor frontend
  | cons (event : Event (p := p) before cursor frontend first middle next nextFrontend)
      (rest : Trace (p := p) middle next nextFrontend more after final finalFrontend) :
      Trace (p := p) before cursor frontend (first ++ more) after final finalFrontend

theorem Trace.run_pins (trace : Trace (p := p) before cursor frontend pins after final finalFrontend) :
    before.run pins = after := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
    simp only [SerialPackage.State.run,List.foldl_append]
    change SerialPackage.State.run (SerialPackage.State.run _ _) _ = _
    rw [event.run_pins]
    exact ih

theorem Trace.preserves (trace : Trace (p := p) before cursor frontend pins after final finalFrontend)
    (initial : Valid (p := p) (layout := layout) before cursor frontend) : Valid (p := p) (layout := layout) after final finalFrontend := by
  induction trace with
  | nil => exact initial
  | cons event rest ih => exact ih (event.preserves initial)

def Trace.Observed : Trace (p := p) before cursor frontend pins after final finalFrontend → Prop
  | .nil => True
  | .cons event rest => event.Observed ∧ rest.Observed

theorem Trace.observed (trace : Trace (p := p) before cursor frontend pins after final finalFrontend)
    (initial : Valid (p := p) (layout := layout) before cursor frontend) : trace.Observed := by
  induction trace with
  | nil => trivial
  | cons event rest ih => exact ⟨event.observed initial,ih (event.preserves initial)⟩

theorem Trace.session (trace : Trace (p := p) before cursor frontend pins after final finalFrontend)
    (initial : Valid (p := p) (layout := layout) before cursor frontend) :
    before.run pins = after ∧ Valid (p := p) (layout := layout) after final finalFrontend ∧ trace.Observed :=
  ⟨trace.run_pins,trace.preserves initial,trace.observed initial⟩

theorem Trace.reusable (trace : Trace (p := p) before (.free logical offset) .available pins
    after (.free finalLogical finalOffset) .available)
    (available : Available before.record)
    (installed : InstalledSram p layout before.controller)
    (aligned : LogicalSession.Aligned before.controller logical offset) :
    before.run pins = after ∧ Available after.record ∧ InstalledSram p layout after.controller ∧
      LogicalSession.Aligned after.controller finalLogical finalOffset ∧ trace.Observed := by
  have result := trace.session ⟨available,installed,aligned⟩
  exact ⟨result.1,result.2.1.1,result.2.1.2.1,result.2.1.2.2,result.2.2⟩

end Pinwheel.Hardware.Buffered.GenericLogicalWire
