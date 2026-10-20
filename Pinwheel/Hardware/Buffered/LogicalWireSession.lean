import Pinwheel.Hardware.Buffered.LogicalWireCore
import Pinwheel.Hardware.Buffered.LogicalWireIdle

/-! One ordinary logical transfer state follows actual sampled-wire sessions.
START allocates from the carried free state, every raw clock advances its owned
source, RELEASE returns that same storage to free, and sampled reset/reload
rebases its epoch-local sequence offset even when interrupting active execution.
The proof concerns the typed digital SRAM package, not emitted RTL or a peer. -/
namespace Pinwheel.Hardware.Buffered.LogicalWire
open Pinwheel.Hardware Pinwheel.Program Refinement Serial.Frames
open SerialSourceSession (Delivery Attempt Frontend)

inductive Cursor where
  | free (logical : Transfer.State) (offset : Nat)
  | owned (payload : BitVec 32) (source : Program.Buffered.State) (offset : Nat)

def Cursor.logical : Cursor → Transfer.State
  | .free logical _ => logical
  | .owned _ source _ => source.buffers

def Cursor.offset : Cursor → Nat
  | .free _ offset | .owned _ _ offset => offset

def Cursor.Holds (actual : SerialPackage.State) : Cursor → Prop
  | .free logical offset => InstalledSram program layout actual.controller ∧
      LogicalSession.Aligned actual.controller logical offset
  | .owned payload source offset => Owned actual.controller payload source offset

def Cursor.advance (pins : List SerialPackage.Pins) : Cursor → Cursor
  | .free logical offset => .free logical offset
  | .owned payload source offset =>
      .owned payload (SerialSourceRead.sourceRun program source pins) offset

def Valid (actual : SerialPackage.State) (cursor : Cursor) (frontend : Frontend) : Prop :=
  frontend.Holds actual ∧ cursor.Holds actual

theorem Cursor.quiet_run {before : SerialPackage.State} {cursor : Cursor}
    (held : cursor.Holds before) (pins : List SerialPackage.Pins)
    (quiet : ∀ i ∈ before.commands pins, SpiCircuit.Quiet i) :
    (cursor.advance pins).Holds (before.run pins) := by
  cases cursor with
  | free logical offset => exact free_quiet_run held.1 held.2 pins quiet
  | owned payload source offset => exact held.quiet_run pins quiet

def Delivery.localStarted (delivery : Delivery before) (logical : Transfer.State) : Program.Buffered.State :=
  SerialSourceRead.sourceRun program
    (LogicalSession.started program delivery.framed.controller
      (delivery.framed.coreInputs delivery.dispatch) logical) [delivery.capture]

def Delivery.localDispatched (delivery : Delivery before) (source : Program.Buffered.State) : Program.Buffered.State :=
  Program.Buffered.advance program capacity
    (SerialSourceRead.sourceRun program source delivery.request.pins) delivery.dispatch.rawInputs

def Delivery.localAdvanced (delivery : Delivery before) (source : Program.Buffered.State) : Program.Buffered.State :=
  SerialSourceRead.sourceRun program source delivery.pins

theorem Delivery.start_owned (delivery : Delivery before) (logical : Transfer.State) (offset : Nat)
    (installed : InstalledSram program layout before.controller)
    (aligned : LogicalSession.Aligned before.controller logical offset)
    (opcode : delivery.request.word.extractLsb' 144 4 = 3#4)
    (starting : Reactive.starting.eval (delivery.framed.coreInputs delivery.dispatch)
      delivery.framed.controller.core = 1) :
    Owned delivery.after.controller (delivery.request.word.extractLsb' 0 32)
      (Delivery.localStarted delivery logical) offset := by
  have frame := free_quiet_run installed aligned delivery.request.pins delivery.request.quiet
  have fields := SerialSourceStart.operands delivery.framed delivery.dispatch
    delivery.request.word delivery.request.closed opcode starting
  have delivered := LogicalWire.start_owned frame.1 frame.2
    (delivery.framed.coreInputs delivery.dispatch) starting
  have captured := delivered.quiet_step (delivery.delivered.coreInputs delivery.capture) delivery.capture_quiet
  rw [fields.txData] at captured
  exact captured

theorem Delivery.administrative_owned (delivery : Delivery before)
    (payload : BitVec 32) (source : Program.Buffered.State) (offset : Nat)
    (owned : Owned before.controller payload source offset)
    (opcode : SerialSourceRequest.ExecutionOpcode delivery.request.word)
    (notRelease : Reactive.releasing.eval (delivery.framed.coreInputs delivery.dispatch)
      delivery.framed.controller.core = 0) :
    Owned delivery.after.controller payload (Delivery.localAdvanced delivery source) offset := by
  have frame := owned.quiet_run delivery.request.pins delivery.request.quiet
  have inputs := SerialSourceRequest.execution_inputs delivery.framed delivery.dispatch
    delivery.request.word delivery.request.closed delivery.dispatchIdle.1 opcode
  have delivered := frame.step (delivery.framed.coreInputs delivery.dispatch) ⟨inputs.1,inputs.2,notRelease⟩
  have captured := delivered.quiet_step (delivery.delivered.coreInputs delivery.capture) delivery.capture_quiet
  change Owned delivery.after.controller payload
    (SerialSourceRead.sourceRun program source (delivery.request.pins ++ [delivery.dispatch,delivery.capture])) offset
  rw [SerialSourceTransaction.sourceRun_append]
  exact captured

def Delivery.localReleased (delivery : Delivery before) (source : Program.Buffered.State) : Transfer.State :=
  let current := SerialSourceRead.sourceRun program source delivery.request.pins
  (Transfer.step capacity current.buffers (.release current.owner)).state

theorem Delivery.release_free (delivery : Delivery before)
    (payload : BitVec 32) (source : Program.Buffered.State) (offset : Nat)
    (owned : Owned before.controller payload source offset)
    (opcode : delivery.request.word.extractLsb' 144 4 = 4#4)
    (valid : codeOf delivery.request.word = 0#4)
    (retained : delivery.framed.controller.core .retained = 1)
    (generation : delivery.request.word.extractLsb' 0 16 = delivery.framed.controller.core .generation)
    (transfer : delivery.request.word.extractLsb' 16 16 = delivery.framed.controller.core .transfer) :
    InstalledSram program layout delivery.after.controller ∧
      LogicalSession.Aligned delivery.after.controller (Delivery.localReleased delivery source) offset := by
  let current := SerialSourceRead.sourceRun program source delivery.request.pins
  have frame := owned.quiet_run delivery.request.pins delivery.request.quiet
  obtain ⟨e,outcome,slot,_,_,owner⟩ := LogicalSession.local_completed frame.related retained
  have released := GenericSession.source_release current e outcome slot owner
  have freed : Delivery.localReleased delivery source = {current.buffers with slot := .free} :=
    congrArg Transfer.Transition.state released
  have fields := SerialSourceRelease.operands delivery.framed delivery.dispatch
    delivery.request.word delivery.request.closed opcode valid delivery.dispatchIdle.1
  have gen := fields.generation.trans generation
  have seq := fields.transfer.trans transfer
  have execution : SramExecution.ExecutingInput (delivery.framed.coreInputs delivery.dispatch) := by
    simp [SramExecution.ExecutingInput,SharedBranches.Runtime,fields.cold,fields.command]
  have installed := frame.related.installed.step (delivery.framed.coreInputs delivery.dispatch) execution
  have transferHeld := Lifecycle.release_scalar_step delivery.framed.controller
    (delivery.framed.coreInputs delivery.dispatch) fields.cold fields.command retained gen seq .transfer trivial
  change delivery.delivered.controller.core .transfer = delivery.framed.controller.core .transfer at transferHeld
  have aligned : LogicalSession.Aligned delivery.delivered.controller (Delivery.localReleased delivery source) offset := by
    refine ⟨by rw [freed],
      Lifecycle.release_scalar_step delivery.framed.controller
        (delivery.framed.coreInputs delivery.dispatch) fields.cold fields.command retained gen seq .phase trivial,
      Lifecycle.release_scalar_step delivery.framed.controller
        (delivery.framed.coreInputs delivery.dispatch) fields.cold fields.command retained gen seq .retained trivial,?_⟩
    rw [freed,transferHeld]
    exact frame.sequence
  exact free_quiet_run installed aligned [delivery.capture] (by
    intro input member
    rcases List.mem_singleton.mp member with rfl
    exact delivery.capture_quiet)

theorem Delivery.start_receipt (delivery : Delivery before) (logical : Transfer.State) (offset : Nat)
    (installed : InstalledSram program layout before.controller)
    (aligned : LogicalSession.Aligned before.controller logical offset)
    (_opcode : delivery.request.word.extractLsb' 144 4 = 3#4)
    (starting : Reactive.starting.eval (delivery.framed.coreInputs delivery.dispatch)
      delivery.framed.controller.core = 1) :
    SerialSourceReceipt.Meaning delivery.after.record.response delivery.delivered.record
      (Lifecycle.IdentityView.buffered offset
        (LogicalSession.started program delivery.framed.controller
          (delivery.framed.coreInputs delivery.dispatch) logical)) := by
  have frame := free_quiet_run installed aligned delivery.request.pins delivery.request.quiet
  have delivered := LogicalWire.start_owned frame.1 frame.2
    (delivery.framed.coreInputs delivery.dispatch) starting
  exact (SerialSourceReceipt.capture_source delivery.delivered _ delivered.related delivery.capture
    delivery.captureIdle.1 delivery.capturing.capture).1

theorem Delivery.administrative_receipt (delivery : Delivery before)
    (payload : BitVec 32) (source : Program.Buffered.State) (offset : Nat)
    (owned : Owned before.controller payload source offset)
    (opcode : SerialSourceRequest.ExecutionOpcode delivery.request.word)
    (notRelease : Reactive.releasing.eval (delivery.framed.coreInputs delivery.dispatch)
      delivery.framed.controller.core = 0) :
    SerialSourceReceipt.Meaning delivery.after.record.response delivery.delivered.record
      (Lifecycle.IdentityView.buffered offset (Delivery.localDispatched delivery source)) := by
  have frame := owned.quiet_run delivery.request.pins delivery.request.quiet
  have inputs := SerialSourceRequest.execution_inputs delivery.framed delivery.dispatch
    delivery.request.word delivery.request.closed delivery.dispatchIdle.1 opcode
  have delivered := frame.step (delivery.framed.coreInputs delivery.dispatch) ⟨inputs.1,inputs.2,notRelease⟩
  exact (SerialSourceReceipt.capture_source delivery.delivered _ delivered.related delivery.capture
    delivery.captureIdle.1 delivery.capturing.capture).1

theorem Delivery.release_observed (delivery : Delivery before)
    (payload : BitVec 32) (source : Program.Buffered.State) (offset : Nat)
    (owned : Owned before.controller payload source offset)
    (opcode : delivery.request.word.extractLsb' 144 4 = 4#4)
    (valid : codeOf delivery.request.word = 0#4)
    (retained : delivery.framed.controller.core .retained = 1)
    (generation : delivery.request.word.extractLsb' 0 16 = delivery.framed.controller.core .generation)
    (transfer : delivery.request.word.extractLsb' 16 16 = delivery.framed.controller.core .transfer) :
    SerialSourceRelease.Receipt delivery.after.record.response delivery.request.word ∧
      (let current := SerialSourceRead.sourceRun program source delivery.request.pins
       ∃ e outcome, current.buffers.slot = .completed ⟨e,outcome⟩ ∧
         e.request.identity = current.owner ∧
         Transfer.step capacity current.buffers (.release current.owner) =
           ⟨Delivery.localReleased delivery source,.released⟩) := by
  have receipt := SerialSourceSession.Delivery.release_receipt delivery
    (Lifecycle.IdentityView.buffered offset source) owned.related opcode valid retained generation transfer
  have frame := owned.quiet_run delivery.request.pins delivery.request.quiet
  obtain ⟨e,outcome,slot,_,_,owner⟩ := LogicalSession.local_completed frame.related retained
  have released := GenericSession.source_release _ e outcome slot owner
  exact ⟨receipt,e,outcome,slot,owner,by simpa only [Delivery.localReleased,
    (congrArg Transfer.Transition.state released)] using released⟩

def reloadLogical (cursor : Cursor) (requestPins : List SerialPackage.Pins) : Transfer.State :=
  LogicalSession.resetLogical (cursor.advance requestPins).logical

theorem reload_free (cursor : Cursor) (reset : SerialWire.Transaction before)
    (kind : SerialUpload.ResetKind) (sequence : BitVec 16)
    (word : reset.request.word = kind.word sequence) (loading : SerialUpload.Loading reset.after)
    (space : SerialUpload.resetGeneration kind (reset.framed.controller.core .generation) ≠ 65535) :
    InstalledSram program layout loading.after.controller ∧
      LogicalSession.Aligned loading.after.controller
        (reloadLogical cursor reset.request.pins) (loading.after.controller.core .transfer).toNat := by
  have result := SerialUpload.wire_install reset kind sequence word loading space
  exact ⟨result.1,⟨rfl,result.2.1.phase,result.2.1.retained,rfl⟩⟩

inductive Event :
    SerialPackage.State → Cursor → Frontend → List SerialPackage.Pins →
      SerialPackage.State → Cursor → Frontend → Type where
  | padding (pins : List SerialPackage.Pins) (cursor : Cursor) (frontend : Frontend)
      (physical : SerialSourceSession.IdlePins pins) :
      Event before cursor frontend pins (before.run pins) (cursor.advance pins) frontend
  | coldInitialize (cursor : Cursor) (frontend : Frontend) (coldPin : SerialPackage.Pins)
      (cold : coldPin.cold = true) (idle : coldPin.csn = true)
      (loading : SerialUpload.Loading (before.step coldPin)) :
      Event before cursor frontend (coldPin :: loading.pins) loading.after
        (.free (LogicalSession.resetLogical cursor.logical) (loading.after.controller.core .transfer).toNat) .available
  | start (delivery : Delivery before) (logical : Transfer.State) (offset : Nat)
      (opcode : delivery.request.word.extractLsb' 144 4 = 3#4)
      (starting : Reactive.starting.eval (delivery.framed.coreInputs delivery.dispatch)
        delivery.framed.controller.core = 1) :
      Event before (.free logical offset) .available delivery.pins delivery.after
        (.owned (delivery.request.word.extractLsb' 0 32) (Delivery.localStarted delivery logical) offset) .ready
  | administrative (delivery : Delivery before) (payload : BitVec 32)
      (source : Program.Buffered.State) (offset : Nat)
      (opcode : SerialSourceRequest.ExecutionOpcode delivery.request.word)
      (notRelease : Reactive.releasing.eval (delivery.framed.coreInputs delivery.dispatch)
        delivery.framed.controller.core = 0) :
      Event before (.owned payload source offset) .available delivery.pins delivery.after
        (.owned payload (Delivery.localAdvanced delivery source) offset) .ready
  | release (delivery : Delivery before) (payload : BitVec 32)
      (source : Program.Buffered.State) (offset : Nat)
      (opcode : delivery.request.word.extractLsb' 144 4 = 4#4)
      (valid : codeOf delivery.request.word = 0#4)
      (retained : delivery.framed.controller.core .retained = 1)
      (generation : delivery.request.word.extractLsb' 0 16 = delivery.framed.controller.core .generation)
      (transfer : delivery.request.word.extractLsb' 16 16 = delivery.framed.controller.core .transfer) :
      Event before (.owned payload source offset) .available delivery.pins delivery.after
        (.free (Delivery.localReleased delivery source) offset) .ready
  | read (attempt : Attempt before) (cursor : Cursor) (length : attempt.bits.length = 192) :
      Event before cursor .ready attempt.pins attempt.after (cursor.advance attempt.pins) .available
  | retry (attempt : Attempt before) (cursor : Cursor) (length : attempt.bits.length ≠ 192) :
      Event before cursor .ready attempt.pins attempt.after (cursor.advance attempt.pins) .ready
  | reload (cursor : Cursor) (reset : SerialWire.Transaction before)
      (kind : SerialUpload.ResetKind) (sequence : BitVec 16)
      (word : reset.request.word = kind.word sequence) (loading : SerialUpload.Loading reset.after)
      (space : SerialUpload.resetGeneration kind (reset.framed.controller.core .generation) ≠ 65535) :
      Event before cursor .available (reset.pins ++ loading.pins) loading.after
        (.free (reloadLogical cursor reset.request.pins) (loading.after.controller.core .transfer).toNat) .available

/-- Any finite sampled SCK/MOSI/raw history can pad either frontend boundary
by holding physical CS high and cold low. -/
def Event.deselected (samples : List SerialPackage.Pins) (cursor : Cursor) (frontend : Frontend) :
    Event before cursor frontend (SerialSourceSession.deselected samples)
      (before.run (SerialSourceSession.deselected samples))
      (cursor.advance (SerialSourceSession.deselected samples)) frontend :=
  .padding _ cursor frontend (SerialSourceSession.deselected_idle samples)

theorem Event.run_pins (event : Event before cursor frontend pins after next nextFrontend) :
    before.run pins = after := by
  cases event with
  | padding => rfl
  | coldInitialize cursor frontend coldPin cold idle loading =>
    exact (SerialUpload.cold_install _ coldPin cold idle loading).2.2.2.2.2.2
  | start delivery _ _ _ _ => exact delivery.run_pins
  | administrative delivery _ _ _ _ _ => exact delivery.run_pins
  | release delivery _ _ _ _ _ _ _ _ => exact delivery.run_pins
  | read => rfl
  | retry => rfl
  | reload cursor reset kind sequence word loading space =>
    exact (SerialUpload.wire_install reset kind sequence word loading space).2.2.2.2

theorem Event.preserves (event : Event before cursor frontend pins after next nextFrontend)
    (initial : Valid before cursor frontend) : Valid after next nextFrontend := by
  cases event with
  | padding pins cursor frontend physical =>
    have idle := SerialSourceSession.Frontend.idle_run initial.1 pins physical
    exact ⟨idle.1, Cursor.quiet_run initial.2 pins idle.2.2⟩
  | coldInitialize cursor frontend coldPin cold idle loading =>
    obtain ⟨installed,phase,retained,_,_,available,_⟩ := SerialUpload.cold_install _ coldPin cold idle loading
    exact ⟨available,installed,⟨rfl,phase,retained,rfl⟩⟩
  | start delivery logical offset opcode starting =>
    exact ⟨delivery.ready,Delivery.start_owned delivery logical offset initial.2.1 initial.2.2 opcode starting⟩
  | administrative delivery payload source offset opcode notRelease =>
    exact ⟨delivery.ready,Delivery.administrative_owned delivery payload source offset initial.2 opcode notRelease⟩
  | release delivery payload source offset opcode valid retained generation transfer =>
    exact ⟨delivery.ready,Delivery.release_free delivery payload source offset initial.2
      opcode valid retained generation transfer⟩
  | read attempt cursor length => exact ⟨(attempt.exact length).1,Cursor.quiet_run initial.2 _ attempt.quiet⟩
  | retry attempt cursor length => exact ⟨(attempt.retry length).1,Cursor.quiet_run initial.2 _ attempt.quiet⟩
  | reload cursor reset kind sequence word loading space =>
    exact ⟨(SerialUpload.wire_install reset kind sequence word loading space).2.2.1,
      reload_free cursor reset kind sequence word loading space⟩

def Event.Observed (event : Event before cursor frontend pins after next nextFrontend) : Prop :=
  match event with
  | .padding pins _ _ _ =>
    (before.run pins).record.response = before.record.response ∧
      (∀ input ∈ before.commands pins, SpiCircuit.Quiet input) ∧
      (before.commands pins).length = pins.length
  | .coldInitialize cursor _ _ _ _ loading =>
    Transfer.step capacity cursor.logical .reset =
      ⟨LogicalSession.resetLogical cursor.logical,.reset⟩ ∧
      (LogicalSession.resetLogical cursor.logical).epoch = cursor.logical.epoch + 1 ∧
      (LogicalSession.resetLogical cursor.logical).nextSequence = 1 ∧
      loading.after.controller.core .generation = 1 ∧ loading.after.controller.core .transfer = 0
  | .start delivery logical offset _ _ =>
    SerialSourceReceipt.Meaning delivery.after.record.response delivery.delivered.record
      (Lifecycle.IdentityView.buffered offset
        (LogicalSession.started program delivery.framed.controller
          (delivery.framed.coreInputs delivery.dispatch) logical))
  | .administrative delivery _ source offset _ _ =>
    SerialSourceReceipt.Meaning delivery.after.record.response delivery.delivered.record
      (Lifecycle.IdentityView.buffered offset (Delivery.localDispatched delivery source))
  | .release delivery _ source _ _ _ _ _ _ =>
    SerialSourceRelease.Receipt delivery.after.record.response delivery.request.word ∧
      (let current := SerialSourceRead.sourceRun program source delivery.request.pins
       ∃ e outcome, current.buffers.slot = .completed ⟨e,outcome⟩ ∧
         e.request.identity = current.owner ∧
         Transfer.step capacity current.buffers (.release current.owner) =
           ⟨Delivery.localReleased delivery source,.released⟩)
  | .read attempt _ _ => attempt.ExactMeaning
  | .retry attempt _ _ => attempt.RetryMeaning
  | .reload cursor reset kind _ _ loading _ =>
    (cursor.advance reset.request.pins).Holds reset.framed ∧
      Transfer.step capacity (cursor.advance reset.request.pins).logical .reset =
        ⟨reloadLogical cursor reset.request.pins,.reset⟩ ∧
      (reloadLogical cursor reset.request.pins).epoch =
        (cursor.advance reset.request.pins).logical.epoch + 1 ∧
      (reloadLogical cursor reset.request.pins).nextSequence = 1 ∧
      SerialUpload.Complete (SerialUpload.resetGeneration kind (reset.framed.controller.core .generation))
        loading.after.controller ∧
      loading.after.controller.core .transfer =
        (match kind with | .cold => 0 | .warm => before.controller.core .transfer)

theorem Event.observed (event : Event before cursor frontend pins after next nextFrontend)
    (initial : Valid before cursor frontend) : event.Observed := by
  cases event with
  | padding pins cursor frontend physical =>
    have idle := SerialSourceSession.Frontend.idle_run initial.1 pins physical
    exact ⟨idle.2.1, idle.2.2, before.commands_length pins⟩
  | coldInitialize cursor frontend coldPin cold idle loading =>
    obtain ⟨_,_,_,generation,transfer,_,_⟩ := SerialUpload.cold_install _ coldPin cold idle loading
    exact ⟨rfl,rfl,rfl,generation,transfer⟩
  | start delivery logical offset opcode starting =>
    exact Delivery.start_receipt delivery logical offset initial.2.1 initial.2.2 opcode starting
  | administrative delivery payload source offset opcode notRelease =>
    exact Delivery.administrative_receipt delivery payload source offset initial.2 opcode notRelease
  | release delivery payload source offset opcode valid retained generation transfer =>
    exact Delivery.release_observed delivery payload source offset initial.2 opcode valid retained generation transfer
  | read attempt cursor length => exact attempt.exact length
  | retry attempt cursor length => exact attempt.retry length
  | reload cursor reset kind sequence word loading space =>
    have result := SerialUpload.wire_install reset kind sequence word loading space
    exact ⟨Cursor.quiet_run initial.2 _ reset.request.quiet,rfl,rfl,rfl,result.2.1,result.2.2.2.1⟩

inductive Trace :
    SerialPackage.State → Cursor → Frontend → List SerialPackage.Pins →
      SerialPackage.State → Cursor → Frontend → Type where
  | nil : Trace before cursor frontend [] before cursor frontend
  | cons (event : Event before cursor frontend first middle next nextFrontend)
      (rest : Trace middle next nextFrontend more after final finalFrontend) :
      Trace before cursor frontend (first ++ more) after final finalFrontend

theorem Trace.run_pins (trace : Trace before cursor frontend pins after final finalFrontend) :
    before.run pins = after := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
    simp only [SerialPackage.State.run,List.foldl_append]
    change SerialPackage.State.run (SerialPackage.State.run _ _) _ = _
    rw [event.run_pins]
    exact ih

theorem Trace.preserves (trace : Trace before cursor frontend pins after final finalFrontend)
    (initial : Valid before cursor frontend) : Valid after final finalFrontend := by
  induction trace with
  | nil => exact initial
  | cons event rest ih => exact ih (event.preserves initial)

def Trace.Observed : Trace before cursor frontend pins after final finalFrontend → Prop
  | .nil => True
  | .cons event rest => event.Observed ∧ rest.Observed

theorem Trace.observed (trace : Trace before cursor frontend pins after final finalFrontend)
    (initial : Valid before cursor frontend) : trace.Observed := by
  induction trace with
  | nil => trivial
  | cons event rest ih => exact ⟨event.observed initial,ih (event.preserves initial)⟩

theorem Trace.session (trace : Trace before cursor frontend pins after final finalFrontend)
    (initial : Valid before cursor frontend) :
    before.run pins = after ∧ Valid after final finalFrontend ∧ trace.Observed :=
  ⟨trace.run_pins,trace.preserves initial,trace.observed initial⟩

theorem Trace.reusable (trace : Trace before (.free logical offset) .available pins
    after (.free finalLogical finalOffset) .available)
    (available : Available before.record)
    (installed : InstalledSram program layout before.controller)
    (aligned : LogicalSession.Aligned before.controller logical offset) :
    before.run pins = after ∧ Available after.record ∧ InstalledSram program layout after.controller ∧
      LogicalSession.Aligned after.controller finalLogical finalOffset ∧ trace.Observed := by
  have result := trace.session ⟨available,installed,aligned⟩
  exact ⟨result.1,result.2.1.1,result.2.1.2.1,result.2.1.2.2,result.2.2⟩

end Pinwheel.Hardware.Buffered.LogicalWire
