import Pinwheel.Hardware.Buffered.GenericLogicalWireCore
import Pinwheel.Hardware.Buffered.LogicalWireIdle

/-! One ordinary logical transfer state follows actual sampled-wire sessions.
START allocates from the carried free state, every raw clock advances its owned
source, RELEASE returns that same storage to free, and sampled reset/reload
rebases its epoch-local sequence offset even when interrupting active execution.
The proof concerns the typed digital SRAM package, not emitted RTL or a peer. -/
namespace Pinwheel.Hardware.Buffered.GenericLogicalWire
open Pinwheel.Hardware Pinwheel.Program Refinement Serial.Frames
open SerialSourceSession (Delivery Attempt Frontend)
variable {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}

inductive Cursor where
  | free (logical : Transfer.State) (offset : Nat)
  | owned (payload : BitVec 32) (source : Program.Buffered.State) (offset : Nat)

def Cursor.logical : Cursor → Transfer.State
  | .free logical _ => logical
  | .owned _ source _ => source.buffers

def Cursor.offset : Cursor → Nat
  | .free _ offset | .owned _ _ offset => offset

def Cursor.Holds (actual : SerialPackage.State) : Cursor → Prop
  | .free logical offset => InstalledSram p layout actual.controller ∧
      LogicalSession.Aligned actual.controller logical offset
  | .owned payload source offset => Owned (p := p) (layout := layout) actual.controller payload source offset

def Cursor.advance (pins : List SerialPackage.Pins) : Cursor → Cursor
  | .free logical offset => .free logical offset
  | .owned payload source offset =>
      .owned payload (SerialSourceRead.sourceRun p source pins) offset

def Valid (actual : SerialPackage.State) (cursor : Cursor) (frontend : Frontend) : Prop :=
  frontend.Holds actual ∧ cursor.Holds (p := p) (layout := layout) actual

theorem Cursor.quiet_run {before : SerialPackage.State} {cursor : Cursor}
    (held : cursor.Holds (p := p) (layout := layout) before) (pins : List SerialPackage.Pins)
    (quiet : ∀ i ∈ before.commands pins, SpiCircuit.Quiet i) :
    (cursor.advance (p := p) pins).Holds (p := p) (layout := layout) (before.run pins) := by
  cases cursor with
  | free logical offset => exact free_quiet_run held.1 held.2 pins quiet
  | owned payload source offset => exact held.quiet_run pins quiet

def Delivery.localStarted (delivery : Delivery before) (logical : Transfer.State) : Program.Buffered.State :=
  SerialSourceRead.sourceRun p
    (LogicalSession.started p delivery.framed.controller
      (delivery.framed.coreInputs delivery.dispatch) logical) [delivery.capture]

def Delivery.localDispatched (delivery : Delivery before) (source : Program.Buffered.State) : Program.Buffered.State :=
  Program.Buffered.advance p capacity
    (SerialSourceRead.sourceRun p source delivery.request.pins) delivery.dispatch.rawInputs

def Delivery.localAdvanced (delivery : Delivery before) (source : Program.Buffered.State) : Program.Buffered.State :=
  SerialSourceRead.sourceRun p source delivery.pins

theorem Delivery.start_owned (delivery : Delivery before) (logical : Transfer.State) (offset : Nat)
    (installed : InstalledSram p layout before.controller)
    (aligned : LogicalSession.Aligned before.controller logical offset)
    (opcode : delivery.request.word.extractLsb' 144 4 = 3#4)
    (starting : Reactive.starting.eval (delivery.framed.coreInputs delivery.dispatch)
      delivery.framed.controller.core = 1) :
    Owned (p := p) (layout := layout) delivery.after.controller (delivery.request.word.extractLsb' 0 32)
      (Delivery.localStarted (p := p) delivery logical) offset := by
  have frame := free_quiet_run installed aligned delivery.request.pins delivery.request.quiet
  have fields := SerialSourceStart.operands delivery.framed delivery.dispatch
    delivery.request.word delivery.request.closed opcode starting
  have delivered := GenericLogicalWire.start_owned frame.1 frame.2
    (delivery.framed.coreInputs delivery.dispatch) starting
  have captured := delivered.quiet_step (delivery.delivered.coreInputs delivery.capture) delivery.capture_quiet
  rw [fields.txData] at captured
  exact captured

theorem Delivery.administrative_owned (delivery : Delivery before)
    (payload : BitVec 32) (source : Program.Buffered.State) (offset : Nat)
    (owned : Owned (p := p) (layout := layout) before.controller payload source offset)
    (opcode : SerialSourceRequest.ExecutionOpcode delivery.request.word)
    (notRelease : Reactive.releasing.eval (delivery.framed.coreInputs delivery.dispatch)
      delivery.framed.controller.core = 0) :
    Owned (p := p) (layout := layout) delivery.after.controller payload (Delivery.localAdvanced (p := p) delivery source) offset := by
  have frame := owned.quiet_run delivery.request.pins delivery.request.quiet
  have inputs := SerialSourceRequest.execution_inputs delivery.framed delivery.dispatch
    delivery.request.word delivery.request.closed delivery.dispatchIdle.1 opcode
  have delivered := frame.step (delivery.framed.coreInputs delivery.dispatch) ⟨inputs.1,inputs.2,notRelease⟩
  have captured := delivered.quiet_step (delivery.delivered.coreInputs delivery.capture) delivery.capture_quiet
  change Owned delivery.after.controller payload
    (SerialSourceRead.sourceRun p source (delivery.request.pins ++ [delivery.dispatch,delivery.capture])) offset
  rw [SerialSourceTransaction.sourceRun_append]
  exact captured

def Delivery.localReleased (delivery : Delivery before) (source : Program.Buffered.State) : Transfer.State :=
  let current := SerialSourceRead.sourceRun p source delivery.request.pins
  (Transfer.step capacity current.buffers (.release current.owner)).state

theorem Delivery.release_free (delivery : Delivery before)
    (payload : BitVec 32) (source : Program.Buffered.State) (offset : Nat)
    (owned : Owned (p := p) (layout := layout) before.controller payload source offset)
    (opcode : delivery.request.word.extractLsb' 144 4 = 4#4)
    (valid : codeOf delivery.request.word = 0#4)
    (retained : delivery.framed.controller.core .retained = 1)
    (generation : delivery.request.word.extractLsb' 0 16 = delivery.framed.controller.core .generation)
    (transfer : delivery.request.word.extractLsb' 16 16 = delivery.framed.controller.core .transfer) :
    InstalledSram p layout delivery.after.controller ∧
      LogicalSession.Aligned delivery.after.controller (Delivery.localReleased (p := p) delivery source) offset := by
  let current := SerialSourceRead.sourceRun p source delivery.request.pins
  have frame := owned.quiet_run delivery.request.pins delivery.request.quiet
  obtain ⟨e,outcome,slot,_,_,owner⟩ := LogicalSession.local_completed frame.related retained
  have released := GenericSession.source_release current e outcome slot owner
  have freed : Delivery.localReleased (p := p) delivery source = {current.buffers with slot := .free} :=
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
  have aligned : LogicalSession.Aligned delivery.delivered.controller (Delivery.localReleased (p := p) delivery source) offset := by
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
    (installed : InstalledSram p layout before.controller)
    (aligned : LogicalSession.Aligned before.controller logical offset)
    (_opcode : delivery.request.word.extractLsb' 144 4 = 3#4)
    (starting : Reactive.starting.eval (delivery.framed.coreInputs delivery.dispatch)
      delivery.framed.controller.core = 1) :
    SerialSourceReceipt.Meaning delivery.after.record.response delivery.delivered.record
      (Lifecycle.IdentityView.buffered offset
        (LogicalSession.started p delivery.framed.controller
          (delivery.framed.coreInputs delivery.dispatch) logical)) := by
  have frame := free_quiet_run installed aligned delivery.request.pins delivery.request.quiet
  have delivered := GenericLogicalWire.start_owned frame.1 frame.2
    (delivery.framed.coreInputs delivery.dispatch) starting
  exact (SerialSourceReceipt.capture_source delivery.delivered _ delivered.related delivery.capture
    delivery.captureIdle.1 delivery.capturing.capture).1

theorem Delivery.administrative_receipt (delivery : Delivery before)
    (payload : BitVec 32) (source : Program.Buffered.State) (offset : Nat)
    (owned : Owned (p := p) (layout := layout) before.controller payload source offset)
    (opcode : SerialSourceRequest.ExecutionOpcode delivery.request.word)
    (notRelease : Reactive.releasing.eval (delivery.framed.coreInputs delivery.dispatch)
      delivery.framed.controller.core = 0) :
    SerialSourceReceipt.Meaning delivery.after.record.response delivery.delivered.record
      (Lifecycle.IdentityView.buffered offset (Delivery.localDispatched (p := p) delivery source)) := by
  have frame := owned.quiet_run delivery.request.pins delivery.request.quiet
  have inputs := SerialSourceRequest.execution_inputs delivery.framed delivery.dispatch
    delivery.request.word delivery.request.closed delivery.dispatchIdle.1 opcode
  have delivered := frame.step (delivery.framed.coreInputs delivery.dispatch) ⟨inputs.1,inputs.2,notRelease⟩
  exact (SerialSourceReceipt.capture_source delivery.delivered _ delivered.related delivery.capture
    delivery.captureIdle.1 delivery.capturing.capture).1

theorem Delivery.release_observed (delivery : Delivery before)
    (payload : BitVec 32) (source : Program.Buffered.State) (offset : Nat)
    (owned : Owned (p := p) (layout := layout) before.controller payload source offset)
    (opcode : delivery.request.word.extractLsb' 144 4 = 4#4)
    (valid : codeOf delivery.request.word = 0#4)
    (retained : delivery.framed.controller.core .retained = 1)
    (generation : delivery.request.word.extractLsb' 0 16 = delivery.framed.controller.core .generation)
    (transfer : delivery.request.word.extractLsb' 16 16 = delivery.framed.controller.core .transfer) :
    SerialSourceRelease.Receipt delivery.after.record.response delivery.request.word ∧
      (let current := SerialSourceRead.sourceRun p source delivery.request.pins
       ∃ e outcome, current.buffers.slot = .completed ⟨e,outcome⟩ ∧
         e.request.identity = current.owner ∧
         Transfer.step capacity current.buffers (.release current.owner) =
           ⟨Delivery.localReleased (p := p) delivery source,.released⟩) := by
  have receipt := SerialSourceSession.Delivery.release_receipt delivery
    (Lifecycle.IdentityView.buffered offset source) owned.related opcode valid retained generation transfer
  have frame := owned.quiet_run delivery.request.pins delivery.request.quiet
  obtain ⟨e,outcome,slot,_,_,owner⟩ := LogicalSession.local_completed frame.related retained
  have released := GenericSession.source_release _ e outcome slot owner
  exact ⟨receipt,e,outcome,slot,owner,by simpa only [Delivery.localReleased,
    (congrArg Transfer.Transition.state released)] using released⟩

end Pinwheel.Hardware.Buffered.GenericLogicalWire
