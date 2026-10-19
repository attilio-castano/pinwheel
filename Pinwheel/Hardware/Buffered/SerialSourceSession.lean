import Pinwheel.Hardware.Buffered.SerialWireTransaction
import Pinwheel.Hardware.Buffered.SerialSourceAdministrative
import Pinwheel.Hardware.Buffered.SerialSourceRelease
import Pinwheel.Hardware.Buffered.SerialSourceRetry

/-! Arbitrary finite source-grounded wire sessions. Request reception,
dispatch, capture, short reads and exact reads retain all raw controller clocks.
The trace alternates frontend availability and held receipts; matching RELEASE
returns the installed engine to its reusable free state. Transfer epoch/offset
bookkeeping across resets is the separate LogicalSession contract. -/
namespace Pinwheel.Hardware.Buffered.SerialSourceSession
open Pinwheel.Hardware Pinwheel.Program Serial.Frames

structure Delivery (before : SerialPackage.State) where
  request : SerialWire.Request before
  dispatch : SerialPackage.Pins
  capture : SerialPackage.Pins
  dispatchIdle : dispatch.cold = false ∧ dispatch.csn = true
  captureIdle : capture.cold = false ∧ capture.csn = true

def Delivery.framed (delivery : Delivery before) : SerialPackage.State := delivery.request.framed
def Delivery.delivered (delivery : Delivery before) : SerialPackage.State :=
  delivery.framed.step delivery.dispatch
def Delivery.after (delivery : Delivery before) : SerialPackage.State :=
  delivery.delivered.step delivery.capture
def Delivery.pins (delivery : Delivery before) : List SerialPackage.Pins :=
  delivery.request.pins ++ [delivery.dispatch,delivery.capture]
def Delivery.rejection (delivery : Delivery before) : Bool :=
  (codeOf delivery.request.word == 0) && (delivery.framed.status delivery.dispatch .rejected == 1)

theorem Delivery.run_pins (delivery : Delivery before) : before.run delivery.pins = delivery.after := by
  simp only [Delivery.pins, SerialPackage.State.run, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

theorem Delivery.capturing (delivery : Delivery before) :
    Capturing delivery.request.word delivery.rejection delivery.delivered.record := by
  rw [Delivery.delivered, delivery.framed.record_step]
  exact delivery.request.closed.step_dispatch (delivery.framed.inputs delivery.dispatch) delivery.dispatchIdle

theorem Delivery.ready (delivery : Delivery before) : ReceiptReady delivery.after.record := by
  rw [Delivery.after, delivery.delivered.record_step]
  exact (delivery.capturing.step_capture (delivery.delivered.inputs delivery.capture) delivery.captureIdle).1

theorem Delivery.capture_quiet (delivery : Delivery before) :
    SpiCircuit.Quiet (delivery.delivered.coreInputs delivery.capture) :=
  SerialSourceRead.core_quiet delivery.delivered delivery.capture delivery.captureIdle.1 delivery.capturing.dispatch

def Delivery.started (program : Program.Buffered.Program) (delivery : Delivery before) : Program.Buffered.State :=
  SerialSourceRead.sourceRun program
    (GenericStart.started program delivery.framed.controller.core
      (delivery.framed.coreInputs delivery.dispatch)) [delivery.capture]

def Delivery.advanced (program : Program.Buffered.Program) (source : Program.Buffered.State)
    (delivery : Delivery before) : Program.Buffered.State :=
  SerialSourceRead.sourceRun program source delivery.pins

structure Attempt (before : SerialPackage.State) where
  assert : SerialPackage.Pins
  close : SerialPackage.Pins
  bits : List Bool
  samples : List SerialPackage.Pins
  ready : ReceiptReady before.record
  low : Low (before.inputs assert)
  wire : IsBits bits ((before.step assert).frontendInputs samples)
  idle : close.cold = false ∧ close.csn = true

def Attempt.pins (attempt : Attempt before) : List SerialPackage.Pins := attempt.assert :: (attempt.samples ++ [attempt.close])
def Attempt.after (attempt : Attempt before) : SerialPackage.State := before.run attempt.pins

theorem Attempt.quiet (attempt : Attempt before) :
    ∀ input ∈ before.commands attempt.pins, SpiCircuit.Quiet input :=
  before.receipt_read_quiet attempt.assert attempt.close attempt.bits attempt.samples
    attempt.ready attempt.low attempt.wire attempt.idle

theorem Attempt.exact (attempt : Attempt before) (length : attempt.bits.length = 192) :
    Available attempt.after.record ∧ attempt.after.record.response = before.record.response ∧
      before.readObserved attempt.pins =
        (List.range 192).map (fun k => before.record.response.getLsbD (191-k)) :=
  before.receipt_exact_read attempt.assert attempt.close attempt.bits attempt.samples
    attempt.ready attempt.low attempt.wire attempt.idle length

theorem Attempt.retry (attempt : Attempt before) (length : attempt.bits.length ≠ 192) :
    ReceiptReady attempt.after.record ∧ attempt.after.record.response = before.record.response :=
  before.receipt_retry_read attempt.assert attempt.close attempt.bits attempt.samples
    attempt.ready attempt.low attempt.wire attempt.idle length

inductive Frontend where
  | available | ready

def Frontend.Holds : Frontend → SerialPackage.State → Prop
  | .available, actual => Available actual.record
  | .ready, actual => ReceiptReady actual.record

inductive Cursor where
  | free
  | owned (payload : BitVec 32) (source : Program.Buffered.State)

def Cursor.Holds (program : Program.Buffered.Program) (layout : GenericCertificate.Layout program)
    (actual : SerialPackage.State) : Cursor → Prop
  | .free => Refinement.InstalledSram program layout actual.controller ∧ SerialSourceRelease.Free actual.controller
  | .owned payload source => Refinement.RelatedSram program layout payload actual.controller source

def Cursor.advance (program : Program.Buffered.Program) (pins : List SerialPackage.Pins) : Cursor → Cursor
  | .free => .free
  | .owned payload source => .owned payload (SerialSourceRead.sourceRun program source pins)

def Valid (program : Program.Buffered.Program) (layout : GenericCertificate.Layout program)
    (actual : SerialPackage.State) (cursor : Cursor) (frontend : Frontend) : Prop :=
  frontend.Holds actual ∧ cursor.Holds program layout actual

theorem start_delivered {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {before : SerialPackage.State}
    (delivery : Delivery before)
    (installed : Refinement.InstalledSram program layout before.controller)
    (opcode : delivery.request.word.extractLsb' 144 4 = 3#4)
    (starting : Reactive.starting.eval (delivery.framed.coreInputs delivery.dispatch)
      delivery.framed.controller.core = 1) :
    Refinement.RelatedSram program layout (delivery.request.word.extractLsb' 0 32)
      delivery.delivered.controller
      (GenericStart.started program delivery.framed.controller.core
        (delivery.framed.coreInputs delivery.dispatch)) := by
  have frame := SerialSourceStart.frame_installed before installed delivery.request.word
    delivery.request.assert delivery.request.close delivery.request.samples delivery.request.available
    delivery.request.low delivery.request.bits delivery.request.idle
  have fields := SerialSourceStart.operands delivery.framed delivery.dispatch
    delivery.request.word frame.1 opcode starting
  have delivered := frame.2.start (delivery.framed.coreInputs delivery.dispatch) starting
  have wire : Refinement.RelatedSram program layout (delivery.request.word.extractLsb' 0 32)
      delivery.delivered.controller
      (GenericStart.started program delivery.framed.controller.core
        (delivery.framed.coreInputs delivery.dispatch)) := by
    rw [← fields.txData]
    exact delivered
  exact wire

private theorem start_delivery {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {before : SerialPackage.State}
    (delivery : Delivery before)
    (installed : Refinement.InstalledSram program layout before.controller)
    (opcode : delivery.request.word.extractLsb' 144 4 = 3#4)
    (starting : Reactive.starting.eval (delivery.framed.coreInputs delivery.dispatch)
      delivery.framed.controller.core = 1) :
    Refinement.RelatedSram program layout (delivery.request.word.extractLsb' 0 32)
      delivery.after.controller (delivery.started program) :=
  (start_delivered delivery installed opcode starting).step
    (delivery.delivered.coreInputs delivery.capture) delivery.capture_quiet

theorem Delivery.start_receipt {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {before : SerialPackage.State}
    (delivery : Delivery before)
    (installed : Refinement.InstalledSram program layout before.controller)
    (opcode : delivery.request.word.extractLsb' 144 4 = 3#4)
    (starting : Reactive.starting.eval (delivery.framed.coreInputs delivery.dispatch)
      delivery.framed.controller.core = 1) :
    SerialSourceReceipt.Meaning delivery.after.record.response delivery.delivered.record
      (GenericStart.started program delivery.framed.controller.core
        (delivery.framed.coreInputs delivery.dispatch)) :=
  (SerialSourceReceipt.capture_source delivery.delivered _
    (start_delivered delivery installed opcode starting) delivery.capture
    delivery.captureIdle.1 delivery.capturing.capture).1

def Delivery.dispatched (program : Program.Buffered.Program) (source : Program.Buffered.State)
    (delivery : Delivery before) : Program.Buffered.State :=
  Program.Buffered.advance program Refinement.capacity
    (SerialSourceRead.sourceRun program source delivery.request.pins) delivery.dispatch.rawInputs

theorem administrative_delivered {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    {before : SerialPackage.State} (delivery : Delivery before) (source : Program.Buffered.State)
    (related : Refinement.RelatedSram program layout payload before.controller source)
    (opcode : SerialSourceRequest.ExecutionOpcode delivery.request.word)
    (notRelease : Reactive.releasing.eval (delivery.framed.coreInputs delivery.dispatch)
      delivery.framed.controller.core = 0) :
    Refinement.RelatedSram program layout payload delivery.delivered.controller
      (delivery.dispatched program source) := by
  have frame := SerialSourceRequest.frame_source before source related delivery.request.word
    delivery.request.assert delivery.request.close delivery.request.samples delivery.request.available
    delivery.request.low delivery.request.bits delivery.request.idle
  have inputs := SerialSourceRequest.execution_inputs delivery.framed delivery.dispatch
    delivery.request.word frame.1 delivery.dispatchIdle.1 opcode
  exact frame.2.step_administrative (delivery.framed.coreInputs delivery.dispatch)
    ⟨inputs.1,inputs.2,notRelease⟩

theorem Delivery.administrative_receipt {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    {before : SerialPackage.State} (delivery : Delivery before) (source : Program.Buffered.State)
    (related : Refinement.RelatedSram program layout payload before.controller source)
    (opcode : SerialSourceRequest.ExecutionOpcode delivery.request.word)
    (notRelease : Reactive.releasing.eval (delivery.framed.coreInputs delivery.dispatch)
      delivery.framed.controller.core = 0) :
    SerialSourceReceipt.Meaning delivery.after.record.response delivery.delivered.record
      (delivery.dispatched program source) :=
  (SerialSourceReceipt.capture_source delivery.delivered _
    (administrative_delivered delivery source related opcode notRelease) delivery.capture
    delivery.captureIdle.1 delivery.capturing.capture).1

private theorem administrative_delivery {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    {before : SerialPackage.State} (delivery : Delivery before) (source : Program.Buffered.State)
    (related : Refinement.RelatedSram program layout payload before.controller source)
    (opcode : SerialSourceRequest.ExecutionOpcode delivery.request.word)
    (notRelease : Reactive.releasing.eval (delivery.framed.coreInputs delivery.dispatch)
      delivery.framed.controller.core = 0) :
    Refinement.RelatedSram program layout payload delivery.after.controller (delivery.advanced program source) := by
  have frame := SerialSourceRequest.frame_source before source related delivery.request.word
    delivery.request.assert delivery.request.close delivery.request.samples delivery.request.available
    delivery.request.low delivery.request.bits delivery.request.idle
  have inputs := SerialSourceRequest.execution_inputs delivery.framed delivery.dispatch
    delivery.request.word frame.1 delivery.dispatchIdle.1 opcode
  have delivered := frame.2.step_administrative (delivery.framed.coreInputs delivery.dispatch)
    ⟨inputs.1,inputs.2,notRelease⟩
  have captured := delivered.step (delivery.delivered.coreInputs delivery.capture) delivery.capture_quiet
  change Refinement.RelatedSram program layout payload delivery.after.controller
    (SerialSourceRead.sourceRun program source (delivery.request.pins ++ [delivery.dispatch,delivery.capture]))
  rw [SerialSourceTransaction.sourceRun_append]
  exact captured

theorem release_delivered {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    {before : SerialPackage.State} (delivery : Delivery before) (source : Program.Buffered.State)
    (related : Refinement.RelatedSram program layout payload before.controller source)
    (opcode : delivery.request.word.extractLsb' 144 4 = 4#4)
    (valid : codeOf delivery.request.word = 0#4)
    (retained : delivery.framed.controller.core .retained = 1)
    (generation : delivery.request.word.extractLsb' 0 16 = delivery.framed.controller.core .generation)
    (transfer : delivery.request.word.extractLsb' 16 16 = delivery.framed.controller.core .transfer) :
    Refinement.InstalledSram program layout delivery.delivered.controller ∧
      SerialSourceRelease.Free delivery.delivered.controller := by
  have frame := SerialSourceRequest.frame_source before source related delivery.request.word
    delivery.request.assert delivery.request.close delivery.request.samples delivery.request.available
    delivery.request.low delivery.request.bits delivery.request.idle
  have fields := SerialSourceRelease.operands delivery.framed delivery.dispatch
    delivery.request.word frame.1 opcode valid delivery.dispatchIdle.1
  have gen := fields.generation.trans generation
  have seq := fields.transfer.trans transfer
  have installed := frame.2.installed
  have executing : SramExecution.ExecutingInput (delivery.framed.coreInputs delivery.dispatch) := by
    simp [SramExecution.ExecutingInput,SharedBranches.Runtime,fields.cold,fields.command]
  have free : SerialSourceRelease.Free delivery.delivered.controller :=
    ⟨Lifecycle.release_scalar_step delivery.framed.controller (delivery.framed.coreInputs delivery.dispatch)
      fields.cold fields.command retained gen seq .phase trivial,
     Lifecycle.release_scalar_step delivery.framed.controller (delivery.framed.coreInputs delivery.dispatch)
      fields.cold fields.command retained gen seq .retained trivial⟩
  have post := installed.step (delivery.framed.coreInputs delivery.dispatch) executing
  exact ⟨post,free⟩

private theorem release_delivery {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    {before : SerialPackage.State} (delivery : Delivery before) (source : Program.Buffered.State)
    (related : Refinement.RelatedSram program layout payload before.controller source)
    (opcode : delivery.request.word.extractLsb' 144 4 = 4#4)
    (valid : codeOf delivery.request.word = 0#4)
    (retained : delivery.framed.controller.core .retained = 1)
    (generation : delivery.request.word.extractLsb' 0 16 = delivery.framed.controller.core .generation)
    (transfer : delivery.request.word.extractLsb' 16 16 = delivery.framed.controller.core .transfer) :
    Refinement.InstalledSram program layout delivery.after.controller ∧ SerialSourceRelease.Free delivery.after.controller := by
  have post := release_delivered delivery source related opcode valid retained generation transfer
  exact ⟨post.1.step (delivery.delivered.coreInputs delivery.capture)
      (by have q := delivery.capture_quiet
          simp [SramExecution.ExecutingInput,SharedBranches.Runtime,q.1,q.2]),
    SerialSourceRelease.free_step post.2 _ delivery.capture_quiet⟩

theorem Delivery.release_receipt {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    {before : SerialPackage.State} (delivery : Delivery before) (source : Program.Buffered.State)
    (related : Refinement.RelatedSram program layout payload before.controller source)
    (opcode : delivery.request.word.extractLsb' 144 4 = 4#4)
    (valid : codeOf delivery.request.word = 0#4)
    (retained : delivery.framed.controller.core .retained = 1)
    (generation : delivery.request.word.extractLsb' 0 16 = delivery.framed.controller.core .generation)
    (transfer : delivery.request.word.extractLsb' 16 16 = delivery.framed.controller.core .transfer) :
    SerialSourceRelease.Receipt delivery.after.record.response delivery.request.word := by
  have frame := SerialSourceRequest.frame_source before source related delivery.request.word
    delivery.request.assert delivery.request.close delivery.request.samples delivery.request.available
    delivery.request.low delivery.request.bits delivery.request.idle
  have fields := SerialSourceRelease.operands delivery.framed delivery.dispatch
    delivery.request.word frame.1 opcode valid delivery.dispatchIdle.1
  have rejection := SerialSourceRelease.accepted_not_rejected frame.2.installed
    (delivery.framed.coreInputs delivery.dispatch) fields retained
    (fields.generation.trans generation) (fields.transfer.trans transfer)
  have closed : Closed delivery.request.word delivery.framed.record := delivery.request.closed
  have pending : Capturing delivery.request.word false delivery.delivered.record := by
    rw [Delivery.delivered,delivery.framed.record_step]
    simpa only [show (delivery.framed.inputs delivery.dispatch).status .rejected = 0 from rejection,
      show ((0 : BitVec 1) == 1) = false from rfl, Bool.and_false] using
      closed.step_dispatch (delivery.framed.inputs delivery.dispatch) delivery.dispatchIdle
  have post := release_delivered delivery source related opcode valid retained generation transfer
  have response := SerialSourceReceipt.captured_fields delivery.delivered.record
    (delivery.delivered.inputs delivery.capture)
  rw [← (delivery.delivered.capture_response delivery.capture delivery.captureIdle.1 pending.capture).1] at response
  change SerialSourceRelease.Receipt (delivery.delivered.step delivery.capture).record.response delivery.request.word
  refine ⟨response.magic, ?_, response.sequence.trans pending.sequence, ?_, ?_, ?_, ?_, ?_⟩
  · rw [response.code]
    simp [Serial.responseCode,Serial.both,Expr.eval,Serial.State.values,pending.code,pending.rejected,valid]
  · rw [response.rejected,pending.rejected]
    rfl
  · rw [response.valid]
    change delivery.delivered.controller.core .valid = 1
    obtain ⟨_,_,_,_,_,installedValid⟩ := post.1
    exact installedValid
  · rw [response.busy]
    change Reactive.busy.eval (delivery.delivered.coreInputs delivery.capture) delivery.delivered.controller.core = 0
    simp [Reactive.busy,Reactive.both,Expr.eval,post.2.1]
  · rw [response.retained]
    exact post.2.2
  · rw [response.phase]
    exact post.2.1

theorem Delivery.release_source {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    {before : SerialPackage.State} (delivery : Delivery before) (source : Program.Buffered.State)
    (related : Refinement.RelatedSram program layout payload before.controller source)
    (retained : delivery.framed.controller.core .retained = 1) :
    let current := SerialSourceRead.sourceRun program source delivery.request.pins
    ∃ e outcome, current.buffers.slot = .completed ⟨e,outcome⟩ ∧
      e.request.identity = current.owner ∧
      Transfer.step Refinement.capacity current.buffers (.release current.owner) =
        ⟨{current.buffers with slot := .free},.released⟩ := by
  have frame := SerialSourceRequest.frame_source before source related delivery.request.word
    delivery.request.assert delivery.request.close delivery.request.samples delivery.request.available
    delivery.request.low delivery.request.bits delivery.request.idle
  exact SerialSourceRelease.source_release frame.2 retained

private theorem read_cursor {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {before : SerialPackage.State}
    (attempt : Attempt before) (cursor : Cursor) (held : cursor.Holds program layout before) :
    (cursor.advance program attempt.pins).Holds program layout attempt.after := by
  cases cursor with
  | free => exact SerialSourceRelease.quiet_run before held.1 held.2 attempt.pins attempt.quiet
  | owned payload source => exact SerialSourceRead.quiet_run held attempt.pins attempt.quiet

inductive Event (program : Program.Buffered.Program) :
    SerialPackage.State → Cursor → Frontend → List SerialPackage.Pins →
      SerialPackage.State → Cursor → Frontend → Type where
  | start (delivery : Delivery before)
      (opcode : delivery.request.word.extractLsb' 144 4 = 3#4)
      (starting : Reactive.starting.eval (delivery.framed.coreInputs delivery.dispatch)
        delivery.framed.controller.core = 1) :
      Event program before .free .available delivery.pins delivery.after
        (.owned (delivery.request.word.extractLsb' 0 32) (delivery.started program)) .ready
  | administrative (delivery : Delivery before) (payload : BitVec 32) (source : Program.Buffered.State)
      (opcode : SerialSourceRequest.ExecutionOpcode delivery.request.word)
      (notRelease : Reactive.releasing.eval (delivery.framed.coreInputs delivery.dispatch)
        delivery.framed.controller.core = 0) :
      Event program before (.owned payload source) .available delivery.pins delivery.after
        (.owned payload (delivery.advanced program source)) .ready
  | release (delivery : Delivery before) (payload : BitVec 32) (source : Program.Buffered.State)
      (opcode : delivery.request.word.extractLsb' 144 4 = 4#4)
      (valid : codeOf delivery.request.word = 0#4)
      (retained : delivery.framed.controller.core .retained = 1)
      (generation : delivery.request.word.extractLsb' 0 16 = delivery.framed.controller.core .generation)
      (transfer : delivery.request.word.extractLsb' 16 16 = delivery.framed.controller.core .transfer) :
      Event program before (.owned payload source) .available delivery.pins delivery.after .free .ready
  | read (attempt : Attempt before) (cursor : Cursor) (length : attempt.bits.length = 192) :
      Event program before cursor .ready attempt.pins attempt.after (cursor.advance program attempt.pins) .available
  | retry (attempt : Attempt before) (cursor : Cursor) (length : attempt.bits.length ≠ 192) :
      Event program before cursor .ready attempt.pins attempt.after (cursor.advance program attempt.pins) .ready

theorem Event.run_pins (event : Event program before cursor frontend pins after next nextFrontend) :
    before.run pins = after := by
  cases event with
  | start delivery _ _ => exact delivery.run_pins
  | administrative delivery _ _ _ _ => exact delivery.run_pins
  | release delivery _ _ _ _ _ _ _ => exact delivery.run_pins
  | read => rfl
  | retry => rfl

theorem Event.preserves {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program}
    (event : Event program before cursor frontend pins after next nextFrontend)
    (initial : Valid program layout before cursor frontend) :
    Valid program layout after next nextFrontend := by
  cases event with
  | start delivery opcode starting =>
    exact ⟨delivery.ready,start_delivery delivery initial.2.1 opcode starting⟩
  | administrative delivery payload source opcode notRelease =>
    exact ⟨delivery.ready,administrative_delivery delivery source initial.2 opcode notRelease⟩
  | release delivery payload source opcode valid retained generation transfer =>
    exact ⟨delivery.ready,release_delivery delivery source initial.2 opcode valid retained generation transfer⟩
  | read attempt cursor length => exact ⟨(attempt.exact length).1,read_cursor attempt cursor initial.2⟩
  | retry attempt cursor length => exact ⟨(attempt.retry length).1,read_cursor attempt cursor initial.2⟩

def Attempt.ExactMeaning (attempt : Attempt before) : Prop :=
  Available attempt.after.record ∧ attempt.after.record.response = before.record.response ∧
    before.readObserved attempt.pins =
      (List.range 192).map (fun k => before.record.response.getLsbD (191-k))

def Attempt.RetryMeaning (attempt : Attempt before) : Prop :=
  ReceiptReady attempt.after.record ∧ attempt.after.record.response = before.record.response

def Event.Observed (event : Event program before cursor frontend pins after next nextFrontend) : Prop :=
  match event with
  | .start delivery _ _ =>
    SerialSourceReceipt.Meaning delivery.after.record.response delivery.delivered.record
      (GenericStart.started program delivery.framed.controller.core
        (delivery.framed.coreInputs delivery.dispatch))
  | .administrative delivery _ source _ _ =>
    SerialSourceReceipt.Meaning delivery.after.record.response delivery.delivered.record
      (delivery.dispatched program source)
  | .release delivery _ source _ _ _ _ _ =>
    SerialSourceRelease.Receipt delivery.after.record.response delivery.request.word ∧
      (let current := SerialSourceRead.sourceRun program source delivery.request.pins
       ∃ e outcome, current.buffers.slot = .completed ⟨e,outcome⟩ ∧
         e.request.identity = current.owner ∧
         Transfer.step Refinement.capacity current.buffers (.release current.owner) =
           ⟨{current.buffers with slot := .free},.released⟩)
  | .read attempt _ _ => attempt.ExactMeaning
  | .retry attempt _ _ => attempt.RetryMeaning

theorem Event.observed {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program}
    (event : Event program before cursor frontend pins after next nextFrontend)
    (initial : Valid program layout before cursor frontend) : event.Observed := by
  cases event with
  | start delivery opcode starting =>
    exact delivery.start_receipt initial.2.1 opcode starting
  | administrative delivery payload source opcode notRelease =>
    exact delivery.administrative_receipt source initial.2 opcode notRelease
  | release delivery payload source opcode valid retained generation transfer =>
    exact ⟨delivery.release_receipt source initial.2 opcode valid retained generation transfer,
      delivery.release_source source initial.2 retained⟩
  | read attempt cursor length => exact attempt.exact length
  | retry attempt cursor length => exact attempt.retry length

inductive Trace (program : Program.Buffered.Program) :
    SerialPackage.State → Cursor → Frontend → List SerialPackage.Pins →
      SerialPackage.State → Cursor → Frontend → Type where
  | nil : Trace program before cursor frontend [] before cursor frontend
  | cons (event : Event program before cursor frontend first middle next nextFrontend)
      (rest : Trace program middle next nextFrontend more after final finalFrontend) :
      Trace program before cursor frontend (first ++ more) after final finalFrontend

theorem Trace.run_pins (trace : Trace program before cursor frontend pins after final finalFrontend) :
    before.run pins = after := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
    simp only [SerialPackage.State.run, List.foldl_append]
    change (SerialPackage.State.run (SerialPackage.State.run _ _) _) = _
    rw [event.run_pins]
    exact ih

theorem Trace.preserves {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program}
    (trace : Trace program before cursor frontend pins after final finalFrontend)
    (initial : Valid program layout before cursor frontend) :
    Valid program layout after final finalFrontend := by
  induction trace with
  | nil => exact initial
  | cons event rest ih => exact ih (event.preserves initial)

def Trace.Observed : Trace program before cursor frontend pins after final finalFrontend → Prop
  | .nil => True
  | .cons event rest => event.Observed ∧ rest.Observed

theorem Trace.observed {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program}
    (trace : Trace program before cursor frontend pins after final finalFrontend)
    (initial : Valid program layout before cursor frontend) : trace.Observed := by
  induction trace with
  | nil => trivial
  | cons event rest ih => exact ⟨event.observed initial,ih (event.preserves initial)⟩

/-- Any finite well-admitted wire history ending free and available is reusable.
The number of rounds, administrative frames and short-read retries is arbitrary. -/
theorem Trace.reusable {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program}
    (trace : Trace program before .free .available pins after .free .available)
    (available : Available before.record)
    (installed : Refinement.InstalledSram program layout before.controller)
    (free : SerialSourceRelease.Free before.controller) :
    before.run pins = after ∧ Available after.record ∧
      Refinement.InstalledSram program layout after.controller ∧ SerialSourceRelease.Free after.controller :=
  ⟨trace.run_pins,trace.preserves ⟨available,installed,free⟩⟩

/-- Source-grounded receipts and reusable installation for every event of an
arbitrary finite raw-wire session, including any number of partial retries. -/
theorem Trace.session {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program}
    (trace : Trace program before .free .available pins after .free .available)
    (available : Available before.record)
    (installed : Refinement.InstalledSram program layout before.controller)
    (free : SerialSourceRelease.Free before.controller) :
    before.run pins = after ∧ Available after.record ∧
      Refinement.InstalledSram program layout after.controller ∧
      SerialSourceRelease.Free after.controller ∧ trace.Observed := by
  have reusable := trace.reusable available installed free
  exact ⟨reusable.1,reusable.2.1,reusable.2.2.1,reusable.2.2.2,
    trace.observed ⟨available,installed,free⟩⟩

end Pinwheel.Hardware.Buffered.SerialSourceSession
