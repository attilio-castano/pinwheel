import Pinwheel.Hardware.Buffered.SerialSourceRead

/-! Reusable raw-wire witnesses for one sampled request, real dispatch and
capture edges, and an exact response read. No decoded command trace or live
status equality is a premise. Controller clocks include every sampled edge. -/
namespace Pinwheel.Hardware.Buffered.SerialWire
open Pinwheel.Hardware Serial.Frames

structure Request (before : SerialPackage.State) where
  word : BitVec 160
  assert : SerialPackage.Pins
  close : SerialPackage.Pins
  samples : List SerialPackage.Pins
  available : Available before.record
  low : Low (before.inputs assert)
  bits : IsBits (wordBits word) ((before.step assert).frontendInputs samples)
  idle : close.cold = false ∧ close.csn = true

def Request.pins (request : Request before) : List SerialPackage.Pins :=
  request.assert :: (request.samples ++ [request.close])
def Request.framed (request : Request before) : SerialPackage.State := before.run request.pins

theorem Request.closed (request : Request before) : Closed request.word request.framed.record :=
  before.frame_closed request.word request.assert request.close request.samples
    request.available request.low request.bits request.idle

theorem Request.quiet (request : Request before) :
    ∀ input ∈ before.commands request.pins, SpiCircuit.Quiet input :=
  before.frame_quiet request.word request.assert request.close request.samples
    request.available request.low request.bits request.idle

structure Read (before : SerialPackage.State) where
  assert : SerialPackage.Pins
  close : SerialPackage.Pins
  bits : List Bool
  samples : List SerialPackage.Pins
  low : Low (before.inputs assert)
  wire : IsBits bits ((before.step assert).frontendInputs samples)
  idle : close.cold = false ∧ close.csn = true
  length : bits.length = 192

def Read.pins (read : Read before) : List SerialPackage.Pins := read.assert :: (read.samples ++ [read.close])
def Read.after (read : Read before) : SerialPackage.State := before.run read.pins

theorem Read.exact (read : Read before) (ready : ReceiptReady before.record) :
    Available read.after.record ∧ read.after.record.response = before.record.response ∧
      before.readObserved read.pins =
        (List.range 192).map (fun k => before.record.response.getLsbD (191-k)) :=
  before.receipt_exact_read read.assert read.close read.bits read.samples ready
    read.low read.wire read.idle read.length

theorem Read.quiet (read : Read before) (ready : ReceiptReady before.record) :
    ∀ input ∈ before.commands read.pins, SpiCircuit.Quiet input :=
  before.receipt_read_quiet read.assert read.close read.bits read.samples ready read.low read.wire read.idle

structure Transaction (before : SerialPackage.State) where
  request : Request before
  dispatch : SerialPackage.Pins
  capture : SerialPackage.Pins
  dispatchIdle : dispatch.cold = false ∧ dispatch.csn = true
  captureIdle : capture.cold = false ∧ capture.csn = true
  read : Read ((request.framed.step dispatch).step capture)

def Transaction.framed (transaction : Transaction before) : SerialPackage.State := transaction.request.framed
def Transaction.delivered (transaction : Transaction before) : SerialPackage.State :=
  transaction.framed.step transaction.dispatch
def Transaction.captured (transaction : Transaction before) : SerialPackage.State :=
  transaction.delivered.step transaction.capture
def Transaction.after (transaction : Transaction before) : SerialPackage.State := transaction.read.after

def Transaction.pins (transaction : Transaction before) : List SerialPackage.Pins :=
  transaction.request.pins ++ transaction.dispatch :: transaction.capture :: transaction.read.pins

def Transaction.rejection (transaction : Transaction before) : Bool :=
  (codeOf transaction.request.word == 0) &&
    (transaction.framed.status transaction.dispatch .rejected == 1)

theorem Transaction.run_pins (transaction : Transaction before) :
    before.run transaction.pins = transaction.after := by
  simp only [Transaction.pins, SerialPackage.State.run, List.foldl_append, List.foldl_cons]
  rfl

theorem Transaction.capturing (transaction : Transaction before) :
    Capturing transaction.request.word transaction.rejection transaction.delivered.record := by
  rw [Transaction.delivered, transaction.framed.record_step]
  exact transaction.request.closed.step_dispatch
    (transaction.framed.inputs transaction.dispatch) transaction.dispatchIdle

theorem Transaction.ready (transaction : Transaction before) : ReceiptReady transaction.captured.record := by
  rw [Transaction.captured, transaction.delivered.record_step]
  exact (transaction.capturing.step_capture
    (transaction.delivered.inputs transaction.capture) transaction.captureIdle).1

theorem Transaction.capture_quiet (transaction : Transaction before) :
    SpiCircuit.Quiet (transaction.delivered.coreInputs transaction.capture) :=
  SerialSourceRead.core_quiet transaction.delivered transaction.capture
    transaction.captureIdle.1 transaction.capturing.dispatch

theorem Transaction.read_quiet (transaction : Transaction before) :
    ∀ input ∈ transaction.captured.commands transaction.read.pins, SpiCircuit.Quiet input :=
  transaction.read.quiet transaction.ready

theorem Transaction.exact (transaction : Transaction before) :
    Available transaction.after.record ∧
      transaction.after.record.response = transaction.captured.record.response ∧
      transaction.captured.readObserved transaction.read.pins =
        (List.range 192).map (fun k => transaction.captured.record.response.getLsbD (191-k)) :=
  transaction.read.exact transaction.ready

end Pinwheel.Hardware.Buffered.SerialWire
