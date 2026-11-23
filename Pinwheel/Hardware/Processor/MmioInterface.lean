import Pinwheel.Hardware.Processor.MmioModel
import Pinwheel.Hardware.Stream.Ports

/-! Always-ready atomic operation pins; there is no response backpressure.
Device codes 0/1/2 select GPIO/timer/UART. Code 3 returns registerHole without
a CPU-requested state change; autonomous activity still occurs. It is never
decoded as a legitimate model request. Response codes: read0, stored1,
registerHole2, direction3, txBusy4, rxEmpty5. Inactive response payload/code and
inactive TX payload are zero; GPIO and TX outputs are reset masked.
-/
namespace Pinwheel.Hardware.Processor.MmioInterface

abbrev inputPorts : Hardware.Stream.Ports where
  size := 11
  widths := fun k => if k.val = 2 then 2 else if k.val = 4 then 6 else
    if k.val = 5 ∨ k.val = 6 then 32 else if k.val = 9 then 8 else 1
  names := fun k => #["reset", "request_valid", "device", "write", "word", "data",
    "gpio_input", "tx_complete", "rx_valid", "rx_data", "framing_error"][k]
  distinct := by decide +kernel

abbrev outputPorts : Hardware.Stream.Ports where
  size := 7
  widths := fun k => if k.val = 2 then 3 else if k.val = 3 ∨ k.val = 4 then 32 else
    if k.val = 6 then 8 else 1
  names := fun k => #["request_ready", "response_valid", "response_code", "response_data",
    "gpio_output", "tx_active", "tx_data"][k]
  distinct := by decide +kernel

abbrev Input := inputPorts.Signal
abbrev Output := outputPorts.Signal

def reset : Input 1 := .at ⟨0, by simp⟩
def requestValid : Input 1 := .at ⟨1, by simp⟩
def device : Input 2 := .at ⟨2, by simp⟩
def write : Input 1 := .at ⟨3, by simp⟩
def word : Input 6 := .at ⟨4, by simp⟩
def data : Input 32 := .at ⟨5, by simp⟩
def gpioInput : Input 32 := .at ⟨6, by simp⟩
def txComplete : Input 1 := .at ⟨7, by simp⟩
def rxValid : Input 1 := .at ⟨8, by simp⟩
def rxData : Input 8 := .at ⟨9, by simp⟩
def framingError : Input 1 := .at ⟨10, by simp⟩

def requestReady : Output 1 := .at ⟨0, by simp⟩
def responseValid : Output 1 := .at ⟨1, by simp⟩
def responseCode : Output 3 := .at ⟨2, by simp⟩
def responseData : Output 32 := .at ⟨3, by simp⟩
def gpioOutput : Output 32 := .at ⟨4, by simp⟩
def txActive : Output 1 := .at ⟨5, by simp⟩
def txData : Output 8 := .at ⟨6, by simp⟩

def inputs : Interface Input := inputPorts.interface
def outputs : Interface Output := outputPorts.interface

def decodeDevice (code : BitVec 2) : Option MmioModel.Device :=
  if code = 0 then some .gpio else if code = 1 then some .timer
  else if code = 2 then some .uart else none

def decode (i : Values Input) : MmioModel.Input :=
  ⟨i reset == 1,
    if i requestValid = 1 then (decodeDevice (i device)).map
      (fun d => ⟨d, i word, i write == 1, i data⟩) else none,
    i gpioInput, i txComplete == 1, if i rxValid = 1 then some (i rxData) else none,
    i framingError == 1⟩

def invalid (i : Values Input) : Prop := i requestValid = 1 ∧ decodeDevice (i device) = none
instance (i : Values Input) : Decidable (invalid i) := inferInstanceAs (Decidable (_ ∧ _))

/-- Legal-selector transport must not discard a malformed request's fault. -/
def Admitted (i : Values Input) : Prop := i reset = 1 ∨ ¬invalid i

def response (i : Values Input) (s : MmioModel.State) : Option MmioModel.Response :=
  if i reset = 1 then none else if invalid i then some (.fault .registerHole)
  else MmioModel.observe (decode i) s

def code : MmioModel.Response → BitVec 3
  | .read _ => 0 | .stored => 1
  | .fault .registerHole => 2 | .fault .direction => 3
  | .fault .txBusy => 4 | .fault .rxEmpty => 5

def payload : MmioModel.Response → BitVec 32
  | .read value => value | _ => 0

def outputValues (i : Values Input) (s : MmioModel.State) : Values Output
  | _, .at ⟨0, _⟩ => BitVec.ofBool (i reset != 1)
  | _, .at ⟨1, _⟩ => BitVec.ofBool (response i s).isSome
  | _, .at ⟨2, _⟩ => ((response i s).map code).getD 0
  | _, .at ⟨3, _⟩ => ((response i s).map payload).getD 0
  | _, .at ⟨4, _⟩ => if i reset = 1 then 0 else s.gpioOut
  | _, .at ⟨5, _⟩ => if i reset = 1 then 0 else BitVec.ofBool s.tx.isSome
  | _, .at ⟨6, _⟩ => if i reset = 1 then 0 else s.tx.getD 0
  | _, .at ⟨k+7, h⟩ => False.elim (by change k+7 < 7 at h; omega)

def spec : Timed.Component (Values Input) MmioModel.State (Values Output) where
  step i s := MmioModel.step (decode i) s
  observe := outputValues

theorem invalid_operation (i : Values Input) (h : invalid i) : (decode i).operation = none := by
  simp [decode, h.1, h.2]

theorem invalid_response (i : Values Input) (s : MmioModel.State)
    (hr : i reset ≠ 1#1) (h : invalid i) : response i s = some (.fault .registerHole) := by
  simp [response, hr, h]

theorem invalid_step (i : Values Input) (s : MmioModel.State)
    (hr : i reset ≠ 1#1) (h : invalid i) :
    spec.step i s = MmioModel.autonomous (decode i) s s := by
  simp [spec, MmioModel.step, MmioModel.cpuState, decode, hr, h.1, h.2]

theorem response_admitted (i : Values Input) (s : MmioModel.State) (h : Admitted i) :
    response i s = MmioModel.observe (decode i) s := by
  rcases h with hr | hi
  · simp [response, MmioModel.observe, decode, hr]
  · by_cases hr : i reset = 1#1 <;> simp [response, MmioModel.observe, decode, hr, hi]

end Pinwheel.Hardware.Processor.MmioInterface
