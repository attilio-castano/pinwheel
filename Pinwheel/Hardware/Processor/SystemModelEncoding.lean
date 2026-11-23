import Pinwheel.Hardware.Processor.SystemModel
import Pinwheel.Hardware.Processor.CoreInterface
import Pinwheel.Hardware.Processor.MmioInterface

/-! Canonical pin encodings for the connected model's pure component inputs.
Inactive payload choices are explicit zeroes; decoding recovers each input. -/
namespace Pinwheel.Hardware.Processor.SystemModelEncoding

open CoreModel

def faultCode : DataReply → BitVec 2
  | .success _ => 0 | .fault .misaligned => 1 | .fault .accessFault => 2

def replyData : DataReply → BitVec 32
  | .success value => value | .fault _ => 0

def serviceReply : DataService → DataReply
  | .deferred => .success 0 | .atomic reply => reply

def corePins (i : CoreModel.Input) : Values CoreInterface.Input
  | _, .at ⟨0,_⟩ => BitVec.ofBool i.reset
  | _, .at ⟨1,_⟩ => BitVec.ofBool i.fetchReady
  | _, .at ⟨2,_⟩ => BitVec.ofBool i.fetchResponse.isSome
  | _, .at ⟨3,_⟩ => BitVec.ofBool (i.fetchResponse matches some .accessFault)
  | _, .at ⟨4,_⟩ => match i.fetchResponse with | some (.instruction word) => word | _ => 0
  | _, .at ⟨5,_⟩ => BitVec.ofBool i.dataService.isSome
  | _, .at ⟨6,_⟩ => BitVec.ofBool (i.dataService matches some (.atomic _))
  | _, .at ⟨7,_⟩ => ((i.dataService.map serviceReply).map faultCode).getD 0
  | _, .at ⟨8,_⟩ => ((i.dataService.map serviceReply).map replyData).getD 0
  | _, .at ⟨9,_⟩ => BitVec.ofBool i.dataResponse.isSome
  | _, .at ⟨10,_⟩ => (i.dataResponse.map faultCode).getD 0
  | _, .at ⟨11,_⟩ => (i.dataResponse.map replyData).getD 0
  | _, .at ⟨k+12,h⟩ => False.elim (by change k+12 < 12 at h; omega)

@[simp] theorem decode_corePins (i : CoreModel.Input) : CoreInterface.decode (corePins i) = i := by
  rcases i with ⟨reset, fetchReady, fetchResponse, dataService, dataResponse⟩
  simp only [CoreInterface.decode, corePins, CoreInterface.reset, CoreInterface.fetchReady,
    CoreInterface.fetchResponseValid, CoreInterface.fetchResponseFault, CoreInterface.fetchResponseData,
    CoreInterface.dataServiceValid, CoreInterface.dataServiceAtomic, CoreInterface.dataServiceFault,
    CoreInterface.dataServiceData, CoreInterface.dataResponseValid, CoreInterface.dataResponseFault,
    CoreInterface.dataResponseData]
  congr 1
  · cases reset <;> rfl
  · cases fetchReady <;> rfl
  · cases fetchResponse with
    | none => rfl
    | some response => cases response <;> rfl
  · cases dataService with
    | none => rfl
    | some service => cases service with
      | deferred => rfl
      | atomic reply => cases reply with
        | success value => rfl
        | fault reason => cases reason <;> rfl
  · cases dataResponse with
    | none => rfl
    | some reply => cases reply with
      | success value => rfl
      | fault reason => cases reason <;> rfl

def deviceCode : MmioModel.Device → BitVec 2
  | .gpio => 0 | .timer => 1 | .uart => 2

def mmioPins (i : MmioModel.Input) : Values MmioInterface.Input
  | _, .at ⟨0,_⟩ => BitVec.ofBool i.reset
  | _, .at ⟨1,_⟩ => BitVec.ofBool i.operation.isSome
  | _, .at ⟨2,_⟩ => (i.operation.map (fun r => deviceCode r.device)).getD 0
  | _, .at ⟨3,_⟩ => BitVec.ofBool ((i.operation.map MmioModel.Request.write).getD false)
  | _, .at ⟨4,_⟩ => (i.operation.map MmioModel.Request.word).getD 0
  | _, .at ⟨5,_⟩ => (i.operation.map MmioModel.Request.data).getD 0
  | _, .at ⟨6,_⟩ => i.gpioInput
  | _, .at ⟨7,_⟩ => BitVec.ofBool i.txComplete
  | _, .at ⟨8,_⟩ => BitVec.ofBool i.rxArrival.isSome
  | _, .at ⟨9,_⟩ => i.rxArrival.getD 0
  | _, .at ⟨10,_⟩ => BitVec.ofBool i.framingError
  | _, .at ⟨k+11,h⟩ => False.elim (by change k+11 < 11 at h; omega)

@[simp] theorem decode_mmioPins (i : MmioModel.Input) : MmioInterface.decode (mmioPins i) = i := by
  rcases i with ⟨reset,operation,gpioInput,txComplete,rxArrival,framingError⟩
  simp only [MmioInterface.decode, mmioPins, MmioInterface.reset, MmioInterface.requestValid,
    MmioInterface.device, MmioInterface.write, MmioInterface.word, MmioInterface.data,
    MmioInterface.gpioInput, MmioInterface.txComplete, MmioInterface.rxValid,
    MmioInterface.rxData, MmioInterface.framingError]
  congr 1
  · cases reset <;> rfl
  · cases operation with
    | none => rfl
    | some request => cases request with
      | mk device word write data => cases device <;> cases write <;> rfl
  · cases txComplete <;> rfl
  · cases rxArrival <;> rfl
  · cases framingError <;> rfl

theorem mmio_admitted (i : MmioModel.Input) : MmioInterface.Admitted (mmioPins i) := by
  apply Or.inr
  cases h : i.operation with
  | none => simp [MmioInterface.invalid, mmioPins, MmioInterface.requestValid, h]
  | some request =>
    cases hd : request.device <;>
      simp [MmioInterface.invalid, mmioPins, MmioInterface.requestValid,
        MmioInterface.device, MmioInterface.decodeDevice, deviceCode, h, hd]

theorem core_outputs_congr (i j : Values CoreInterface.Input) (s : CoreModel.State)
    (h : CoreInterface.decode i = CoreInterface.decode j) :
    @Eq (Values CoreInterface.Output) (CoreInterface.outputValues i s) (CoreInterface.outputValues j s) := by
  unfold CoreInterface.outputValues
  rw [h]

end Pinwheel.Hardware.Processor.SystemModelEncoding
