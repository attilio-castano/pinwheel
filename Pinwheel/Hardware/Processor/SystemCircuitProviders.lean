import Pinwheel.Hardware.Processor.SystemCircuitInputs

/-! Actual provider reply pins and the connected model's responses. -/
namespace Pinwheel.Hardware.Processor.SystemCircuit

set_option backward.isDefEq.respectTransparency false

variable (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

theorem ramOutput_eval (i : Values Input) (s : Values (Register aw))
    (o : Memory.ByteAdapterInterface.Output b) :
    (ramOutput layout ramFits o).eval i s =
      (Memory.ByteAdapterInterface.spec aw).observe (ramPins layout ramFits i s) (view s).ram o := by
  simp only [ramOutput, Expr.eval_bind, Expr.eval]
  exact Memory.ByteAdapterCircuit.output_eq (ramPins layout ramFits i s) (ramValues s) o

theorem ramOutput_value (i : Values Input) (s : Values (Register aw)) (hr : i reset = 0)
    (o : Memory.ByteAdapterInterface.Output b) :
    (ramOutput layout ramFits o).eval i s =
      Memory.ByteAdapterInterface.outputValues
        ⟨Memory.ByteAdapterModel.ready (view s).ram, Memory.ByteAdapterModel.offer (view s).ram⟩ o := by
  rw [ramOutput_eval]
  simp [Memory.ByteAdapterInterface.spec, Memory.ByteAdapterModel.component,
    Memory.ByteAdapterModel.machine, Stream.Machine.component,
    Memory.ByteAdapterInterface.decode, ramPins_reset, hr]

theorem mmioOutput_eval (i : Values Input) (s : Values (Register aw)) (o : MmioInterface.Output b) :
    (mmioOutput layout o).eval i s =
      MmioInterface.outputValues (mmioPins layout i s) (view s).mmio o := by
  simp only [mmioOutput, Expr.eval_bind, Expr.eval]
  exact MmioCircuit.output_eq (mmioPins layout i s) (mmioValues s) o

theorem mmio_response (i : Values Input) (s : Values (Register aw)) (hr : i reset = 0)
    (hc : CoreCircuit.Valid (coreValues s)) :
    MmioInterface.response (mmioPins layout i s) (view s).mmio =
      MmioModel.observe (SystemModel.mmioInput layout rom (decode i) (view s)) (view s).mmio := by
  rw [MmioInterface.response_admitted _ _ (mmioPins_admitted layout i s),
    mmioPins_decode layout rom i s hr hc]

theorem mmioOutput_value (i : Values Input) (s : Values (Register aw)) (hr : i reset = 0)
    (hc : CoreCircuit.Valid (coreValues s)) (o : MmioInterface.Output b) :
    (mmioOutput layout o).eval i s =
      MmioInterface.outputValues
        (SystemModelEncoding.mmioPins (SystemModel.mmioInput layout rom (decode i) (view s))) (view s).mmio o := by
  rw [mmioOutput_eval]
  have actual := mmio_response layout rom i s hr hc
  have expected := MmioInterface.response_admitted
    (SystemModelEncoding.mmioPins (SystemModel.mmioInput layout rom (decode i) (view s))) (view s).mmio
    (SystemModelEncoding.mmio_admitted _)
  rw [SystemModelEncoding.decode_mmioPins] at expected
  have actualReset : mmioPins layout i s MmioInterface.reset = 0 := by simpa using hr
  have expectedReset : SystemModelEncoding.mmioPins
      (SystemModel.mmioInput layout rom (decode i) (view s)) MmioInterface.reset = 0 := by
    simp [SystemModelEncoding.mmioPins, MmioInterface.reset, SystemModel.mmioInput, decode, hr]
  match o with
  | .at ⟨0,_⟩ | .at ⟨1,_⟩ | .at ⟨2,_⟩ | .at ⟨3,_⟩ |
    .at ⟨4,_⟩ | .at ⟨5,_⟩ | .at ⟨6,_⟩ =>
    simp [MmioInterface.outputValues, actual, expected, actualReset, expectedReset]
  | .at ⟨k+7,h⟩ => exact False.elim (by change k+7 < 7 at h; omega)

theorem corePins_dataResponse (i : Values Input) (s : Values (Register aw)) (hr : i reset = 0) :
    (CoreInterface.decode (corePins layout rom romFits ramFits i s)).dataResponse =
      (Memory.ByteAdapterModel.offer (view s).ram).map SystemModel.ramReply := by
  simp only [CoreInterface.decode, corePins, CoreInterface.dataResponseValid,
    CoreInterface.dataResponseFault, CoreInterface.dataResponseData, coreInput,
    SystemWiring.coreInput, SystemWiring.responseFault, network, Expr.eval,
    ramOutput_value layout ramFits i s hr]
  cases offered : Memory.ByteAdapterModel.offer (view s).ram with
  | none => simp [Memory.ByteAdapterInterface.outputValues, Memory.ByteAdapterInterface.responseValid]
  | some response =>
    cases response with
    | read value =>
      simp [Memory.ByteAdapterInterface.outputValues, Memory.ByteAdapterInterface.responseValid,
        Memory.ByteAdapterInterface.responseCode, Memory.ByteAdapterInterface.responseData,
        Memory.ByteAdapterInterface.code, Memory.ByteAdapterInterface.payload,
        SystemModel.ramReply, CoreInterface.reply]
    | stored =>
      simp [Memory.ByteAdapterInterface.outputValues, Memory.ByteAdapterInterface.responseValid,
        Memory.ByteAdapterInterface.responseCode, Memory.ByteAdapterInterface.responseData,
        Memory.ByteAdapterInterface.code, Memory.ByteAdapterInterface.payload,
        SystemModel.ramReply, CoreInterface.reply]
    | fault reason =>
      cases reason <;>
        simp [Memory.ByteAdapterInterface.outputValues, Memory.ByteAdapterInterface.responseValid,
          Memory.ByteAdapterInterface.responseCode,
          Memory.ByteAdapterInterface.code,
          SystemModel.ramReply, CoreInterface.reply]

theorem corePins_reset_value (i : Values Input) (s : Values (Register aw)) :
    (CoreInterface.decode (corePins layout rom romFits ramFits i s)).reset = (decode i).reset := rfl

theorem corePins_fetchReady (i : Values Input) (s : Values (Register aw)) :
    (CoreInterface.decode (corePins layout rom romFits ramFits i s)).fetchReady = true := rfl

theorem corePins_fetchResponse (i : Values Input) (s : Values (Register aw)) :
    (CoreInterface.decode (corePins layout rom romFits ramFits i s)).fetchResponse = (view s).fetch := rfl

theorem corePins_dataService_quiet (i : Values Input) (s : Values (Register aw))
    (hc : CoreCircuit.Valid (coreValues s))
    (quiet : ∀ q, (view s).core.phase ≠ .dataRequest q) :
    (CoreInterface.decode (corePins layout rom romFits ramFits i s)).dataService = none := by
  cases hp : (view s).core.phase with
  | dataRequest q => exact False.elim (quiet q hp)
  | fetchRequest | fetchResponse | execute _ | dataResponse _ | fence _ | terminal _ =>
    simp [CoreInterface.decode, CoreInterface.dataServiceValid, corePins, coreInput,
      SystemWiring.coreInput, SystemWiring.both, network, requestNetwork, Expr.eval,
      offer_eval i s hc, CoreInterface.outputValues, CoreModel.observe,
      CoreInterface.dataValid, hp]

theorem network_core_output (o : CoreInterface.Output b) :
    (network layout ramFits).coreOutputs o = offer o := rfl

theorem network_ram_output (o : Memory.ByteAdapterInterface.Output b) :
    (network layout ramFits).ramOutputs o = ramOutput layout ramFits o := rfl

theorem network_mmio_output (o : MmioInterface.Output b) :
    (network layout ramFits).mmioOutputs o = mmioOutput layout o := rfl

theorem network_route : SystemWiring.route (network layout ramFits) layout = route layout := rfl

theorem corePins_service_ram (i : Values Input) (s : Values (Register aw)) (hr : i reset = 0)
    (hv : (offer CoreInterface.dataValid).eval i s = 1)
    (routeRam : (route layout).eval i s = 1) :
    (CoreInterface.decode (corePins layout rom romFits ramFits i s)).dataService =
      if Memory.ByteAdapterModel.ready (view s).ram then some .deferred else none := by
  have ready : (ramOutput layout ramFits Memory.ByteAdapterInterface.requestReady).eval i s =
      BitVec.ofBool (Memory.ByteAdapterModel.ready (view s).ram) := by
    simpa [Memory.ByteAdapterInterface.outputValues, Memory.ByteAdapterInterface.requestReady] using
      ramOutput_value layout ramFits i s hr Memory.ByteAdapterInterface.requestReady
  simp only [CoreInterface.decode, corePins, CoreInterface.dataServiceValid,
    CoreInterface.dataServiceAtomic, coreInput, SystemWiring.coreInput, SystemWiring.both,
    SystemWiring.region, Expr.eval, network_route, network_core_output, network_ram_output,
    hv, routeRam, ready]
  cases Memory.ByteAdapterModel.ready (view s).ram <;> rfl

theorem corePins_service_mmio (i : Values Input) (s : Values (Register aw)) (hr : i reset = 0)
    (hc : CoreCircuit.Valid (coreValues s)) (hv : (offer CoreInterface.dataValid).eval i s = 1)
    (device : (route layout).eval i s = 2 ∨ (route layout).eval i s = 3 ∨ (route layout).eval i s = 4)
    (response : MmioModel.Response)
    (reply : MmioModel.observe (SystemModel.mmioInput layout rom (decode i) (view s)) (view s).mmio = some response) :
    (CoreInterface.decode (corePins layout rom romFits ramFits i s)).dataService =
      some (.atomic (SystemModel.mmioReply response)) := by
  have actual := (mmio_response layout rom i s hr hc).trans reply
  have code : (mmioOutput layout MmioInterface.responseCode).eval i s = MmioInterface.code response := by
    rw [mmioOutput_eval]
    simp [MmioInterface.outputValues, MmioInterface.responseCode, actual]
  have data : (mmioOutput layout MmioInterface.responseData).eval i s = MmioInterface.payload response := by
    rw [mmioOutput_eval]
    simp [MmioInterface.outputValues, MmioInterface.responseData, actual]
  simp only [CoreInterface.decode, corePins, CoreInterface.dataServiceValid,
    CoreInterface.dataServiceAtomic, CoreInterface.dataServiceFault, CoreInterface.dataServiceData,
    coreInput, SystemWiring.coreInput, SystemWiring.both, SystemWiring.serviceFault,
    SystemWiring.peripheral, SystemWiring.either, SystemWiring.region, Expr.eval, WordOps.wordOr_eval,
    network_route, network_core_output, network_mmio_output, hv, code, data]
  rcases device with selected | selected | selected
  all_goals cases response with
  | read value => simp [selected, MmioInterface.code, MmioInterface.payload, SystemModel.mmioReply, CoreInterface.reply]
  | stored => simp [selected, MmioInterface.code, MmioInterface.payload, SystemModel.mmioReply, CoreInterface.reply]
  | fault reason => cases reason <;>
      simp [selected, MmioInterface.code, SystemModel.mmioReply, CoreInterface.reply]

theorem corePins_service_fault (i : Values Input) (s : Values (Register aw))
    (hv : (offer CoreInterface.dataValid).eval i s = 1) (reason : AddressMap.Fault)
    (fault : (route layout).eval i s = match reason with | .misaligned => 5 | .access => 6) :
    (CoreInterface.decode (corePins layout rom romFits ramFits i s)).dataService =
      some (.atomic (SystemModel.faultReply reason)) := by
  simp only [CoreInterface.decode, corePins, CoreInterface.dataServiceValid,
    CoreInterface.dataServiceAtomic, CoreInterface.dataServiceFault, CoreInterface.dataServiceData,
    coreInput, SystemWiring.coreInput, SystemWiring.both, SystemWiring.serviceFault,
    SystemWiring.peripheral, SystemWiring.either, SystemWiring.region, Expr.eval, WordOps.wordOr_eval,
    network_route, network_core_output, hv, fault]
  cases reason <;> simp [SystemModel.faultReply, CoreInterface.reply]

end Pinwheel.Hardware.Processor.SystemCircuit
