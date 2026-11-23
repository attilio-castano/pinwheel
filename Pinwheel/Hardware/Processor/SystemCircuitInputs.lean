import Pinwheel.Hardware.Processor.SystemCircuitState
import Pinwheel.Hardware.Processor.SystemModelEncoding
import Pinwheel.Hardware.Processor.SystemAddressProofs

/-! Connected-system refinement. The typed observation includes the MMIO
response ports in addition to the core, GPIO and TX observables of SystemModel.
Its transition is exactly the frozen connected model transition. -/
namespace Pinwheel.Hardware.Processor.SystemCircuit

set_option backward.isDefEq.respectTransparency false

variable (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

def logicalOutputs (i : SystemModel.Input) (s : SystemModel.State aw) : Values Output :=
  Stream.Joint.values
    (CoreInterface.outputValues (SystemModelEncoding.corePins (SystemModel.coreInput layout rom i s)) s.core)
    (MmioInterface.outputValues (SystemModelEncoding.mmioPins (SystemModel.mmioInput layout rom i s)) s.mmio)

def spec : Timed.Component (Values Input) (SystemModel.State aw) (Values Output) where
  step i s := SystemModel.step layout rom (decode i) s
  observe i s := logicalOutputs layout rom (decode i) s

/-- Literal-zero response pins used only to elaborate the request network.
No response-dependent retirement output is consumed by this network. -/
def requestPins (i : Values Input) : Values CoreInterface.Input
  | _, .at ⟨0,_⟩ => i reset
  | _, .at _ => 0

theorem requestInput_eval (i : Values Input) (s : Values (Register aw)) (p : CoreInterface.Input b) :
    (requestInput p).eval i s = requestPins i p := by
  match p with | .at ⟨0,_⟩ | .at ⟨k+1,_⟩ => rfl

theorem requestPins_decode (i : Values Input) :
    CoreInterface.decode (requestPins i) = {reset := (decode i).reset} := rfl

theorem offer_eval (i : Values Input) (s : Values (Register aw))
    (h : CoreCircuit.Valid (coreValues s)) (o : CoreInterface.Output b) :
    (offer o).eval i s = CoreInterface.outputValues (requestPins i) (view s).core o := by
  simp only [offer, Expr.eval_bind, requestInput_eval, Expr.eval]
  exact CoreCircuit.output_eq (requestPins i) (coreValues s) h o

theorem ramPins_decode_quiet (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (quiet : ∀ q, (view s).core.phase ≠ .dataRequest q) :
    Memory.ByteAdapterInterface.decode (ramPins layout ramFits i s) =
      SystemModel.ramInput layout rom (decode i) (view s) := by
  cases hp : (view s).core.phase with
  | dataRequest q => exact False.elim (quiet q hp)
  | fetchRequest | fetchResponse | execute _ | dataResponse _ | fence _ | terminal _ =>
    simp [Memory.ByteAdapterInterface.decode, ramPins, ramInput, SystemWiring.ramInput,
      SystemWiring.both, requestNetwork, Expr.eval,
      offer_eval i s hc, CoreInterface.outputValues, CoreModel.observe, requestPins_decode,
      CoreInterface.dataValid, CoreInterface.dataResponseReady, Memory.ByteAdapterInterface.reset,
      Memory.ByteAdapterInterface.requestValid, Memory.ByteAdapterInterface.responseReady,
      SystemModel.ramInput, SystemModel.pendingPlan, decode, hr, hp]

theorem offer_load_routing (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (c : RV32I.Semantics.Context) (op : RV32I.LoadOp) (dest : RV32I.Register) (address : BitVec 32)
    (hp : (view s).core.phase = .dataRequest (.load c op dest address)) :
    (offer CoreInterface.dataWrite).eval i s = 0 ∧
    (offer CoreInterface.dataSize).eval i s = SystemModel.sizeCode (RV32I.Semantics.loadSize op) ∧
    (offer CoreInterface.dataAddress).eval i s = address := by
  simp only [offer_eval i s hc]
  cases op <;>
    simp [CoreInterface.outputValues, CoreModel.observe, requestPins_decode, decode, hr, hp,
      CoreInterface.dataWrite, CoreInterface.dataSize, CoreInterface.dataAddress,
      CoreModel.DataRequest.intent, CoreModel.DataRequest.pending, RV32I.Semantics.Pending.intent,
      RV32I.Semantics.loadSize, SystemModel.sizeCode]
  all_goals rfl

theorem offer_store_routing (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (c : RV32I.Semantics.Context) (op : RV32I.StoreOp) (address data : BitVec 32)
    (hp : (view s).core.phase = .dataRequest (.store c op address data)) :
    (offer CoreInterface.dataWrite).eval i s = 1 ∧
    (offer CoreInterface.dataSize).eval i s = SystemModel.sizeCode (RV32I.Semantics.storeSize op) ∧
    (offer CoreInterface.dataAddress).eval i s = address := by
  simp only [offer_eval i s hc]
  cases op <;>
    simp [CoreInterface.outputValues, CoreModel.observe, requestPins_decode, decode, hr, hp,
      CoreInterface.dataWrite, CoreInterface.dataSize, CoreInterface.dataAddress,
      CoreModel.DataRequest.intent, CoreModel.DataRequest.pending, RV32I.Semantics.Pending.intent,
      RV32I.Semantics.storeSize, SystemModel.sizeCode]
  all_goals rfl

theorem route_load (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (c : RV32I.Semantics.Context) (op : RV32I.LoadOp) (dest : RV32I.Register) (address : BitVec 32)
    (hp : (view s).core.phase = .dataRequest (.load c op dest address)) :
    (route layout).eval i s = AddressDecode.routeCode
      (AddressMap.route layout ⟨.load, RV32I.Semantics.loadSize op, address⟩) := by
  obtain ⟨hw, hz, ha⟩ := offer_load_routing i s hr hc c op dest address hp
  simp only [route, SystemWiring.route, AddressDecode.runtime_eval, requestNetwork, Expr.eval, hw, hz, ha]
  cases op <;> rfl

theorem route_store (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (c : RV32I.Semantics.Context) (op : RV32I.StoreOp) (address data : BitVec 32)
    (hp : (view s).core.phase = .dataRequest (.store c op address data)) :
    (route layout).eval i s = AddressDecode.routeCode
      (AddressMap.route layout ⟨.store, RV32I.Semantics.storeSize op, address⟩) := by
  obtain ⟨hw, hz, ha⟩ := offer_store_routing i s hr hc c op address data hp
  simp only [route, SystemWiring.route, AddressDecode.runtime_eval, requestNetwork, Expr.eval, hw, hz, ha]
  cases op <;> rfl

theorem offer_load_control (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (c : RV32I.Semantics.Context) (op : RV32I.LoadOp) (dest : RV32I.Register) (address : BitVec 32)
    (hp : (view s).core.phase = .dataRequest (.load c op dest address)) :
    (offer CoreInterface.dataValid).eval i s = 1 ∧
    (offer CoreInterface.dataSigned).eval i s = BitVec.ofBool (RV32I.Semantics.loadSigned op) ∧
    (offer CoreInterface.dataStoreData).eval i s = 0 ∧
    (offer CoreInterface.dataResponseReady).eval i s = 0 := by
  simp only [offer_eval i s hc]
  cases op <;>
    simp [CoreInterface.outputValues, CoreModel.observe, requestPins_decode, decode, hr, hp,
      CoreInterface.dataValid, CoreInterface.dataSigned, CoreInterface.dataStoreData, CoreInterface.dataResponseReady,
      CoreModel.DataRequest.intent, CoreModel.DataRequest.pending, RV32I.Semantics.Pending.intent,
      RV32I.Semantics.loadSigned]
  all_goals rfl

theorem offer_store_control (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (c : RV32I.Semantics.Context) (op : RV32I.StoreOp) (address data : BitVec 32)
    (hp : (view s).core.phase = .dataRequest (.store c op address data)) :
    (offer CoreInterface.dataValid).eval i s = 1 ∧
    (offer CoreInterface.dataSigned).eval i s = 0 ∧
    (offer CoreInterface.dataStoreData).eval i s = data ∧
    (offer CoreInterface.dataResponseReady).eval i s = 0 := by
  simp only [offer_eval i s hc]
  simp [CoreInterface.outputValues, CoreModel.observe, requestPins_decode, decode, hr, hp,
    CoreInterface.dataValid, CoreInterface.dataSigned, CoreInterface.dataStoreData, CoreInterface.dataResponseReady,
    CoreModel.DataRequest.intent, CoreModel.DataRequest.pending, RV32I.Semantics.Pending.intent]

theorem ramPins_decode_load (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (c : RV32I.Semantics.Context) (op : RV32I.LoadOp) (dest : RV32I.Register) (address : BitVec 32)
    (hp : (view s).core.phase = .dataRequest (.load c op dest address)) :
    Memory.ByteAdapterInterface.decode (ramPins layout ramFits i s) =
      SystemModel.ramInput layout rom (decode i) (view s) := by
  obtain ⟨hw, hz, ha⟩ := offer_load_routing i s hr hc c op dest address hp
  obtain ⟨hv, hs, hd, hready⟩ := offer_load_control i s hr hc c op dest address hp
  have routedExpr := route_load layout i s hr hc c op dest address hp
  dsimp only [route] at routedExpr
  cases routed : AddressMap.route layout ⟨.load, RV32I.Semantics.loadSize op, address⟩ with
  | error reason =>
    cases reason <;>
      simp_all [Memory.ByteAdapterInterface.decode, Memory.ByteAdapterInterface.reset,
        Memory.ByteAdapterInterface.requestValid, Memory.ByteAdapterInterface.responseReady,
        ramPins, ramInput, SystemWiring.ramInput, SystemWiring.both, SystemWiring.region,
        requestNetwork, Expr.eval, AddressDecode.routeCode, SystemModel.ramInput,
        SystemModel.pendingPlan, SystemModel.plan, CoreModel.DataRequest.intent,
        CoreModel.DataRequest.pending, RV32I.Semantics.Pending.intent, decode]
  | ok hit =>
    have word := hit.word_slice_width aw
    have offset := hit.offset_slice
    cases region : hit.region <;>
      simp_all [Memory.ByteAdapterInterface.decode, Memory.ByteAdapterInterface.request,
        Memory.ByteAdapterInterface.reset, Memory.ByteAdapterInterface.requestValid,
        Memory.ByteAdapterInterface.write, Memory.ByteAdapterInterface.signed,
        Memory.ByteAdapterInterface.size, Memory.ByteAdapterInterface.address,
        Memory.ByteAdapterInterface.offset,
        Memory.ByteAdapterInterface.responseReady, ramPins, ramInput, SystemWiring.ramInput,
        SystemWiring.both, SystemWiring.region, SystemWiring.localAddress, requestNetwork,
        Expr.eval, AddressDecode.routeCode, AddressDecode.regionCode, AddressMap.Config.base,
        BitVec.ofNat_toNat,
        SystemModel.ramInput, SystemModel.pendingPlan, SystemModel.plan, CoreModel.DataRequest.intent,
        CoreModel.DataRequest.pending, RV32I.Semantics.Pending.intent, decode]
    cases RV32I.Semantics.loadSigned op <;> rfl

theorem ramPins_decode_store (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (c : RV32I.Semantics.Context) (op : RV32I.StoreOp) (address data : BitVec 32)
    (hp : (view s).core.phase = .dataRequest (.store c op address data)) :
    Memory.ByteAdapterInterface.decode (ramPins layout ramFits i s) =
      SystemModel.ramInput layout rom (decode i) (view s) := by
  obtain ⟨hw, hz, ha⟩ := offer_store_routing i s hr hc c op address data hp
  obtain ⟨hv, hs, hd, hready⟩ := offer_store_control i s hr hc c op address data hp
  have routedExpr := route_store layout i s hr hc c op address data hp
  dsimp only [route] at routedExpr
  cases routed : AddressMap.route layout ⟨.store, RV32I.Semantics.storeSize op, address⟩ with
  | error reason =>
    cases reason <;>
      simp_all [Memory.ByteAdapterInterface.decode, Memory.ByteAdapterInterface.reset,
        Memory.ByteAdapterInterface.requestValid, Memory.ByteAdapterInterface.responseReady,
        ramPins, ramInput, SystemWiring.ramInput, SystemWiring.both, SystemWiring.region,
        requestNetwork, Expr.eval, AddressDecode.routeCode, SystemModel.ramInput,
        SystemModel.pendingPlan, SystemModel.plan, CoreModel.DataRequest.intent,
        CoreModel.DataRequest.pending, RV32I.Semantics.Pending.intent, decode]
  | ok hit =>
    have word := hit.word_slice_width aw
    have offset := hit.offset_slice
    cases region : hit.region <;>
      simp_all [Memory.ByteAdapterInterface.decode, Memory.ByteAdapterInterface.request,
        Memory.ByteAdapterInterface.reset, Memory.ByteAdapterInterface.requestValid,
        Memory.ByteAdapterInterface.write, Memory.ByteAdapterInterface.data,
        Memory.ByteAdapterInterface.size, Memory.ByteAdapterInterface.address,
        Memory.ByteAdapterInterface.offset,
        Memory.ByteAdapterInterface.responseReady, ramPins, ramInput, SystemWiring.ramInput,
        SystemWiring.both, SystemWiring.region, SystemWiring.localAddress, requestNetwork,
        Expr.eval, AddressDecode.routeCode, AddressDecode.regionCode, AddressMap.Config.base,
        BitVec.ofNat_toNat,
        SystemModel.ramInput, SystemModel.pendingPlan, SystemModel.plan, CoreModel.DataRequest.intent,
        CoreModel.DataRequest.pending, RV32I.Semantics.Pending.intent, decode]

theorem ramPins_decode (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s)) :
    Memory.ByteAdapterInterface.decode (ramPins layout ramFits i s) =
      SystemModel.ramInput layout rom (decode i) (view s) := by
  by_cases active : ∃ q, (view s).core.phase = .dataRequest q
  · obtain ⟨q, hp⟩ := active
    cases q with
    | load c op dest address => exact ramPins_decode_load layout rom ramFits i s hr hc c op dest address hp
    | store c op address data => exact ramPins_decode_store layout rom ramFits i s hr hc c op address data hp
  · exact ramPins_decode_quiet layout rom ramFits i s hr hc (fun q hp => active ⟨q,hp⟩)

theorem mmioPins_decode_quiet (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (quiet : ∀ q, (view s).core.phase ≠ .dataRequest q) :
    MmioInterface.decode (mmioPins layout i s) =
      SystemModel.mmioInput layout rom (decode i) (view s) := by
  cases hp : (view s).core.phase with
  | dataRequest q => exact False.elim (quiet q hp)
  | fetchRequest | fetchResponse | execute _ | dataResponse _ | fence _ | terminal _ =>
    simp [MmioInterface.decode, mmioPins, mmioInput, SystemWiring.mmioInput,
      SystemWiring.both, requestNetwork, Expr.eval,
      offer_eval i s hc, CoreInterface.outputValues, CoreModel.observe, requestPins_decode,
      CoreInterface.dataValid, MmioInterface.reset, MmioInterface.requestValid,
      MmioInterface.gpioInput, MmioInterface.txComplete, MmioInterface.rxValid,
      MmioInterface.rxData, MmioInterface.framingError,
      SystemModel.mmioInput, SystemModel.pendingPlan, decode, hr, hp]

theorem mmioPins_decode_load (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (c : RV32I.Semantics.Context) (op : RV32I.LoadOp) (dest : RV32I.Register) (address : BitVec 32)
    (hp : (view s).core.phase = .dataRequest (.load c op dest address)) :
    MmioInterface.decode (mmioPins layout i s) =
      SystemModel.mmioInput layout rom (decode i) (view s) := by
  obtain ⟨hw, hz, ha⟩ := offer_load_routing i s hr hc c op dest address hp
  obtain ⟨hv, hs, hd, hready⟩ := offer_load_control i s hr hc c op dest address hp
  have routedExpr := route_load layout i s hr hc c op dest address hp
  dsimp only [route] at routedExpr
  cases routed : AddressMap.route layout ⟨.load, RV32I.Semantics.loadSize op, address⟩ with
  | error reason =>
    cases reason <;>
      simp_all [MmioInterface.decode, MmioInterface.reset, MmioInterface.requestValid,
        MmioInterface.gpioInput, MmioInterface.txComplete, MmioInterface.rxValid,
        MmioInterface.rxData, MmioInterface.framingError, mmioPins, mmioInput,
        SystemWiring.mmioInput, SystemWiring.both, SystemWiring.region,
        SystemWiring.peripheral, SystemWiring.either, WordOps.wordOr_eval,
        requestNetwork, Expr.eval, AddressDecode.routeCode, SystemModel.mmioInput,
        SystemModel.pendingPlan, SystemModel.plan, CoreModel.DataRequest.intent,
        CoreModel.DataRequest.pending, RV32I.Semantics.Pending.intent, decode]
  | ok hit =>
    have word := hit.word_slice_width 6
    cases region : hit.region <;>
      simp_all [MmioInterface.decode, MmioInterface.decodeDevice,
        MmioInterface.reset, MmioInterface.requestValid, MmioInterface.device,
        MmioInterface.write, MmioInterface.word, MmioInterface.data,
        MmioInterface.gpioInput, MmioInterface.txComplete, MmioInterface.rxValid,
        MmioInterface.rxData, MmioInterface.framingError, mmioPins, mmioInput,
        SystemWiring.mmioInput, SystemWiring.both, SystemWiring.region,
        SystemWiring.peripheral, SystemWiring.either, WordOps.wordOr_eval,
        SystemWiring.peripheralBase, requestNetwork, Expr.eval, AddressDecode.routeCode,
        AddressDecode.regionCode, AddressMap.Config.base, BitVec.ofNat_toNat,
        SystemModel.mmioInput, SystemModel.pendingPlan, SystemModel.plan, CoreModel.DataRequest.intent,
        CoreModel.DataRequest.pending, RV32I.Semantics.Pending.intent, decode]

theorem mmioPins_decode_store (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (c : RV32I.Semantics.Context) (op : RV32I.StoreOp) (address data : BitVec 32)
    (hp : (view s).core.phase = .dataRequest (.store c op address data)) :
    MmioInterface.decode (mmioPins layout i s) =
      SystemModel.mmioInput layout rom (decode i) (view s) := by
  obtain ⟨hw, hz, ha⟩ := offer_store_routing i s hr hc c op address data hp
  obtain ⟨hv, hs, hd, hready⟩ := offer_store_control i s hr hc c op address data hp
  have routedExpr := route_store layout i s hr hc c op address data hp
  dsimp only [route] at routedExpr
  cases routed : AddressMap.route layout ⟨.store, RV32I.Semantics.storeSize op, address⟩ with
  | error reason =>
    cases reason <;>
      simp_all [MmioInterface.decode, MmioInterface.reset, MmioInterface.requestValid,
        MmioInterface.gpioInput, MmioInterface.txComplete, MmioInterface.rxValid,
        MmioInterface.rxData, MmioInterface.framingError, mmioPins, mmioInput,
        SystemWiring.mmioInput, SystemWiring.both, SystemWiring.region,
        SystemWiring.peripheral, SystemWiring.either, WordOps.wordOr_eval,
        requestNetwork, Expr.eval, AddressDecode.routeCode, SystemModel.mmioInput,
        SystemModel.pendingPlan, SystemModel.plan, CoreModel.DataRequest.intent,
        CoreModel.DataRequest.pending, RV32I.Semantics.Pending.intent, decode]
  | ok hit =>
    have word := hit.word_slice_width 6
    cases region : hit.region <;>
      simp_all [MmioInterface.decode, MmioInterface.decodeDevice,
        MmioInterface.reset, MmioInterface.requestValid, MmioInterface.device,
        MmioInterface.write, MmioInterface.word, MmioInterface.data,
        MmioInterface.gpioInput, MmioInterface.txComplete, MmioInterface.rxValid,
        MmioInterface.rxData, MmioInterface.framingError, mmioPins, mmioInput,
        SystemWiring.mmioInput, SystemWiring.both, SystemWiring.region,
        SystemWiring.peripheral, SystemWiring.either, WordOps.wordOr_eval,
        SystemWiring.peripheralBase, requestNetwork, Expr.eval, AddressDecode.routeCode,
        AddressDecode.regionCode, AddressMap.Config.base, BitVec.ofNat_toNat,
        SystemModel.mmioInput, SystemModel.pendingPlan, SystemModel.plan, CoreModel.DataRequest.intent,
        CoreModel.DataRequest.pending, RV32I.Semantics.Pending.intent, decode]

theorem mmioPins_decode (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s)) :
    MmioInterface.decode (mmioPins layout i s) =
      SystemModel.mmioInput layout rom (decode i) (view s) := by
  by_cases active : ∃ q, (view s).core.phase = .dataRequest q
  · obtain ⟨q, hp⟩ := active
    cases q with
    | load c op dest address => exact mmioPins_decode_load layout rom i s hr hc c op dest address hp
    | store c op address data => exact mmioPins_decode_store layout rom i s hr hc c op address data hp
  · exact mmioPins_decode_quiet layout rom i s hr hc (fun q hp => active ⟨q,hp⟩)

theorem mmioPins_admitted (i : Values Input) (s : Values (Register aw)) :
    MmioInterface.Admitted (mmioPins layout i s) := by
  apply Or.inr
  intro invalid
  have absent := invalid.2
  simp only [mmioPins, MmioInterface.device, mmioInput, SystemWiring.mmioInput, Expr.eval] at absent
  split at absent <;> simp_all [MmioInterface.decodeDevice]
  split at absent <;> simp_all

end Pinwheel.Hardware.Processor.SystemCircuit
