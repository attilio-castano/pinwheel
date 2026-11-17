import Pinwheel.Hardware.Processor.SystemCircuitRom

/-! The actual connected core input agrees with its model input. Atomic
ROM/device/fault service and deferred RAM ownership remain distinct. -/
namespace Pinwheel.Hardware.Processor.SystemCircuit

set_option backward.isDefEq.respectTransparency false

variable (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

theorem corePins_service_mmio_plan (i : Values Input) (s : Values (Register aw)) (hr : i reset = 0)
    (hc : CoreCircuit.Valid (coreValues s)) (hv : (offer CoreInterface.dataValid).eval i s = 1)
    (device : (route layout).eval i s = 2 ∨ (route layout).eval i s = 3 ∨ (route layout).eval i s = 4)
    (request : MmioModel.Request)
    (plan : SystemModel.pendingPlan layout rom (view s) = some (.mmio request)) :
    (CoreInterface.decode (corePins layout rom romFits ramFits i s)).dataService =
      (SystemModel.coreInput layout rom (decode i) (view s)).dataService := by
  have reply : MmioModel.observe (SystemModel.mmioInput layout rom (decode i) (view s)) (view s).mmio =
      some (MmioModel.access (decode i).gpio request (view s).mmio).1 := by
    simp [MmioModel.observe, SystemModel.mmioInput, plan, decode, hr]
  rw [corePins_service_mmio layout rom romFits ramFits i s hr hc hv device _ reply]
  simp only [SystemModel.coreInput, plan, reply, Option.map_some]

theorem corePins_dataService_load (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (c : RV32I.Semantics.Context) (op : RV32I.LoadOp) (dest : RV32I.Register) (address : BitVec 32)
    (hp : (view s).core.phase = .dataRequest (.load c op dest address)) :
    (CoreInterface.decode (corePins layout rom romFits ramFits i s)).dataService =
      (SystemModel.coreInput layout rom (decode i) (view s)).dataService := by
  have hv := (offer_load_control i s hr hc c op dest address hp).1
  have routedExpr := route_load layout i s hr hc c op dest address hp
  have planned : SystemModel.pendingPlan layout rom (view s) =
      some (SystemModel.plan layout rom (.load address (RV32I.Semantics.loadSize op) (RV32I.Semantics.loadSigned op))) := by
    simp [SystemModel.pendingPlan, hp, CoreModel.DataRequest.intent, CoreModel.DataRequest.pending, RV32I.Semantics.Pending.intent]
  cases routed : AddressMap.route layout ⟨.load, RV32I.Semantics.loadSize op, address⟩ with
  | error reason =>
    rw [corePins_service_fault layout rom romFits ramFits i s hv reason (by
      cases reason <;> simpa [routed, AddressDecode.routeCode] using routedExpr)]
    simp [SystemModel.coreInput, planned, SystemModel.plan, routed]
  | ok hit =>
    cases region : hit.region with
    | rom =>
      rw [corePins_service_rom layout rom romFits ramFits i s hv (by
        simpa [routed, AddressDecode.routeCode, region, AddressDecode.regionCode] using routedExpr)
        _ (romLoad_load layout rom romFits ramFits i s hr hc c op dest address hp hit region)]
      simp [SystemModel.coreInput, planned, SystemModel.plan, routed, region]
    | ram =>
      rw [corePins_service_ram layout rom romFits ramFits i s hr hv (by
        simpa [routed, AddressDecode.routeCode, region, AddressDecode.regionCode] using routedExpr)]
      simp [SystemModel.coreInput, planned, SystemModel.plan, routed, region]
    | gpio =>
      apply corePins_service_mmio_plan layout rom romFits ramFits i s hr hc hv
        (Or.inl (by simpa [routed, AddressDecode.routeCode, region, AddressDecode.regionCode] using routedExpr))
        ⟨.gpio, BitVec.ofNat 6 hit.wordIndex, false, 0⟩
      simp [planned, SystemModel.plan, routed, region]
    | timer =>
      apply corePins_service_mmio_plan layout rom romFits ramFits i s hr hc hv
        (Or.inr (Or.inl (by simpa [routed, AddressDecode.routeCode, region, AddressDecode.regionCode] using routedExpr)))
        ⟨.timer, BitVec.ofNat 6 hit.wordIndex, false, 0⟩
      simp [planned, SystemModel.plan, routed, region]
    | uart =>
      apply corePins_service_mmio_plan layout rom romFits ramFits i s hr hc hv
        (Or.inr (Or.inr (by simpa [routed, AddressDecode.routeCode, region, AddressDecode.regionCode] using routedExpr)))
        ⟨.uart, BitVec.ofNat 6 hit.wordIndex, false, 0⟩
      simp [planned, SystemModel.plan, routed, region]

theorem corePins_dataService_store (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (c : RV32I.Semantics.Context) (op : RV32I.StoreOp) (address data : BitVec 32)
    (hp : (view s).core.phase = .dataRequest (.store c op address data)) :
    (CoreInterface.decode (corePins layout rom romFits ramFits i s)).dataService =
      (SystemModel.coreInput layout rom (decode i) (view s)).dataService := by
  have hv := (offer_store_control i s hr hc c op address data hp).1
  have routedExpr := route_store layout i s hr hc c op address data hp
  have planned : SystemModel.pendingPlan layout rom (view s) =
      some (SystemModel.plan layout rom (.store address (RV32I.Semantics.storeSize op) data)) := by
    simp [SystemModel.pendingPlan, hp, CoreModel.DataRequest.intent, CoreModel.DataRequest.pending, RV32I.Semantics.Pending.intent]
  cases routed : AddressMap.route layout ⟨.store, RV32I.Semantics.storeSize op, address⟩ with
  | error reason =>
    rw [corePins_service_fault layout rom romFits ramFits i s hv reason (by
      cases reason <;> simpa [routed, AddressDecode.routeCode] using routedExpr)]
    simp [SystemModel.coreInput, planned, SystemModel.plan, routed]
  | ok hit =>
    cases region : hit.region with
    | rom => exact False.elim (hit.store_not_rom rfl region)
    | ram =>
      rw [corePins_service_ram layout rom romFits ramFits i s hr hv (by
        simpa [routed, AddressDecode.routeCode, region, AddressDecode.regionCode] using routedExpr)]
      simp [SystemModel.coreInput, planned, SystemModel.plan, routed, region]
    | gpio =>
      apply corePins_service_mmio_plan layout rom romFits ramFits i s hr hc hv
        (Or.inl (by simpa [routed, AddressDecode.routeCode, region, AddressDecode.regionCode] using routedExpr))
        ⟨.gpio, BitVec.ofNat 6 hit.wordIndex, true, data⟩
      simp [planned, SystemModel.plan, routed, region]
    | timer =>
      apply corePins_service_mmio_plan layout rom romFits ramFits i s hr hc hv
        (Or.inr (Or.inl (by simpa [routed, AddressDecode.routeCode, region, AddressDecode.regionCode] using routedExpr)))
        ⟨.timer, BitVec.ofNat 6 hit.wordIndex, true, data⟩
      simp [planned, SystemModel.plan, routed, region]
    | uart =>
      apply corePins_service_mmio_plan layout rom romFits ramFits i s hr hc hv
        (Or.inr (Or.inr (by simpa [routed, AddressDecode.routeCode, region, AddressDecode.regionCode] using routedExpr)))
        ⟨.uart, BitVec.ofNat 6 hit.wordIndex, true, data⟩
      simp [planned, SystemModel.plan, routed, region]

theorem corePins_dataService (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s)) :
    (CoreInterface.decode (corePins layout rom romFits ramFits i s)).dataService =
      (SystemModel.coreInput layout rom (decode i) (view s)).dataService := by
  by_cases active : ∃ q, (view s).core.phase = .dataRequest q
  · obtain ⟨q, hp⟩ := active
    cases q with
    | load c op dest address => exact corePins_dataService_load layout rom romFits ramFits i s hr hc c op dest address hp
    | store c op address data => exact corePins_dataService_store layout rom romFits ramFits i s hr hc c op address data hp
  · have quiet := fun q hp => active (Exists.intro q hp)
    rw [corePins_dataService_quiet layout rom romFits ramFits i s hc quiet]
    have planned : SystemModel.pendingPlan layout rom (view s) = none := by
      cases hp : (view s).core.phase with
      | dataRequest q => exact False.elim (quiet q hp)
      | fetchRequest | fetchResponse | execute _ | dataResponse _ | fence _ | terminal _ =>
          simp [SystemModel.pendingPlan, hp]
    simp [SystemModel.coreInput, planned]

private theorem core_input_ext (a b : CoreModel.Input)
    (hr : a.reset = b.reset) (hf : a.fetchReady = b.fetchReady)
    (hfr : a.fetchResponse = b.fetchResponse) (hd : a.dataService = b.dataService)
    (hdr : a.dataResponse = b.dataResponse) : a = b := by
  cases a
  cases b
  simp_all

/-- Complete functional input binding off reset. No assumed provider values are
substituted: RAM, ROM and MMIO reply wires were each decoded above. -/
theorem corePins_decode (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s)) :
    CoreInterface.decode (corePins layout rom romFits ramFits i s) =
      SystemModel.coreInput layout rom (decode i) (view s) := by
  apply core_input_ext
  · exact corePins_reset_value layout rom romFits ramFits i s
  · exact corePins_fetchReady layout rom romFits ramFits i s
  · exact corePins_fetchResponse layout rom romFits ramFits i s
  · exact corePins_dataService layout rom romFits ramFits i s hr hc
  · exact corePins_dataResponse layout rom romFits ramFits i s hr

end Pinwheel.Hardware.Processor.SystemCircuit
