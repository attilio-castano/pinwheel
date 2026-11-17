import Pinwheel.Hardware.Processor.SystemCircuitProviders

/-! Explicit immutable ROM image lookup and byte-lane loading. Lookup equality
uses the admitted natural address before narrowing, never an alias assumption. -/
namespace Pinwheel.Hardware.Processor.SystemCircuit

set_option backward.isDefEq.respectTransparency false

variable (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

theorem rom_read_eval (i : Values Input) (s : Values (Register aw)) (address : E aw 32)
    (access : AddressMap.Access) (value : address.eval i s = access.address)
    (hit : AddressMap.Hit layout access) (region : hit.region = .rom) :
    (Execution.readTree rw (fun a => .lit (rom a))
      (.slice 2 rw (Nat.add_le_add_left romFits 2) address)).eval i s =
      rom (BitVec.ofNat rw hit.wordIndex) := by
  simp only [Execution.readTree_correct, Expr.eval, value]
  apply congrArg rom
  have word := hit.word_slice_width rw
  simpa [region, AddressMap.Config.base] using word

theorem romData_load (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (c : RV32I.Semantics.Context) (op : RV32I.LoadOp) (dest : RV32I.Register) (address : BitVec 32)
    (hp : (view s).core.phase = .dataRequest (.load c op dest address))
    (hit : AddressMap.Hit layout ⟨.load, RV32I.Semantics.loadSize op, address⟩)
    (region : hit.region = .rom) :
    (SystemWiring.romData (network layout ramFits) rom romFits).eval i s =
      rom (BitVec.ofNat rw hit.wordIndex) := by
  have fields := offer_load_routing i s hr hc c op dest address hp
  apply rom_read_eval layout rom romFits i s _ _ _ hit region
  exact fields.2.2

theorem romLoad_load (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (c : RV32I.Semantics.Context) (op : RV32I.LoadOp) (dest : RV32I.Register) (address : BitVec 32)
    (hp : (view s).core.phase = .dataRequest (.load c op dest address))
    (hit : AddressMap.Hit layout ⟨.load, RV32I.Semantics.loadSize op, address⟩)
    (region : hit.region = .rom) :
    (SystemWiring.romLoad (network layout ramFits) rom romFits).eval i s =
      Memory.ByteAccess.loadCore (RV32I.Semantics.loadSize op) (RV32I.Semantics.loadSigned op)
        hit.offset (rom (BitVec.ofNat rw hit.wordIndex)) := by
  obtain ⟨_, hz, ha⟩ := offer_load_routing i s hr hc c op dest address hp
  have hs := (offer_load_control i s hr hc c op dest address hp).2.1
  have offset : (Expr.slice 0 2 (by decide)
      ((network layout ramFits).coreOutputs CoreInterface.dataAddress)).eval i s = hit.offset := by
    change ((offer CoreInterface.dataAddress).eval i s).extractLsb' 0 2 = hit.offset
    rw [ha]
    exact hit.offset_slice
  have legal : Memory.ByteAccess.access
      (((network layout ramFits).coreOutputs CoreInterface.dataSize).eval i s)
      ((Expr.slice 0 2 (by decide) ((network layout ramFits).coreOutputs CoreInterface.dataAddress)).eval i s) =
      .ok (RV32I.Semantics.loadSize op) := by
    rw [network_core_output, hz, offset]
    apply (Memory.ByteAccess.access_ok_iff _ _ _).mpr
    refine ⟨?_, hit.byteAccess_aligned⟩
    cases op <;> rfl
  rw [SystemWiring.romLoad, Memory.ByteAdapterCircuit.loadExpr_eval _ _ _ _ i s _ legal,
    network_core_output, hs, offset, romData_load layout rom romFits ramFits i s hr hc c op dest address hp hit region]
  cases RV32I.Semantics.loadSigned op <;> rfl

theorem corePins_service_rom (i : Values Input) (s : Values (Register aw))
    (hv : (offer CoreInterface.dataValid).eval i s = 1)
    (selected : (route layout).eval i s = 0) (value : BitVec 32)
    (data : (SystemWiring.romLoad (network layout ramFits) rom romFits).eval i s = value) :
    (CoreInterface.decode (corePins layout rom romFits ramFits i s)).dataService =
      some (.atomic (.success value)) := by
  simp only [CoreInterface.decode, corePins, CoreInterface.dataServiceValid,
    CoreInterface.dataServiceAtomic, CoreInterface.dataServiceFault, CoreInterface.dataServiceData,
    coreInput, SystemWiring.coreInput, SystemWiring.both, SystemWiring.serviceFault,
    SystemWiring.peripheral, SystemWiring.either, SystemWiring.region, Expr.eval, WordOps.wordOr_eval,
    network_route, network_core_output, hv, selected, data]
  simp [CoreInterface.reply]

end Pinwheel.Hardware.Processor.SystemCircuit
