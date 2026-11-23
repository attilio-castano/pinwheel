import Pinwheel.Hardware.Processor.SystemCircuitConnection

/-! Fetch response storage follows accepted aligned fetch offers. Its inactive
fault/data latches are erased by the valid-bit projection. -/
namespace Pinwheel.Hardware.Processor.SystemCircuit

set_option backward.isDefEq.respectTransparency false

variable (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

theorem fetchView_step_quiet (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (owned : SystemModel.FetchOwned layout rom (view s))
    (quiet : (view s).core.phase ≠ .fetchRequest) :
    fetchView ((circuit layout rom romFits ramFits).step i s) =
      SystemModel.fetchStep layout rom (decode i) (view s) := by
  cases hp : (view s).core.phase with
  | fetchRequest => exact False.elim (quiet hp)
  | fetchResponse | execute _ | dataRequest _ | dataResponse _ | fence _ | terminal _ =>
    simp only [SystemModel.FetchOwned, hp] at owned
    simp [fetchView, fetchValid, fetch, Circuit.step, circuit, fetchNext, SystemWiring.fetchNext,
      SystemWiring.both, requestNetwork, Expr.eval, offer_eval i s hc,
      CoreInterface.outputValues, CoreInterface.fetchValid, CoreModel.observe, requestPins_decode,
      decode, hr, hp, SystemModel.fetchStep, owned]

theorem fetchView_step_unaligned (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (hp : (view s).core.phase = .fetchRequest) (unaligned : ¬CoreModel.aligned (view s).core.arch) :
    fetchView ((circuit layout rom romFits ramFits).step i s) =
      SystemModel.fetchStep layout rom (decode i) (view s) := by
  simp [fetchView, fetchValid, fetch, Circuit.step, circuit, fetchNext, SystemWiring.fetchNext,
    SystemWiring.both, requestNetwork, Expr.eval, offer_eval i s hc,
    CoreInterface.outputValues, CoreInterface.fetchValid, CoreModel.observe, requestPins_decode,
    decode, hr, hp, SystemModel.fetchStep, unaligned]

theorem offer_fetch_routing (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (hp : (view s).core.phase = .fetchRequest) (aligned : CoreModel.aligned (view s).core.arch) :
    (offer CoreInterface.fetchValid).eval i s = 1 ∧
    (offer CoreInterface.fetchAddress).eval i s = (view s).core.arch.pc := by
  simp only [offer_eval i s hc]
  simp [CoreInterface.outputValues, CoreInterface.fetchValid, CoreInterface.fetchAddress,
    CoreModel.observe, requestPins_decode, decode, hr, hp, aligned]

theorem fetchView_step_aligned (i : Values Input) (s : Values (Register aw))
    (hr : i reset = 0) (hc : CoreCircuit.Valid (coreValues s))
    (hp : (view s).core.phase = .fetchRequest) (aligned : CoreModel.aligned (view s).core.arch) :
    fetchView ((circuit layout rom romFits ramFits).step i s) =
      SystemModel.fetchStep layout rom (decode i) (view s) := by
  obtain ⟨hv, ha⟩ := offer_fetch_routing i s hr hc hp aligned
  have routeEval : (SystemWiring.fetchRoute requestNetwork layout).eval i s =
      AddressDecode.routeCode (AddressMap.route layout ⟨.fetch, .word, (view s).core.arch.pc⟩) := by
    simp only [SystemWiring.fetchRoute, AddressDecode.result_eval, requestNetwork]
    exact congrArg (fun address => AddressDecode.routeCode (AddressMap.route layout ⟨.fetch, .word, address⟩)) ha
  dsimp only [requestNetwork, fetch] at routeEval
  cases routed : AddressMap.route layout ⟨.fetch, .word, (view s).core.arch.pc⟩ with
  | error reason =>
    cases reason <;>
      simp_all [fetchView, fetchValid, fetchFault, fetch, Circuit.step, circuit,
        fetchNext, SystemWiring.fetchNext, SystemWiring.both, requestNetwork, Expr.eval,
        AddressDecode.routeCode, SystemModel.fetchStep,
        SystemModel.fetchReply, decode]
  | ok hit =>
    have region := (hit.fetch_rom rfl).1
    have word := rom_read_eval layout rom romFits i s (offer CoreInterface.fetchAddress)
      ⟨.fetch, .word, (view s).core.arch.pc⟩ ha hit region
    simp_all [fetchView, fetchValid, fetchFault, fetchData, fetch, Circuit.step, circuit,
      fetchNext, SystemWiring.fetchNext, SystemWiring.both, requestNetwork, Expr.eval,
      AddressDecode.routeCode, AddressDecode.regionCode, SystemModel.fetchStep, SystemModel.fetchReply, decode]

theorem fetchView_step (i : Values Input) (s : Values (Register aw))
    (hc : CoreCircuit.Valid (coreValues s)) (owned : SystemModel.FetchOwned layout rom (view s)) :
    fetchView ((circuit layout rom romFits ramFits).step i s) =
      SystemModel.fetchStep layout rom (decode i) (view s) := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  · by_cases hp : (view s).core.phase = .fetchRequest
    · by_cases aligned : CoreModel.aligned (view s).core.arch
      · exact fetchView_step_aligned layout rom romFits ramFits i s hr hc hp aligned
      · exact fetchView_step_unaligned layout rom romFits ramFits i s hr hc hp aligned
    · exact fetchView_step_quiet layout rom romFits ramFits i s hr hc owned hp
  · rw [reset_fetch layout rom romFits ramFits i s hr]
    simp [SystemModel.fetchStep, decode, hr]

end Pinwheel.Hardware.Processor.SystemCircuit
