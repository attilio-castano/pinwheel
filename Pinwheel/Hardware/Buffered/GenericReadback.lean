import Pinwheel.Hardware.Buffered.GenericSessionReuse

/-! Retained RX readback agrees with the completed source prefix at every
physical index. Wire readValid is an availability bit; owned source access
still uses the full logical identity and no authentication property is added. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

theorem datapath_read_valid {payload : BitVec 32} {actual : SramState.State}
    {e : Transfer.Execution} (data : Datapath payload actual.core e)
    (retained : actual.core .retained = 1) (query : Values Reactive.Input) :
    actual.observe query .readValid =
      BitVec.ofBool (decide ((query .readIndex).toNat < e.rx.length)) := by
  rw [Lifecycle.observe_effective]
  change actual.core .retained &&&
    BitVec.ofBool (decide ((0#1 ++ query .readIndex).toNat < (actual.core .rxLength).toNat)) = _
  simp only [retained, data.rxLength, BitVec.toNat_append, BitVec.toNat_ofNat]
  by_cases inside : (query .readIndex).toNat < e.rx.length
  all_goals simp [inside]

theorem datapath_read_bit {payload : BitVec 32} {actual : SramState.State}
    {e : Transfer.Execution} (data : Datapath payload actual.core e)
    (retained : actual.core .retained = 1) (query : Values Reactive.Input) :
    actual.observe query .readBit = BitVec.ofBool (e.rx.getD (query .readIndex).toNat false) := by
  have valid := datapath_read_valid data retained query
  rw [Lifecycle.observe_effective] at valid ⊢
  change Reactive.readValid.eval (Lifecycle.effectiveInputs actual query)
    (Lifecycle.effectiveState actual query) = _ at valid
  change (if Reactive.readValid.eval (Lifecycle.effectiveInputs actual query)
      (Lifecycle.effectiveState actual query) = 1 then
    (Execution.readTree 5 (fun k => Expr.slice k.toNat 1 (by omega) (.reg .rxData))
      (.input .readIndex)).eval (Lifecycle.effectiveInputs actual query)
        (Lifecycle.effectiveState actual query) else 0) = _
  rw [Execution.readTree_correct, valid]
  change (if BitVec.ofBool (decide ((query .readIndex).toNat < e.rx.length)) = 1 then
      (actual.core .rxData).extractLsb' (query .readIndex).toNat 1 else 0) = _
  rw [data.received]
  by_cases inside : (query .readIndex).toNat < e.rx.length
  · simp only [inside, decide_true, BitVec.ofBool_true]
    change (SpiPacking.rxWord e.rx).extractLsb' (query .readIndex).toNat 1 = _
    rw [← SpiPacking.rxWord_getLsbD e.rx (query .readIndex).toNat (query .readIndex).isLt]
    exact Decode.extract_bit _ _ (query .readIndex).isLt
  · simp [inside]

theorem retained_read {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {actual : SramState.State} {source : Program.Buffered.State}
    (related : RelatedSram p layout payload actual source)
    (retained : actual.core .retained = 1) (query : Values Reactive.Input) :
    ∃ e outcome,
      source.buffers.slot = .completed ⟨e, outcome⟩ ∧
      Transfer.step capacity source.buffers (.read source.owner) =
        ⟨source.buffers, .result ⟨e, outcome⟩⟩ ∧
      actual.observe query .readValid =
        BitVec.ofBool (decide ((query .readIndex).toNat < e.rx.length)) ∧
      actual.observe query .readBit = BitVec.ofBool (e.rx.getD (query .readIndex).toNat false) := by
  obtain ⟨e, outcome, slot, _, data, owner⟩ := GenericSession.completed related retained
  refine ⟨e, outcome, slot, ?_, datapath_read_valid data retained query,
    datapath_read_bit data retained query⟩
  simp [Transfer.step, Transfer.Command.identity, Transfer.Slot.identity,
    Transfer.admittedStep, slot, owner]

end Pinwheel.Hardware.Buffered.Refinement
