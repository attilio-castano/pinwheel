import Pinwheel.Hardware.Processor.SystemCircuitFetch

/-! Complete connected-system cycle refinement. The proof composes the existing
core/RAM/MMIO implementations with exact request, reply and fetch wiring.
Provider ownership and byte snapshots remain explicit in Valid; raw reset has
no such premise and retains the entire pre-reset RAM image and read snapshot. -/
namespace Pinwheel.Hardware.Processor.SystemCircuit

set_option backward.isDefEq.respectTransparency false

variable (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

theorem spec_reset (i : Values Input) (s : SystemModel.State aw) (hr : i reset = 1) :
    (spec layout rom).step i s = SystemModel.initial s.ram.memory.contents s.ram.memory.q := by
  simp [spec, SystemModel.step, SystemModel.coreInput, SystemModel.ramInput,
    SystemModel.mmioInput, SystemModel.fetchStep, decode, hr, CoreModel.step, CoreModel.tick,
    Memory.ByteAdapterModel.step, Memory.ByteAdapterModel.command, Memory.SinglePort.step,
    MmioModel.step, SystemModel.initial]

/-- Exact next-state projection, including same-edge atomic MMIO completion and
RAM write-on-acknowledgement. Reset is handled directly rather than assuming
reset-masked pins equal the model's inactive request metadata. -/
theorem view_step (i : Values Input) (s : Values (Register aw)) (h : Valid layout rom s) :
    view ((circuit layout rom romFits ramFits).step i s) = (spec layout rom).step i (view s) := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  · change SystemModel.State.mk
      (CoreCircuit.view (coreValues ((circuit layout rom romFits ramFits).step i s)))
      (Memory.ByteAdapterCircuit.view (ramValues ((circuit layout rom romFits ramFits).step i s)))
      (MmioCircuit.view (mmioValues ((circuit layout rom romFits ramFits).step i s)))
      (fetchView ((circuit layout rom romFits ramFits).step i s)) = _
    rw [core_step, ram_step, mmio_step, CoreCircuit.step_eq _ _ h.1,
      Memory.ByteAdapterCircuit.view_step, MmioCircuit.view_step,
      fetchView_step layout rom romFits ramFits i s h.1 h.2.fetch]
    change SystemModel.State.mk
      (CoreModel.step (CoreInterface.decode (corePins layout rom romFits ramFits i s)) (view s).core)
      (Memory.ByteAdapterModel.step (Memory.ByteAdapterInterface.decode (ramPins layout ramFits i s)) (view s).ram)
      (MmioModel.step (MmioInterface.decode (mmioPins layout i s)) (view s).mmio)
      (SystemModel.fetchStep layout rom (decode i) (view s)) = _
    rw [corePins_decode layout rom romFits ramFits i s hr h.1,
      ramPins_decode layout rom ramFits i s hr h.1, mmioPins_decode layout rom i s hr h.1]
    rfl
  · rw [reset_view layout rom romFits ramFits i s hr, spec_reset layout rom i (view s) hr]
    rfl

theorem preserved (i : Values Input) (s : Values (Register aw)) (h : Valid layout rom s) :
    Valid layout rom ((circuit layout rom romFits ramFits).step i s) := by
  refine ⟨?_, ?_⟩
  · rw [core_step]
    exact CoreCircuit.preserved _ _ h.1
  · rw [view_step layout rom romFits ramFits i s h]
    exact SystemModel.preserved layout rom (decode i) (view s) h.2

private theorem core_reset_outputs_congr (a b : Values CoreInterface.Input) (s : CoreModel.State)
    (ha : (CoreInterface.decode a).reset = true) (hb : (CoreInterface.decode b).reset = true) :
    @Eq (Values CoreInterface.Output) (CoreInterface.outputValues a s) (CoreInterface.outputValues b s) := by
  simp [CoreInterface.outputValues, CoreModel.observe, CoreModel.event, CoreModel.tick, ha, hb]

/-- Complete 37-port observation correspondence, including MMIO response fields
and pre-edge retirement/trap outputs. -/
theorem output_eq (i : Values Input) (s : Values (Register aw)) (h : Valid layout rom s) (o : Output b) :
    (circuit layout rom romFits ramFits).observe i s o = (spec layout rom).observe i (view s) o := by
  cases o with
  | left o =>
    rw [core_output, CoreCircuit.output_eq _ _ h.1]
    change CoreInterface.outputValues (corePins layout rom romFits ramFits i s) (view s).core o =
      CoreInterface.outputValues (SystemModelEncoding.corePins
        (SystemModel.coreInput layout rom (decode i) (view s))) (view s).core o
    apply congrArg (fun outputs : Values CoreInterface.Output => outputs o)
    rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
    · apply SystemModelEncoding.core_outputs_congr
      rw [SystemModelEncoding.decode_corePins]
      exact corePins_decode layout rom romFits ramFits i s hr h.1
    · apply core_reset_outputs_congr
      · simp [corePins_reset_value, decode, hr]
      · simp [SystemModelEncoding.decode_corePins, SystemModel.coreInput, decode, hr]
  | right o =>
    change (mmioOutput layout o).eval i s = MmioInterface.outputValues
      (SystemModelEncoding.mmioPins (SystemModel.mmioInput layout rom (decode i) (view s))) (view s).mmio o
    rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
    · exact mmioOutput_value layout rom i s hr h.1 o
    · rw [mmioOutput_eval]
      have actualReset : mmioPins layout i s MmioInterface.reset = 1 := by simpa using hr
      have expectedReset : SystemModelEncoding.mmioPins
          (SystemModel.mmioInput layout rom (decode i) (view s)) MmioInterface.reset = 1 := by
        simp [SystemModelEncoding.mmioPins, MmioInterface.reset, SystemModel.mmioInput, decode, hr]
      cases o with
      | «at» k =>
        match k with
        | ⟨0,_⟩ | ⟨1,_⟩ | ⟨2,_⟩ | ⟨3,_⟩ |
          ⟨4,_⟩ | ⟨5,_⟩ | ⟨6,_⟩ =>
          simp [MmioInterface.outputValues, MmioInterface.response, actualReset, expectedReset]
        | ⟨k+7,bound⟩ => exact False.elim (by change k+7 < 7 at bound; omega)

def implementation : DecodedImplementation (circuit layout rom romFits ramFits) (spec layout rom) where
  Valid := Valid layout rom
  view := view
  preserved := preserved layout rom romFits ramFits
  step_eq := view_step layout rom romFits ramFits
  output_eq i s h {_} o := output_eq layout rom romFits ramFits i s h o

def resetCertificate : (implementation layout rom romFits ramFits).Reset reset where
  initial := resetState
  reset_valid := reset_valid layout rom romFits ramFits
  reset_view := reset_view layout rom romFits ramFits

end Pinwheel.Hardware.Processor.SystemCircuit
