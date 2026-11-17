import Pinwheel.Hardware.Processor.SystemCertified

/-! Actual provider events of the connected circuit. RAM completions decode
actual response pins and retained request metadata; MMIO completions decode
actual response pins and preserve autonomous device events. These are not a
new core retirement extractor: the complete core port/state correspondence is
provided by SystemCertified, while its architectural event decoding is separate.
-/
namespace Pinwheel.Hardware.Processor.SystemCircuit

variable (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30)

/-- The existing hardware extractor uses the actual bound byte-RAM input pins,
actual response outputs and retained request, including the store operand. -/
def ramEvents (i : Values Input) (s : Values (Register aw)) : List (Memory.ByteAdapterEffects.Event aw) :=
  Memory.ByteAdapterRefinement.events (ramPins layout ramFits i s) (ramValues s)

/-- CPU responses are extracted from the actual MMIO outputs. Autonomous input
and timer events are preserved even on a cycle without architectural retirement. -/
def mmioEvents (i : Values Input) (s : Values (Register aw)) : List MmioModel.Event :=
  MmioCircuit.physicalEvents (mmioPins layout i s) (mmioValues s)

theorem ramEvents_eq (i : Values Input) (s : Values (Register aw)) (h : CoreCircuit.Valid (coreValues s)) :
    ramEvents layout ramFits i s = (SystemModel.events layout rom (decode i) (view s)).ram := by
  unfold ramEvents
  rw [Memory.ByteAdapterRefinement.events_eq]
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  · rw [ramPins_decode layout rom ramFits i s hr h]
    rfl
  · have actual : (Memory.ByteAdapterInterface.decode (ramPins layout ramFits i s)).reset = true := by
      simp [Memory.ByteAdapterInterface.decode, hr]
    simp [SystemModel.events, Memory.ByteAdapterEffects.events, Memory.ByteAdapterModel.completedRequests,
      actual, SystemModel.ramInput, decode, hr]

theorem mmioEvents_eq (i : Values Input) (s : Values (Register aw)) (h : CoreCircuit.Valid (coreValues s)) :
    mmioEvents layout i s = (SystemModel.events layout rom (decode i) (view s)).mmio := by
  unfold mmioEvents
  rw [MmioCircuit.physicalEvents_eq _ _ (mmioPins_admitted layout i s)]
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr
  · rw [mmioPins_decode layout rom i s hr h]
    rfl
  · have actual : (MmioInterface.decode (mmioPins layout i s)).reset = true := by
      simp [MmioInterface.decode, hr]
    simp [SystemModel.events, MmioModel.events, actual, SystemModel.mmioInput, decode, hr]

theorem ramEvents_path (i : Values Input) (s : Values (Register aw)) (h : Valid layout rom s) :
    (Memory.ByteAdapterEffects.atomic aw).Path (view s).ram.memory.contents
      (ramEvents layout ramFits i s)
      (view ((circuit layout rom romFits ramFits).step i s)).ram.memory.contents := by
  rw [ramEvents_eq layout rom ramFits i s h.1, view_step layout rom romFits ramFits i s h]
  exact SystemModel.ram_edge_path layout rom (decode i) (view s) h.2

theorem mmioEvents_replay (i : Values Input) (s : Values (Register aw)) (h : Valid layout rom s) :
    MmioModel.replay (view s).mmio (mmioEvents layout i s) =
      some (view ((circuit layout rom romFits ramFits).step i s)).mmio := by
  rw [mmioEvents_eq layout rom i s h.1, view_step layout rom romFits ramFits i s h]
  exact SystemModel.mmio_replay layout rom (decode i) (view s)

/-- Replaying actual RAM completion events reconstructs every final RAM word.
Reset drops pending work and therefore emits no RAM completion event. -/
theorem ram_trace_path (s : Values (Register aw)) (h : Valid layout rom s) (traffic : List (Values Input)) :
    (Memory.ByteAdapterEffects.atomic aw).Path (view s).ram.memory.contents
      ((circuit layout rom romFits ramFits).component.eventTrace (ramEvents layout ramFits) s traffic)
      (view ((circuit layout rom romFits ramFits).component.run s traffic)).ram.memory.contents := by
  induction traffic generalizing s with
  | nil => exact .nil _
  | cons i rest ih =>
    exact (ramEvents_path layout rom romFits ramFits i s h).append
      (ih _ (preserved layout rom romFits ramFits i s h))

theorem ram_trace_replay (s : Values (Register aw)) (h : Valid layout rom s) (traffic : List (Values Input)) :
    Memory.ByteAdapterEffects.replay (view s).ram.memory.contents
      ((circuit layout rom romFits ramFits).component.eventTrace (ramEvents layout ramFits) s traffic) =
      some (view ((circuit layout rom romFits ramFits).component.run s traffic)).ram.memory.contents :=
  Memory.ByteAdapterEffects.replay_of_path (ram_trace_path layout rom romFits ramFits s h traffic)

/-- Autonomous timer/RX/TX events remain in the replay during CPU stalls and
terminal cycles. No UART wire timing is asserted by this event-level model. -/
theorem mmio_trace_replay (s : Values (Register aw)) (h : Valid layout rom s) (traffic : List (Values Input)) :
    MmioModel.replay (view s).mmio
      ((circuit layout rom romFits ramFits).component.eventTrace (mmioEvents layout) s traffic) =
      some (view ((circuit layout rom romFits ramFits).component.run s traffic)).mmio := by
  induction traffic generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change MmioModel.replay (view s).mmio (mmioEvents layout i s ++ _) = _
    rw [MmioModel.replay_append, mmioEvents_replay layout rom romFits ramFits i s h, Option.bind_some]
    exact ih _ (preserved layout rom romFits ramFits i s h)

end Pinwheel.Hardware.Processor.SystemCircuit
