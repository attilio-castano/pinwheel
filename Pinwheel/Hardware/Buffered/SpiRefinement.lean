import Pinwheel.Hardware.Buffered.SpiRelation

/-! Clock-step preservation for the SPI source/packed-circuit relation. -/
namespace Pinwheel.Hardware.Buffered.SpiRefinement
open Pinwheel.Hardware Pinwheel.Program

theorem Stopped.phase_cases {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {complete : Bool} (h : Stopped c payload r s e complete) :
    r .phase = 5 ∨ r .phase = 7 := by
  cases complete <;> simp [h.phase]

theorem Stopped.step {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {complete : Bool} (h : Stopped c payload r s e complete)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i) :
    Stopped c payload (Reactive.circuit.step i r)
      (Program.Buffered.advance (BufferedSPI.program c) capacity s (i .rawInputs)) e complete := by
  rw [SpiCircuit.stopped_step i r quiet h.phase_cases,
    SpiInterpreter.advance_stopped _ _ s (stopReason complete) h.control]
  exact ⟨h.common.sampleTick (i .rawInputs), h.slot, h.control, h.phase,
    h.retained, h.pc, h.virtualPC, h.outer, h.inner, h.currentControl, h.remaining⟩

theorem decrement8 (n : Fin 256) (positive : 0 < n.val) :
    BitVec.ofNat 8 n.val - 1 = BitVec.ofNat 8 (n.val - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
  done

theorem Running.owned {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {pc : Program.Buffered.PC} {remaining : Fin 256}
    (h : Running c payload r s e pc remaining) : Program.Buffered.owned s = true := by
  simp [Program.Buffered.owned, h.slot, h.common.owner]

theorem Running.remaining_ne_zero {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {pc : Program.Buffered.PC} {remaining : Fin 256}
    (h : Running c payload r s e pc remaining) (positive : 0 < remaining.val) :
    r .remaining ≠ 0 := by
  rw [h.remaining_eq]
  intro zero
  have hz : remaining = 0 := by simpa using congrArg BitVec.toNat zero
  omega
  done

theorem Running.countdown {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {pc : Program.Buffered.PC} {remaining : Fin 256}
    (h : Running c payload r s e pc remaining) (positive : 0 < remaining.val)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i) :
    Running c payload (Reactive.circuit.step i r)
      (Program.Buffered.advance (BufferedSPI.program c) capacity s (i .rawInputs))
      e pc ⟨remaining.val - 1, by omega⟩ := by
  rw [SpiCircuit.countdown_step i r quiet h.coordinates.phase (h.remaining_ne_zero positive),
    SpiInterpreter.advance_countdown _ _ s pc remaining h.owned h.control positive]
  refine ⟨h.common.countdownTick (i .rawInputs) _, h.slot, rfl, h.within,
    ⟨h.coordinates.phase, h.coordinates.virtualPC, h.coordinates.pc,
      h.coordinates.currentControl, h.coordinates.outer, h.coordinates.inner,
      h.coordinates.count, h.coordinates.virtualSpan, h.coordinates.words⟩,
    ?_, h.retained, rfl, h.first⟩
  exact (congrArg (fun v : BitVec 8 => v - 1) h.remaining_eq).trans
    (decrement8 remaining positive)

end Pinwheel.Hardware.Buffered.SpiRefinement
