import Pinwheel.Hardware.Buffered.SpiRefinement
import Pinwheel.Hardware.Buffered.SpiFrame
import Pinwheel.Hardware.Buffered.SpiEntryControls
import Pinwheel.Hardware.Buffered.SpiDatapath
import Pinwheel.Hardware.Buffered.SpiScratch
import Pinwheel.Hardware.Buffered.SpiPins

/-! Dispatch preservation for canonical compact SPI leaves. -/
namespace Pinwheel.Hardware.Buffered.SpiRefinement
open Pinwheel.Hardware Pinwheel.Program

theorem spi_last (c : SpiSource.Config) :
    (BufferedSPI.program c).last.val = SpiCoordinates.bitSpan c + 1 := by
  simp [Program.Buffered.Program.last, BufferedSPI.program,
    (BufferedSPI.geometry c).2.1, SpiCoordinates.bitSpan]

def Running.nextPC {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {pc : Program.Buffered.PC} {remaining : Fin 256}
    (h : Running c payload r s e pc remaining) : Program.Buffered.PC :=
  ⟨pc.val + 1, by have bound := (SpiCoordinates.bitSpan_bounds c).2; have := h.within; omega⟩

theorem Running.before_last {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {pc : Program.Buffered.PC} {remaining : Fin 256}
    (h : Running c payload r s e pc remaining) : pc.val < (BufferedSPI.program c).last.val := by
  rw [spi_last]
  exact Nat.lt_succ_of_le h.within

theorem Running.remaining_zero {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {pc : Program.Buffered.PC}
    (h : Running c payload r s e pc 0) : r .remaining = 0 := by
  simpa using h.remaining_eq

theorem Running.preEntry {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {pc : Program.Buffered.PC}
    (h : Running c payload r s e pc 0) (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i) :
    SpiEntryControls.PreEntry i r :=
  SpiEntryControls.quiet_preEntry i r quiet h.coordinates.phase h.remaining_zero
    (SpiEntry.dispatch_legal c pc.val i r quiet.1 quiet.2 h.coordinates h.within h.remaining_zero)

theorem Running.nextFrame {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {pc : Program.Buffered.PC}
    (h : Running c payload r s e pc 0) (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i) :
    SpiCoordinates.At c h.nextPC.val (SpiCircuit.runEntryTick i r) := by
  have next := SpiCoordinates.next_coordinates c pc.val i r quiet.1 quiet.2 h.coordinates h.within
  have fields := SpiCoordinates.entry_fields c pc.val i r quiet.1 quiet.2
    h.coordinates h.within h.remaining_zero
  exact SpiFrame.run_entry_at c (pc.val + 1) i r next.1 next.2.1 next.2.2.1 next.2.2.2
    fields.2.1 h.common.geometry.count h.common.geometry.virtualSpan h.common.image

theorem Running.wordNext {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {pc : Program.Buffered.PC}
    (h : Running c payload r s e pc 0) (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i) :
    Reactive.entryWord.eval i r =
      SpiSource.word c (BitVec.ofNat 6 (SpiCoordinates.physicalPC c h.nextPC.val)) :=
  (SpiCoordinates.entry_fields c pc.val i r quiet.1 quiet.2
    h.coordinates h.within h.remaining_zero).1

theorem source_fetch_physical (c : SpiSource.Config) (target : Program.Buffered.PC)
    (within : target.val ≤ SpiCoordinates.bitSpan c + 1) :
    (BufferedSPI.program c).fetch target =
      some (SpiSource.leaf c ⟨SpiCoordinates.physicalPC c target.val,
        SpiEntry.physicalPC_lt_four c target.val within⟩) := by
  rw [BufferedSPI.fetch_shape]
  by_cases inside : target.val < SpiCoordinates.bitSpan c
  all_goals simp [SpiCoordinates.physicalPC, inside, SpiSource.leaf, SpiSource.leafAt]
  case pos =>
    have parity : target.val % 2 = 0 ∨ target.val % 2 = 1 := by omega
    rcases parity with parity | parity
    all_goals simp [parity]
    done
  case neg =>
    have ending : target.val = SpiCoordinates.bitSpan c ∨
        target.val = SpiCoordinates.bitSpan c + 1 := by omega
    rcases ending with ending | ending
    all_goals simp [ending]
    done
  done

theorem Running.wordLeaf {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {pc : Program.Buffered.PC}
    (h : Running c payload r s e pc 0) (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (leaf : Fin 4) (physical : SpiCoordinates.physicalPC c h.nextPC.val = leaf.val) :
    Reactive.entryWord.eval i r = SpiSource.word c (BitVec.ofNat 6 leaf.val) := by
  simpa only [physical] using h.wordNext i quiet

theorem Running.fetchLeaf {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {pc : Program.Buffered.PC}
    (h : Running c payload r s e pc 0) (leaf : Fin 4)
    (physical : SpiCoordinates.physicalPC c h.nextPC.val = leaf.val) :
    (BufferedSPI.program c).fetch h.nextPC = some (SpiSource.leaf c leaf) :=
  (source_fetch_physical c h.nextPC (Nat.add_le_add_right h.within 1)).trans
    (congrArg (fun k : Fin 4 => some (SpiSource.leaf c k)) (Fin.ext physical))

theorem Common.idle {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    (h : Common c payload r s e) :
    (BufferedSPI.program c).idle = ⟨r .idleLevels, r .idleEnabled⟩ := by
  rw [h.geometry.idleLevels, h.geometry.idleEnabled]
  rfl

theorem Common.runEntryTick {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    (h : Common c payload r s e) (i : Values Reactive.Input) (e' : Transfer.Execution)
    (control : Engine.Reactive.Control 1023) (pins : Engine.Reactive.Pins)
    (buffers : Transfer.State)
    (data : Datapath payload (SpiCircuit.runEntryTick i r) e')
    (owner : e'.request.identity = s.owner)
    (commands : pins = ⟨Reactive.entryLevels.eval i r, Reactive.entryEnabled.eval i r⟩)
    (scratch : Reactive.entryScratch.eval i r = 0) :
    Common c payload (SpiCircuit.runEntryTick i r)
      {s with
        core := ⟨control, pins, s.core.samples⟩
        buffers := buffers
        samplerFirst := i .rawInputs
        samplerSecond := s.samplerFirst} e' :=
  ⟨SpiFrame.geometry_runEntryTick c i r h.geometry, h.image, h.valid,
    data, owner, commands, h.samples, scratch⟩

theorem Common.stopEntryTick {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    (h : Common c payload r s e) (i : Values Reactive.Input) (e' : Transfer.Execution)
    (complete : Bool) (buffers : Transfer.State)
    (data : Datapath payload (SpiCircuit.stopEntryTick i r) e')
    (owner : e'.request.identity = s.owner)
    (scratch : Reactive.entryScratch.eval i r = 0) :
    Common c payload (SpiCircuit.stopEntryTick i r)
      {s with
        core := ⟨.stopped (stopReason complete), (BufferedSPI.program c).idle, s.core.samples⟩
        buffers := buffers
        samplerFirst := i .rawInputs
        samplerSecond := s.samplerFirst} e' :=
  ⟨⟨h.geometry.count, h.geometry.virtualSpan, h.geometry.idleLevels, h.geometry.idleEnabled⟩,
    h.image, h.valid, data, owner, h.idle, h.samples, scratch⟩

end Pinwheel.Hardware.Buffered.SpiRefinement
