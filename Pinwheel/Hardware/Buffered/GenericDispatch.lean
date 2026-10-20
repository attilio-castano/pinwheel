import Pinwheel.Hardware.Buffered.GenericHeldStop
import Pinwheel.Hardware.Buffered.GenericEntryImage
import Pinwheel.Hardware.Buffered.GenericLayoutCircuit

/-! Source-selected dispatch targets determine the actual packed sequencer's
virtual address, physical row and counted-loop indices. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

theorem sequential_virtual (i : Values Reactive.Input) (r : Values Reactive.Register)
    (pc : Program.Buffered.PC) (notStarting : Reactive.starting.eval i r = 0)
    (notAbsolute : Reactive.absoluteDispatch.eval i r = 0)
    (current : r .virtualPC = BitVec.ofNat 10 pc.val) :
    Reactive.entryVirtual.eval i r = BitVec.ofNat 11 (pc.val + 1) := by
  simp only [Reactive.entryVirtual, Reactive.increment, Expr.eval, notStarting, notAbsolute,
    show (0 : BitVec 1) ≠ 1 from by decide, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub, current]
  rw [BitVec.toNat_append]
  simp [Nat.add_comm]
  done

theorem Running.sequential_coordinates {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc)
    (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i)
    (notAbsolute : Reactive.absoluteDispatch.eval i r = 0)
    (within : pc.val + 1 < p.code.span) :
    GenericLayout.Coordinates.mk (Reactive.entryPC.eval i r) (Reactive.entryOuter.eval i r)
        (Reactive.entryInner.eval i r) =
      layout.map ⟨pc.val + 1, by have := p.fits; omega⟩ ∧
    Reactive.entryVirtual.eval i r = BitVec.ofNat 11 (pc.val + 1) := by
  have seq := GenericLayoutCircuit.sequential_coordinates i r
    (SpiCircuit.quiet_controls i r quiet).2.2.1
  rw [h.currentControl, h.coordinates, layout.successor pc within] at seq
  refine ⟨?_, sequential_virtual i r pc (SpiCircuit.quiet_controls i r quiet).2.2.1 notAbsolute h.virtualPC⟩
  simpa only [Reactive.entryPC, Reactive.entryOuter, Reactive.entryInner, Expr.eval,
    notAbsolute, show (0 : BitVec 1) ≠ 1 from by decide, ↓reduceIte] using seq
  done

end Pinwheel.Hardware.Buffered.Refinement
