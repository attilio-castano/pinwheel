import Pinwheel.Hardware.Buffered.GenericStartSeed
import Pinwheel.Hardware.Buffered.GenericEntryAt
import Pinwheel.Hardware.Buffered.SpiAdmission

/-! Installed static geometry and actual admitted START identify source PC0
before reading its word. Word legality follows from the independent layout. -/
namespace Pinwheel.Hardware.Buffered.GenericStart
open Pinwheel.Hardware Pinwheel.Program

structure Installed (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (r : Values Reactive.Register) : Prop where
  count : r .count = BitVec.ofNat 7 layout.count.val
  span : r .virtualSpan = BitVec.ofNat 11 p.code.span
  idleLevels : r .idleLevels = p.idle.levels
  idleEnabled : r .idleEnabled = p.idle.enabled
  image : ∀ k, r (.word k) = layout.words k

theorem entryAt {p : Program.Buffered.Program} (layout : GenericCertificate.Layout p)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (starting : Reactive.starting.eval i r = 1) : Refinement.EntryAt layout.map i r 0 := by
  have controls := SpiAdmission.starting_controls i r starting
  refine ⟨controls.entering, ?_, ?_⟩
  · rw [controls.pc, controls.outer, controls.inner, layout.initial]
  · exact controls.virtualPC

theorem legal {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {i : Values Reactive.Input} {r : Values Reactive.Register}
    (installed : Installed p layout r) (starting : Reactive.starting.eval i r = 1) :
    Reactive.legalEntry.eval i r = 1 := by
  have atEntry := entryAt layout i r starting
  exact Refinement.entryLegal layout i r 0 (GenericLayout.span_positive p.code)
    atEntry.entering atEntry.address atEntry.outer atEntry.inner atEntry.virtualPC
    installed.image installed.count installed.span

end Pinwheel.Hardware.Buffered.GenericStart
