import Pinwheel.Hardware.Buffered.GenericEntryImage

/-! A dispatch location is identified before the selected word is read. Fetch
and legality then follow from the independent installed-image certificate. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

structure EntryAt (map : Program.Buffered.PC → GenericLayout.Coordinates)
    (i : Values Reactive.Input) (r : Values Reactive.Register) (pc : Program.Buffered.PC) : Prop where
  entering : Reactive.entering.eval i r = 1
  coordinates : GenericLayout.Coordinates.mk (Reactive.entryPC.eval i r)
    (Reactive.entryOuter.eval i r) (Reactive.entryInner.eval i r) = map pc
  virtualPC : Reactive.entryVirtual.eval i r = BitVec.ofNat 11 pc.val

theorem EntryAt.address {map : Program.Buffered.PC → GenericLayout.Coordinates}
    {i : Values Reactive.Input} {r : Values Reactive.Register} {pc : Program.Buffered.PC}
    (h : EntryAt map i r pc) : Reactive.entryPC.eval i r = (map pc).row :=
  congrArg GenericLayout.Coordinates.row h.coordinates

theorem EntryAt.outer {map : Program.Buffered.PC → GenericLayout.Coordinates}
    {i : Values Reactive.Input} {r : Values Reactive.Register} {pc : Program.Buffered.PC}
    (h : EntryAt map i r pc) : Reactive.entryOuter.eval i r = (map pc).outer :=
  congrArg GenericLayout.Coordinates.outer h.coordinates

theorem EntryAt.inner {map : Program.Buffered.PC → GenericLayout.Coordinates}
    {i : Values Reactive.Input} {r : Values Reactive.Register} {pc : Program.Buffered.PC}
    (h : EntryAt map i r pc) : Reactive.entryInner.eval i r = (map pc).inner :=
  congrArg GenericLayout.Coordinates.inner h.coordinates

theorem EntryAt.word {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {i : Values Reactive.Input} {r : Values Reactive.Register} {pc : Program.Buffered.PC}
    (h : EntryAt layout.map i r pc) (within : pc.val < p.code.span)
    (instruction : Program.Buffered.Instruction) (fetch : p.fetch pc = some instruction)
    (image : ∀ k, r (.word k) = layout.words k) :
    Reactive.entryWord.eval i r = GenericEncoding.encode instruction :=
  entryWord layout i r pc within instruction fetch h.entering h.address image

theorem EntryAt.branch {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {i : Values Reactive.Input} {r : Values Reactive.Register} {pc : Program.Buffered.PC}
    (h : EntryAt layout.map i r pc) (within : pc.val < p.code.span)
    (instruction : Program.Buffered.Instruction) (fetch : p.fetch pc = some instruction)
    (image : ∀ k, r (.word k) = layout.words k) :
    Reactive.entryBranch.eval i r = GenericLayout.instructionFinish layout.map instruction :=
  entryBranch layout i r pc within instruction fetch h.entering h.address image

theorem EntryAt.legal {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {s : Program.Buffered.State} {e : Transfer.Execution}
    {i : Values Reactive.Input} {r : Values Reactive.Register} {pc : Program.Buffered.PC}
    (h : EntryAt layout.map i r pc) (within : pc.val < p.code.span)
    (common : Common p layout payload r s e) : Reactive.legalEntry.eval i r = 1 :=
  entryLegal layout i r pc within h.entering h.address h.outer h.inner h.virtualPC
    common.image common.count common.span

end Pinwheel.Hardware.Buffered.Refinement
