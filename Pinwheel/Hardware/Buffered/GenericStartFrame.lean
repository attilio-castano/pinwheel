import Pinwheel.Hardware.Buffered.GenericStartData

/-! START resets scratch before its optional capture and preserves exactly
the old physical pins selected by the first instruction's masks. -/
namespace Pinwheel.Hardware.Buffered.GenericStart
open Pinwheel.Hardware Pinwheel.Program Pinwheel.Engine.Reactive

theorem scratch (instruction : Program.Buffered.Instruction)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (starting : Reactive.starting.eval i r = 1)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction)
    (running : Reactive.runEntry.eval i r = BitVec.ofBool (GenericEntryFlags.runs instruction)) :
    GenericPhase.Scratch (Reactive.entryScratch.eval i r)
      (capture (Vector.replicate 16 false) (GenericEntry.capture instruction) (r .stage2)) := by
  cases active : GenericEntryFlags.runs instruction
  case false =>
    have noCapture : GenericEntry.capture instruction = none := by
      cases operation : instruction.operation
      all_goals simp [GenericEntryFlags.runs, operation] at active
      all_goals simp [GenericEntry.capture, operation]
    intro k
    simp [Reactive.entryScratch, Expr.eval, running, active, starting,
      noCapture, capture]
  case true =>
    have fields : GenericPhase.CaptureFields (Reactive.entryCapture.eval i r)
        (GenericEntry.capture instruction) := by
      simpa only [Reactive.entryCapture, Expr.eval, word, GenericWord.capture_field,
        GenericEntry.capture_field] using GenericPhase.capture_fields (GenericEntry.capture instruction)
    have old : GenericPhase.Scratch
        ((Expr.mux Reactive.starting (.lit 0) Reactive.exitScratch).eval i r)
        (Vector.replicate 16 false) := by
      intro k
      simp [Expr.eval, starting]
    simpa only [Reactive.entryScratch, Expr.eval, running, active, BitVec.ofBool_true, ↓reduceIte]
      using GenericPhase.capture_matches Reactive.entryCapture
        (.mux Reactive.starting (.lit 0) Reactive.exitScratch) i r (Vector.replicate 16 false)
        (GenericEntry.capture instruction) fields old

theorem txBit (p : Program.Buffered.Program) (i : Values Reactive.Input)
    (r : Values Reactive.Register) (available : 0 < (i .txLength).toNat) :
    (i .txData).getLsbD 0 = Program.Buffered.txBit (base p r i) := by
  simp [Program.Buffered.txBit, base, resample, seed, SpiStart.request, available,
    SpiPacking.txBits]

theorem entry_pins (p : Program.Buffered.Program) (instruction : Program.Buffered.Instruction)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (starting : Reactive.starting.eval i r = 1)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction)
    (available : ∀ pin enable invert action,
      instruction.operation = .shift pin enable invert action → 0 < (i .txLength).toNat) :
    (⟨Reactive.entryLevels.eval i r, Reactive.entryEnabled.eval i r⟩ : Pins) =
      GenericPins.pins instruction (base p r i).core.pins (Program.Buffered.txBit (base p r i)) := by
  rw [GenericPins.entry_pins instruction i r word]
  cases operation : instruction.operation
  all_goals simp only [GenericPins.pins, operation]
  case shift pin enable invert action =>
    rw [show (Reactive.entryTx.eval i r).getLsbD 0 = Program.Buffered.txBit (base p r i) from
      by simpa [Reactive.entryTx, Expr.eval, starting] using
        txBit p i r (available pin enable invert action operation)]
  all_goals rfl

end Pinwheel.Hardware.Buffered.GenericStart
