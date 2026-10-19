import Pinwheel.Hardware.Buffered.SpiCircuit

/-! Disabled scratch capture leaves the actual packed capture bank unchanged. -/
namespace Pinwheel.Hardware.Buffered.SpiScratch
open Pinwheel.Hardware

theorem capture_zero (bits : Reactive.E 6) (old : Reactive.E 16)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (capture : bits.eval i r = 0) :
    (Reactive.captureBits bits old).eval i r = old.eval i r := by
  apply (BitVec.eq_of_getLsbD_eq_iff).2
  intro index bound
  rw [Reactive.capture_bit_at bits old i r ⟨index, bound⟩]
  simp [Reactive.both, Expr.eval, capture]

theorem entryScratch_zero (i : Values Reactive.Input) (r : Values Reactive.Register)
    (capture : Reactive.entryCapture.eval i r = 0)
    (terminal : Reactive.terminalEdge.eval i r = 0) (scratch : r .scratch = 0) :
    Reactive.entryScratch.eval i r = 0 := by
  have exit : Reactive.exitScratch.eval i r = 0 := by
    simp [Reactive.exitScratch, Expr.eval, terminal, scratch]
  have base : (Expr.mux Reactive.starting (.lit 0) Reactive.exitScratch).eval i r = 0 := by
    simp [Expr.eval, exit]
  have captured := (capture_zero Reactive.entryCapture
    (Expr.mux Reactive.starting (.lit 0) Reactive.exitScratch) i r capture).trans base
  simp only [Reactive.entryScratch, Expr.eval]
  split
  · exact captured
  · exact base

/-- An admitted START clears the scratch base before optional entry capture;
disabled capture therefore establishes zero from arbitrary old scratch. -/
theorem starting_scratch_zero (i : Values Reactive.Input) (r : Values Reactive.Register)
    (starting : Reactive.starting.eval i r = 1)
    (capture : Reactive.entryCapture.eval i r = 0) :
    Reactive.entryScratch.eval i r = 0 := by
  have base : (Expr.mux Reactive.starting (.lit 0) Reactive.exitScratch).eval i r = 0 := by
    simp [Expr.eval, starting]
  have captured := (capture_zero Reactive.entryCapture
    (Expr.mux Reactive.starting (.lit 0) Reactive.exitScratch) i r capture).trans base
  simp only [Reactive.entryScratch, Expr.eval]
  split
  · exact captured
  · rfl

end Pinwheel.Hardware.Buffered.SpiScratch
