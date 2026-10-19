import Pinwheel.Hardware.Buffered.GenericCertificate
import Pinwheel.Hardware.Decode

/-! Transport static layout and word checks to the actual packed expression
graph. These are combinational identities, before any execution relation. -/
namespace Pinwheel.Hardware.Buffered.GenericLayoutCircuit
open Pinwheel.Hardware Pinwheel.Program GenericLayout GenericCertificate

theorem sequential_coordinates (i : Values Reactive.Input) (r : Values Reactive.Register)
    (notStarting : Reactive.starting.eval i r = 0) :
    Coordinates.mk (Reactive.sequentialPC.eval i r) (Reactive.sequentialOuter.eval i r)
      (Reactive.sequentialInner.eval i r) = sequential (r .currentControl) (coordinates r) := by
  simp only [Reactive.sequentialPC, Reactive.sequentialOuter, Reactive.sequentialInner,
    Reactive.innerAgain, Reactive.outerAgain,
    Reactive.currentControl, Reactive.controlDepth, Reactive.innerStart, Reactive.outerStart,
    Reactive.innerBound, Reactive.outerBound, Reactive.innerEnd, Reactive.outerEnd,
    Reactive.both, Reactive.increment, Expr.eval, notStarting, sequential, coordinates]
  simp (disch := decide) only [BitVec.extractLsb'_append_eq_of_add_le]
  by_cases inner : (r .inner).toNat < ((r .currentControl).extractLsb' 17 3).toNat
  all_goals by_cases outer : (r .outer).toNat < ((r .currentControl).extractLsb' 8 3).toNat
  all_goals simp only [inner, outer, decide_true, decide_false]
  all_goals congr 1
  all_goals by_cases depth : (r .currentControl).extractLsb' 0 2 = 2#2
  all_goals by_cases innerEnd : (r .currentControl)[21] = true
  all_goals by_cases outerEnd : (r .currentControl)[20] = true
  all_goals simp [Decode.extract_bit, BitVec.sub_eq_add_neg, Bool.beq_eq_decide_eq,
    depth, innerEnd, outerEnd]
  all_goals done
  done

end Pinwheel.Hardware.Buffered.GenericLayoutCircuit
