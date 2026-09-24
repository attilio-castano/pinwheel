import Pinwheel.Hardware.Storage.SramSchedule
import Pinwheel.Hardware.Reactive.CaptureRead

/-! The early/late boundary of the existing hybrid fetch loop. These facts
describe information dependence; they do not create timing exceptions or add
registers. `SramSchedule` continues to own the edge and port obligations. -/
namespace Pinwheel.Hardware.Storage.FetchContract
open Pinwheel.Hardware

/-- The next candidate calculation uses only 21 bits of the entered word:
kind, finish and the two targets. Duration, captures, pins and validity do not
belong to this address calculation; execution still checks them separately. -/
theorem entered_metadata (i : Reactive.Inputs) (s : Reactive.State) (word : BitVec 64)
    (b : Bool)
    (hk : (Execution.unpack word).kind = (Execution.unpack i.successor).kind)
    (hf : (Execution.unpack word).finish = (Execution.unpack i.successor).finish)
    (hy : (Execution.unpack word).yes = (Execution.unpack i.successor).yes)
    (hn : (Execution.unpack word).no = (Execution.unpack i.successor).no) :
    Dispatch.entered {i with successor := word} s b = Dispatch.entered i s b := by
  simp only [Dispatch.entered, hk, hf, hy, hn]
  rfl
  done

private theorem clean_finish (word mask : BitVec 64)
    (hm : (~~~mask).extractLsb' 41 2 = BitVec.allOnes 2)
    (hc : Execution.clean word mask = true) : (Execution.unpack word).finish = 0 := by
  have h := congrArg (fun w : BitVec 64 => w.extractLsb' 41 2) (beq_iff_eq.mp hc)
  simpa only [Execution.unpack, BitVec.extractLsb'_and, hm, BitVec.and_allOnes,
    show (0 : BitVec 64).extractLsb' 41 2 = (0 : BitVec 2) from rfl] using h
  done

/-- Valid records outside the checked instruction class have a zero finish
tag. This restricted semantic fact does not justify deleting a mapped path. -/
theorem checked_or_sequential (word : BitVec 64) (hv : Execution.validValue word = true) :
    (Execution.unpack word).kind = 2 ∨ (Execution.unpack word).finish = 0 := by
  simp only [Execution.validValue, Bool.and_eq_true] at hv
  by_cases hk : (Execution.unpack word).kind = 2
  all_goals simp only [hk, ↓reduceIte, true_or, false_or] at hv ⊢
  by_cases h0 : (Execution.unpack word).kind = 0 <;>
    by_cases h1 : (Execution.unpack word).kind = 1 <;>
    by_cases h3 : (Execution.unpack word).kind = 3 <;> simp_all
  all_goals first | exact clean_finish word _ (by decide +kernel) hv.1.1 | decide +kernel
  all_goals done

/-- Under a valid-word premise, finish and target fields suffice. Any future
implementation using this simplification must establish that premise at the
real interface and preserve fault/idle behavior; this theorem alone is not an
arbitrary-state replacement for `Dispatch.enteredExpr`. -/
theorem entered_valid (i : Reactive.Inputs) (s : Reactive.State) (b : Bool)
    (hv : Execution.validValue i.successor = true) :
    Dispatch.entered i s b =
      if (Execution.unpack i.successor).finish = 0 then Reactive.targetValue i s - 255
      else if (Execution.unpack i.successor).finish = 1 then (Execution.unpack i.successor).yes
      else if b then (Execution.unpack i.successor).yes else (Execution.unpack i.successor).no := by
  rcases checked_or_sequential i.successor hv with hk | hf
  all_goals simp_all [Dispatch.entered]
  all_goals done

end Pinwheel.Hardware.Storage.FetchContract
