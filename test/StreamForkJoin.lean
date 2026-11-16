import Pinwheel.Hardware.Stream.ForkJoin
import Pinwheel.Hardware.Stream.Queue

open Pinwheel.Hardware Pinwheel.Hardware.Stream

def leftBranch := elastic (fun n : Nat => n + 1)
def rightBranch := elastic (fun n : Nat => n * 2)
def pairMachine := Parallel.machine leftBranch rightBranch Prod.mk
def pairContract := Parallel.contract (elasticContract (fun n : Nat => n + 1))
  (elasticContract (fun n : Nat => n * 2)) Prod.mk

example (inputs : List (Input Nat)) :
    let result := runHistory pairMachine.component (none, none) {} inputs
    result.2.inputs.map (fun n => (n + 1, n * 2)) =
      result.2.outputs ++ pairContract.pending result.1 :=
  pairContract.history _ _ ⟨True.intro, True.intro, rfl⟩ rfl inputs

/-- A ready branch must not take an input that the blocked branch cannot take. -/
example : accepted (⟨false, forkOffer (some 7) false, true⟩ : Input Nat)
    (⟨true, none⟩ : Output Nat) = [] := rfl

/-- A join waits for both sides, even if the downstream consumer is ready. -/
example : emitted (⟨false, none, true && (none : Option Nat).isSome⟩ : Input Nat)
    ⟨true, some 7⟩ = [] := rfl
