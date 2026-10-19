import Lean
import Pinwheel.Program.StreamingUARTFirstTerminal

/-! Statement-shape obligations: exact first terminal, arbitrary profile/byte/
selector, real START arming, and no assumed prior phase or captured result. -/
namespace Pinwheel.Test.StreamingUARTFirstTerminal
open Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingUART
open QuietTiming FrameSamples Frame FirstTerminal

example (p : Profile) (s : State a) (start : Input) (marks : List Input)
    (payload : BitVec 8) (incoming : Nat → Input)
    (runtime : start.Runtime) (admitted : (start.command == 3 && s.canStart start) = true)
    (count : start.startCount = 8)
    (markQuiet : ∀ i ∈ marks, Quiet i) (markRaw : ∀ i ∈ marks, i.rawInputs = 3) (long : 6 ≤ marks.length)
    (quiet : ∀ n, Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload)
    (stopHigh : (incoming (38*p.Q)).rawInputs[p.rxInput.val] = true) :
    (run (image p).program s (start :: (marks ++ clocks incoming 0 (38*p.Q+4)))).phase.retained = true ∧
    ∀ earlier, earlier < 38*p.Q+4 →
      (run (image p).program s (start :: (marks ++ clocks incoming 0 earlier))).phase.busy = true := by
  have first := admitted_good_frame_first p s start marks payload incoming runtime admitted count
    markQuiet markRaw long quiet falling startLow samples stopHigh
  simpa only [FirstAt,run,List.foldl_cons,List.foldl_append] using first

example (p : Profile) (generation transfer : BitVec 16) (payload : BitVec 8)
    (incoming : Nat → Input) (quiet : ∀ n, Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload)
    (stopLow : (incoming (38*p.Q)).rawInputs[p.rxInput.val] = false) :
    (run (image p).program (Arm.armed (a := a) p generation transfer)
      (clocks incoming 0 (38*p.Q+3))).phase.retained = true ∧
    ∀ earlier, earlier < 38*p.Q+3 →
      (run (image p).program (Arm.armed (a := a) p generation transfer)
        (clocks incoming 0 earlier)).phase.busy = true :=
  bad_stop_first p generation transfer payload incoming quiet falling startLow samples stopLow

example (p : Profile) (generation transfer : BitVec 16)
    (incoming : Nat → Input) (quiet : ∀ n, Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startHigh : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = true) :
    (run (image p).program (Arm.armed (a := a) p generation transfer)
      (clocks incoming 0 (2*p.Q+3))).phase.retained = true ∧
    ∀ earlier, earlier < 2*p.Q+3 →
      (run (image p).program (Arm.armed (a := a) p generation transfer)
        (clocks incoming 0 earlier)).phase.busy = true :=
  false_start_first p generation transfer incoming quiet falling startHigh

end Pinwheel.Test.StreamingUARTFirstTerminal

open Lean Elab Command
elab "#audit_uart_first_terminal" : command => do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx =>
        let owner := env.header.modules[idx.toNat]!.module.toString
        owner == "Pinwheel" || owner.startsWith "Pinwheel."
      | none => info.isAxiom || info.isTheorem
    if owned then
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax =>
        ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
      unless unexpected.isEmpty do throwError "Unapproved axioms in {name}: {unexpected}"
  if declarations == 0 || theorems == 0 then throwError "Empty UART first-terminal audit"
  logInfo m!"UART first-terminal audit: {declarations} declarations, {theorems} theorems; standard axioms only."
#audit_uart_first_terminal
