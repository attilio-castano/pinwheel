import Pinwheel.Program.StreamingUARTArm
import Pinwheel.Program.StreamingUARTStartFacts
import Pinwheel.Program.StreamingBootPins

/-! A checked physical START exchange. The finite certificate records command
control only; source feedback acceptance is proved separately. -/
namespace Pinwheel.Program.StreamingUART.StartPins
open Pinwheel.Program.StreamingReady
open Pinwheel.Program.Streaming
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

abbrev Control := Host.BootControl.State

def request : BitVec 176 := BootPins.request 3 10 (1#16 ++ (8#16 ++ 0#96))
def pins : List Pinwheel.Program.StreamingReady.Session.Pins := BootPins.transaction request 3

def commandSafe (c : Host.Command) : Bool :=
  !c.runtime.initialize && !c.runtime.txPush && !c.runtime.rxPop && c.runtime.rawInputs == 3

def next (started : Bool) (elapsed : Nat) (c : Host.Command) : Option (Bool × Nat) :=
  if !commandSafe c then none
  else if c.runtime.command == 0 then some (started,elapsed + if started then 1 else 0)
  else if !started && c.runtime.command == 3 && c.runtime.expectedGeneration == 1 && c.runtime.startCount == 8 then
    some (true,0)
  else none

structure Safe (c : Host.Command) : Prop where
  cold : c.runtime.initialize = false
  tx : c.runtime.txPush = false
  rx : c.runtime.rxPop = false
  raw : c.runtime.rawInputs = 3

inductive Delivery (started : Bool) (elapsed : Nat) (c : Host.Command) : Bool → Nat → Prop
  | quiet (safe : Safe c) (command : c.runtime.command = 0) :
      Delivery started elapsed c started (elapsed + if started then 1 else 0)
  | start (safe : Safe c) (before : started = false) (command : c.runtime.command = 3)
      (generation : c.runtime.expectedGeneration = 1) (count : c.runtime.startCount = 8) :
      Delivery started elapsed c true 0

def check : Control → Bool → Nat → List Pinwheel.Program.StreamingReady.Session.Pins → Bool
  | control,started,elapsed,[] => started && decide (6 ≤ elapsed) && control.phase == 0 && !control.active
  | control,started,elapsed,pin::rest =>
      BootPins.controlSafe control &&
      match next started elapsed (Host.BootControl.command (pin.host {}) control) with
      | none => false
      | some (nextStarted,nextElapsed) =>
        check (Host.BootControl.step false (pin.host {}) control) nextStarted nextElapsed rest

inductive Certified : Control → Bool → Nat → List Pinwheel.Program.StreamingReady.Session.Pins → Prop
  | nil (control : Control) (started : Bool) (elapsed : Nat)
      (done : started = true) (long : 6 ≤ elapsed) (phase : control.phase = 0) (inactive : control.active = false) :
      Certified control started elapsed []
  | cons {control started elapsed pin rest nextStarted nextElapsed}
      (safe : Host.BootControl.Safe control)
      (delivery : Delivery started elapsed (Host.BootControl.command (pin.host {}) control) nextStarted nextElapsed)
      (after : Certified (Host.BootControl.step false (pin.host {}) control) nextStarted nextElapsed rest) :
      Certified control started elapsed (pin::rest)

theorem next_sound (started : Bool) (elapsed : Nat) (c : Host.Command) (after : Bool × Nat)
    (checked : next started elapsed c = some after) : Delivery started elapsed c after.1 after.2 := by
  unfold next at checked
  split at checked
  · contradiction
  · rename_i good
    have safe : Safe c := by
      have fields : commandSafe c = true := by simpa using good
      simp only [commandSafe,Bool.and_eq_true,Bool.not_eq_true',beq_iff_eq] at fields
      exact ⟨fields.1.1.1,fields.1.1.2,fields.1.2,fields.2⟩
    split at checked
    · rename_i command
      cases checked
      exact .quiet safe (by simpa using command)
    · split at checked
      · rename_i fields
        simp only [Bool.and_eq_true,Bool.not_eq_true',beq_iff_eq] at fields
        cases checked
        exact .start safe fields.1.1.1 fields.1.1.2 fields.1.2 fields.2
      · contradiction

theorem check_sound (control : Control) (started : Bool) (elapsed : Nat) (samples : List Pinwheel.Program.StreamingReady.Session.Pins)
    (checked : check control started elapsed samples = true) : Certified control started elapsed samples := by
  induction samples generalizing control started elapsed with
  | nil =>
    simp only [check,Bool.and_eq_true,Bool.not_eq_true',beq_iff_eq,decide_eq_true_eq] at checked
    exact .nil _ _ _ checked.1.1.1 checked.1.1.2 checked.1.2 checked.2
  | cons pin rest induction =>
    simp only [check,Bool.and_eq_true] at checked
    cases found : next started elapsed (Host.BootControl.command (pin.host {}) control) with
    | none => simp only [found,Bool.false_eq_true] at checked; exact False.elim checked.2
    | some after =>
      exact .cons (BootPins.controlSafe_sound control checked.1)
        (next_sound _ _ _ after found) (induction _ _ _ (by simpa only [found] using checked.2))

theorem length : pins.length = 245 := rfl

end Pinwheel.Program.StreamingUART.StartPins
