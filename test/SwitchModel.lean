import Pinwheel.Hardware.Switch.Model

open Pinwheel.Hardware
open Pinwheel.Hardware.Switch

namespace SwitchModelTests

def packet (destination : Fin 2) (payload : Nat) : Packet 2 Nat := ⟨destination, payload⟩

def idle (ready : Fin 2 → Bool) : Input 1 2 Nat := ⟨false, fun _ => none, ready⟩

def fill : Input 1 2 Nat :=
  ⟨false, fun k => some (packet 0 (if k = 0 then 10 else 20)), fun _ => false⟩

def first : State 1 2 Nat := step 1 fill initial

def replace : Input 1 2 Nat :=
  ⟨false, fun k => if k = 0 then some (packet 1 11) else none, fun _ => false⟩

def second : State 1 2 Nat := step 1 replace first

/-- A full input can replace its transferred head on the same edge. -/
example : (observe 1 replace first).ready 0 = true := by decide +kernel
example : second.queues 0 = [packet 1 11] := by decide +kernel
example : second.slots 0 = some ⟨0, packet 0 10⟩ := by decide +kernel
example : second.cursor 0 = 1 := by decide +kernel
example : second.queues 1 = [packet 0 20] := by decide +kernel

def third : State 1 2 Nat := step 1 (idle (fun o => o == 1)) second

/-- A blocked output holds its complete delivery while a different output
receives a later packet from the same source. External order is per flow. -/
example : third.slots 0 = second.slots 0 := by decide +kernel
example : third.cursor 0 = second.cursor 0 := by decide +kernel
example : third.slots 1 = some ⟨0, packet 1 11⟩ := by decide +kernel
example : third.queues 1 = [packet 0 20] := by decide +kernel

def fourth : State 1 2 Nat := step 1 (idle (fun _ => true)) third

/-- Consumer acceptance and replacement of an occupied output slot coincide. -/
example : emittedAt (idle (fun _ => true)) third 0 = [⟨0, packet 0 10⟩] := by decide +kernel
example : fourth.slots 0 = some ⟨1, packet 0 20⟩ := by decide +kernel
example : fourth.cursor 0 = 0 := by decide +kernel

def resetInput : Input 1 2 Nat := ⟨true, fun _ => some (packet 0 99), fun _ => true⟩
example : step 1 resetInput fourth = initial := reset_state 1 resetInput fourth rfl
example : observe 1 resetInput fourth = ⟨fun _ => false, fun _ => none⟩ := reset_observe 1 resetInput fourth rfl

def threeFill : Input 2 1 Nat := ⟨false, fun k => some ⟨0, k.val⟩, fun _ => true⟩
def threeIdle : Input 2 1 Nat := ⟨false, fun _ => none, fun _ => true⟩
def three0 : State 2 1 Nat := step 1 threeFill initial
def three1 := step 1 threeIdle three0
def three2 := step 1 threeIdle three1
def three3 := step 1 threeIdle three2

example : three1.slots 0 = some ⟨0, ⟨0, 0⟩⟩ := by decide +kernel
example : three2.slots 0 = some ⟨1, ⟨0, 1⟩⟩ := by decide +kernel
example : three3.slots 0 = some ⟨2, ⟨0, 2⟩⟩ := by decide +kernel
example : three3.cursor 0 = 0 := by decide +kernel

example (depth : Nat) (i : Input n m α) (s : State n m α) (h : Valid depth s) :
    Valid depth (step depth i s) := valid_preserved depth i s h

example (depth : Nat) (i : Input n m α) (s : State n m α) (o : Fin m)
    (hr : i.reset = false) (hd : i.ready o = false) (hv : (s.slots o).isSome = true) :
    (step depth i s).slots o = s.slots o := slot_stalled depth i s o hr hd hv

end SwitchModelTests

def main : IO Unit :=
  IO.println "Switch model: routing, bounds, stalls, replacement, reset and 3-input round-robin tests checked."
