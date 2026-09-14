import Pinwheel.Hardware.Reactive.State

namespace Pinwheel.Hardware.Reactive

abbrev E := Expr Input Register
abbrev Bank := {w : Nat} → Register w → E w
abbrev Slots := Fin 16 → E 1

def oldSlots : Slots := fun k => .reg (.sample k)
def zeroSlots : Slots := fun _ => .lit 0
def current : {w : Nat} → Execution.Port w → E w := Execution.logic (.input .current)
def successor : {w : Nat} → Execution.Port w → E w := Execution.logic (.input .successor)
def isMode (m : BitVec 3) : E 1 := .equal (.reg .mode) (.lit m)
def running : E 1 := .band (.inv (.zero (.reg .mode))) (.ult (.reg .mode) (.lit 5))
def hold : Bank := fun r => .reg r

def inputBit (selector : E 1) : E 1 :=
  .mux selector (.slice 1 1 (by decide) (.input .incoming)) (.slice 0 1 (by decide) (.input .incoming))

def captureSlots (bits : E 6) (slots : Slots) : Slots := fun k =>
  .mux (.band (.slice 0 1 (by decide) bits)
      (.equal (.slice 2 4 (by decide) bits) (.lit (BitVec.ofFin k))))
    (inputBit (.slice 1 1 (by decide) bits)) (slots k)

def terminalSlots : Slots := captureSlots (current .terminal) oldSlots

def exitSlots : Slots := fun k => .mux (isMode 3) (terminalSlots k) (oldSlots k)
def entrySlots : Slots := fun k => .mux running (exitSlots k) (.lit 0)

def sequential : E 1 := Execution.bor (.inv (isMode 3)) (.zero (current .finish))

def target : E 8 := .mux running
  (.mux sequential (.sub (.reg .pc) (.lit 255))
    (.mux (.equal (current .finish) (.lit 1)) (current .yes)
      (.mux (Execution.readTree 4 (fun k => terminalSlots k.toFin) (current .sample)) (current .yes) (current .no))))
  (.lit 0)

def inRange : E 1 := .mux sequential (.ult (.reg .pc) (.input .last))
  (.inv (.ult (.input .last) target))

def stop (mode : BitVec 3) (slots : Slots) : Bank
  | _, .mode => .lit mode
  | _, .pc | _, .remaining | _, .waitLeft => .lit 0
  | _, .levels => .input .idleLevels
  | _, .enabled => .input .idleEnabled
  | _, .sample k => slots k

def enterRunning : Bank
  | _, .mode => .mux (.equal (successor .kind) (.lit 0)) (.lit 1)
      (.mux (.equal (successor .kind) (.lit 1)) (.lit 2)
        (.mux (.equal (successor .kind) (.lit 2)) (.lit 3) (.lit 4)))
  | _, .pc => target
  | _, .remaining => successor .duration
  | _, .waitLeft => .mux (.equal (successor .kind) (.lit 3)) (successor .budget) (.lit 0)
  | _, .levels => successor .levels
  | _, .enabled => successor .enabled
  | _, .sample k => captureSlots (successor .entry) entrySlots k

def entry : Bank := fun r => .mux (successor .valid)
  (.mux (.equal (successor .kind) (.lit 4)) (stop 5 entrySlots r) (enterRunning r))
  (stop 7 entrySlots r)

def dispatch : Bank := fun r => .mux inRange (entry r) (stop 7 exitSlots r)

def decrement : Bank
  | _, .remaining => .sub (.reg .remaining) (.lit 1)
  | _, r => .reg r

def guarded : E 1 := .equal
  (.band (.input .incoming) (.slice 0 2 (by decide) (current .check)))
  (.band (.slice 2 2 (by decide) (current .check)) (.slice 0 2 (by decide) (current .check)))

def ready : E 1 := .equal (inputBit (.slice 0 1 (by decide) (current .check)))
  (.slice 1 1 (by decide) (current .check))

def currentKind (kind : BitVec 3) : E 1 := .band (current .valid) (.equal (current .kind) (.lit kind))

def qualifiedProgress : Bank
  | _, .remaining => .sub (.reg .remaining) (.lit 1)
  | _, .waitLeft => current .budget
  | _, r => .reg r

def qualificationRetry : Bank
  | _, .remaining => current .duration
  | _, .waitLeft => .sub (.reg .waitLeft) (.lit 1)
  | _, r => .reg r

def advance : Bank := fun r =>
  .mux (isMode 1)
    (.mux (.zero (.reg .remaining)) (dispatch r) (decrement r))
    (.mux (isMode 2)
      (.mux (currentKind 1)
        (.mux ready (dispatch r)
          (.mux (.zero (.reg .remaining)) (stop 6 oldSlots r) (decrement r)))
        (stop 7 oldSlots r))
      (.mux (isMode 3)
        (.mux (.band (currentKind 2) guarded)
          (.mux (.zero (.reg .remaining)) (dispatch r) (decrement r))
          (stop 7 oldSlots r))
        (.mux (currentKind 3)
          (.mux guarded
            (.mux (.zero (.reg .remaining)) (dispatch r) (qualifiedProgress r))
            (.mux (.zero (.reg .waitLeft)) (stop 6 oldSlots r) (qualificationRetry r)))
          (stop 7 oldSlots r))))

def circuit : Circuit Input Register Output where
  next := fun r => .mux (.input .reset) (stop 0 zeroSlots r)
    (.mux running (advance r) (.mux (.input .start) (entry r) (hold r)))
  output
    | .state r => .reg r
    | .readA => .reg .pc
    | .readB => target
    | .busy => running

def tick (i : Inputs) (s : State) : State := fromValues (circuit.step i.values s.values)

end Pinwheel.Hardware.Reactive
