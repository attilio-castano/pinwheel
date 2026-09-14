import Pinwheel.Hardware.Storage.RepetitionCircuit

namespace Pinwheel.Hardware.Storage.Repetition

inductive BankRegister : Nat → Type where
  | field : Register w → BankRegister w
  | idle : BankRegister 6 | last : BankRegister 8

def registers : Array (Sigma Register) :=
  Array.ofFn (fun k : Fin 15 => ⟨64, .template k⟩) ++
  Array.ofFn (fun k : Fin 2 => ⟨8, .byte (BitVec.ofFin k)⟩) ++
  Array.ofFn (fun k : Fin 4 => ⟨8, .descriptor k⟩)
def bankRegisters : Array (Sigma BankRegister) := registers.map (fun ⟨w,r⟩ => ⟨w, .field r⟩) ++ #[⟨6,.idle⟩,⟨8,.last⟩]
def label : {w : Nat} → Register w → String
  | _, .template k => s!"template{k.val}" | _, .byte k => s!"byte{k.toNat}"
  | _, .descriptor k => s!"descriptor{k.val}"
def bankLabel : {w : Nat} → BankRegister w → String
  | _, .field r => label r | _, .idle => "idle" | _, .last => "last"
def offset : BankRegister w → BitVec 9
  | .field (.template k) => BitVec.ofNat 9 k.val
  | .field (.byte k) => BitVec.ofNat 9 (15+k.toNat)
  | .field (.descriptor k) => BitVec.ofNat 9 (17+k.val)
  | .idle => 320 | .last => 321

def layout (c : BitVec 9) (data : BitVec 64) : Bool :=
  if c.toNat < 15 then true else if c.toNat < 17 then data.toNat < 256
  else if c.toNat < 21 then data == (if c == 17 then 2 else if c == 18 then 36 else if c == 19 then 32 else 74)
  else if c.toNat < 320 then data == 4 else true

def host (i : Loader.Inputs) (c : BitVec 9) : Loader.Inputs :=
  {i with command := if i.command == 2 && !layout c i.data then 6 else i.command
          data := if !(c.toNat < 15) && c.toNat < 64 then 4 else i.data}

abbrev H := Expr Loader.Machine.Input Loader.Machine.Register

def layoutGate : H 1 :=
  let c : H 9 := .reg (.control .cursor)
  let data : H 64 := .input .data
  .mux (.ult c (.lit 15)) (.lit 1)
    (.mux (.ult c (.lit 17)) (.ult data (.lit 256))
      (.mux (.ult c (.lit 21))
        (.equal data (.mux (.equal c (.lit 17)) (.lit 2)
          (.mux (.equal c (.lit 18)) (.lit 36) (.mux (.equal c (.lit 19)) (.lit 32) (.lit 74)))))
        (.mux (.ult c (.lit 320)) (.equal data (.lit 4)) (.lit 1))))

def hostCommand : H 3 :=
  .mux (.band (.equal (.input .command) (.lit 2)) (.inv layoutGate)) (.lit 6) (.input .command)
def hostData : H 64 :=
  .mux (.band (.inv (.ult (.reg (.control .cursor)) (.lit 15)))
    (.ult (.reg (.control .cursor)) (.lit 64))) (.lit 4) (.input .data)

set_option backward.isDefEq.respectTransparency false in
theorem layout_correct (i : Loader.Machine.Inputs) (s : Loader.Machine.State) :
    layoutGate.eval i.values s.values = BitVec.ofBool (layout s.control.cursor i.data) := by
  by_cases h15 : s.control.cursor.toNat < 15 <;> by_cases h17 : s.control.cursor.toNat < 17 <;>
    by_cases h21 : s.control.cursor.toNat < 21 <;> by_cases h320 : s.control.cursor.toNat < 320 <;>
    simp [h15, h17, h21, h320, layoutGate, layout, Expr.eval, Loader.Machine.Inputs.values, Loader.Machine.State.values,
    Loader.State.values, Bool.beq_eq_decide_eq]
  done

set_option backward.isDefEq.respectTransparency false in
theorem command_correct (i : Loader.Machine.Inputs) (s : Loader.Machine.State) :
    hostCommand.eval i.values s.values = (host (Loader.Machine.controlInput i s) s.control.cursor).command := by
  simp [hostCommand, Expr.eval, layout_correct, host, Loader.Machine.Inputs.values,
    Loader.Machine.controlInput, Bool.beq_eq_decide_eq]
  done

set_option backward.isDefEq.respectTransparency false in
theorem data_correct (i : Loader.Machine.Inputs) (s : Loader.Machine.State) :
    hostData.eval i.values s.values = (host (Loader.Machine.controlInput i s) s.control.cursor).data := by
  simp [hostData, Expr.eval, host, Loader.Machine.Inputs.values, Loader.Machine.State.values,
    Loader.State.values, Loader.Machine.controlInput]
  done

def write (i : Loader.Store.Inputs) (s : Values BankRegister) : Values BankRegister := fun {w} r =>
  if i.write && i.cursor == offset r then i.data.extractLsb' 0 w else s r

def next (r : BankRegister w) : Expr Loader.Store.Input BankRegister w :=
  .mux (.band (.input .write) (.equal (.input .cursor) (.lit (offset r))))
    (.slice 0 w (by cases r with | field r => cases r <;> decide | idle => decide | last => decide) (.input .data)) (.reg r)

set_option backward.isDefEq.respectTransparency false in
theorem write_correct (i : Loader.Store.Inputs) (s : Values BankRegister) (r : BankRegister w) :
    (next r).eval i.values s = write i s r := by
  simp [next, write, Expr.eval, Loader.Store.Inputs.values, Bool.beq_eq_decide_eq]
  done

theorem active_preserved (push active : Bool) (cursor : BitVec 9) (data : BitVec 64)
    (s : Bool → Values BankRegister) (r : BankRegister w) :
    write ⟨push && (active != active), cursor, data, 0⟩ (s active) r = s active r := by
  simp [write]
  done

end Pinwheel.Hardware.Storage.Repetition
