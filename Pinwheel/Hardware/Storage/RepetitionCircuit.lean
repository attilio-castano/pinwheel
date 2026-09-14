import Pinwheel.Hardware.Storage.Repetition

namespace Pinwheel.Hardware.Storage.Repetition

inductive Register : Nat → Type where
  | template : Fin 15 → Register 64
  | byte : BitVec 1 → Register 8
  | descriptor : Fin 4 → Register 8
inductive Input : Nat → Type where | address : Input 8
inductive Cut : Nat → Type where
  | template : Cut 4 | byte : Cut 1 | bit : Cut 3
  | serial : Cut 1 | ackCapture : Cut 1 | ackFinish : Cut 1 | padding : Cut 1

def Image.values (m : Image) : Values Register
  | _, .template k => m.templates[k.val] | _, .byte k => m.bytes[k.toNat]
  | _, .descriptor k => m.descriptors[k.val]
def Location.values (l : Location) : Values Cut
  | _, .template => l.template | _, .byte => l.byte | _, .bit => l.bit
  | _, .serial => BitVec.ofBool l.serial | _, .ackCapture => BitVec.ofBool l.ackCapture
  | _, .ackFinish => BitVec.ofBool l.ackFinish | _, .padding => BitVec.ofBool l.padding

def locations {w : Nat} (p : Cut w) : Expr Input Register w :=
  let pc : Expr Input Register 8 := .input .address
  let start : Expr Input Register 8 := .reg (.descriptor 0)
  let span : Expr Input Register 8 := .reg (.descriptor 1)
  let bits : Expr Input Register 8 := .reg (.descriptor 2)
  let stop : Expr Input Register 8 := .reg (.descriptor 3)
  let offset := Expr.sub pc start
  let second := Expr.inv (.ult offset span)
  let within := Expr.mux second (.sub offset span) offset
  let body := Expr.band (.inv (.ult pc start)) (.ult pc stop)
  match p with
    | .template => .mux (.ult pc start) (.slice 0 4 (by decide) pc)
        (.mux (.ult pc stop)
          (.mux (.ult within bits)
            (.sub (.concat (.lit (0#2)) (.slice 0 2 (by decide) within : Expr Input Register 2)) (.lit 14))
            (.sub (.concat (.lit (0#2)) (.slice 0 2 (by decide) (.sub within bits) : Expr Input Register 2)) (.lit 10)))
          (.sub (.slice 0 4 (by decide) (.sub pc stop)) (.lit 6)))
    | .byte => second
    | .bit => .inv (.slice 2 3 (by decide) within)
    | .serial => .band body (.ult within bits)
    | .ackCapture => .band body (.equal within (.sub bits (.lit 254)))
    | .ackFinish => .band (.band body (.equal within (.sub bits (.lit 253)))) second
    | .padding => .inv (.ult pc (.sub stop (.lit 251)))

def body : Expr Cut Register 64 :=
  let word : Expr Cut Register 64 := Execution.readTree 4
    (fun k => if h : k.toNat < 15 then .reg (.template ⟨k.toNat, h⟩) else .lit 4) (.input .template)
  let data : Expr Cut Register 8 := Execution.readTree 1 (fun k => .reg (.byte k)) (.input .byte)
  let bit : Expr Cut Register 1 := Execution.readTree 3
    (fun k => .slice k.toNat 1 (by have := k.isLt; omega) data) (.input .bit)
  let word := Expr.mux (.input .serial)
    (.concat (.concat (.slice 8 56 (by decide) word) (.inv bit)) (.slice 0 7 (by decide) word : Expr Cut Register 7)) word
  let word := Expr.mux (.input .ackCapture)
    (.concat (.concat (.slice 38 26 (by decide) word) (.input .byte : Expr Cut Register 1))
      (.slice 0 37 (by decide) word : Expr Cut Register 37)) word
  let word := Expr.mux (.input .ackFinish) (.concat (.lit (0#23)) (.slice 0 41 (by decide) word : Expr Cut Register 41)) word
  .mux (.input .padding) (.lit 4) word

def reader : Expr Input Register 64 := body.bind locations (fun r => .reg r)

set_option backward.isDefEq.respectTransparency false in
theorem locations_correct (m : Image) (pc : BitVec 8) (p : Cut w) :
    (locations p).eval (fun .address => pc) m.values = (locate m pc).values p := by
  cases p <;> simp [locations, Expr.eval, Image.values, locate, Location.values, Bool.beq_eq_decide_eq]
  all_goals rfl
  done

set_option backward.isDefEq.respectTransparency false in
theorem body_correct (m : Image) (l : Location) :
    body.eval l.values m.values = patch
      (if h : l.template.toNat < 15 then m.templates[l.template.toNat] else 4) m l := by
  by_cases ht : l.template.toNat < 15 <;>
    simp [body, Execution.readTree_correct, Expr.eval, Location.values, Image.values, patch, ht]
  done

theorem reader_correct (m : Image) (pc : BitVec 8) :
    reader.eval (fun .address => pc) m.values = read m pc := by
  simp [reader, Expr.eval_bind, locations_correct, Expr.eval, body_correct, read]
  done

end Pinwheel.Hardware.Storage.Repetition
