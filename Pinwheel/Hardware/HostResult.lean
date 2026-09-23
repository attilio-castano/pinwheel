import Pinwheel.Hardware.Chip
import Pinwheel.Hardware.Observer

/-! A one-result mailbox at the chip boundary. The oldest unconsumed result
survives later execution and program replacement. This does not stall the core. -/
namespace Pinwheel.Hardware.HostResult
open Loader

private def collect : {n : Nat} → (Fin n → Expr I R 1) → Expr I R n
  | 0, _ => .lit 0
  | 1, f => f 0
  | n + 2, f => Expr.concat (a := n + 1) (b := 1) (collect (fun k => f k.succ)) (f 0)

private def collectValues : {n : Nat} → (Fin n → BitVec 1) → BitVec n
  | 0, _ => 0
  | 1, f => f 0
  | n + 2, f => collectValues (fun k : Fin (n + 1) => f k.succ) ++ f 0

def sampleValues (o : Values Machine.Output) : BitVec 16 :=
  collectValues (fun k => o (.core (.state (.sample k))))
inductive Register : Nat → Type where
  | resetFirst : Register 1 | resetSecond : Register 1
  | pageFirst : Register 2 | pageSecond : Register 2
  | controlFirst : Register 2 | controlSecond : Register 2
  | consumePrev : Register 1 | clearPrev : Register 1 | wasActive : Register 1
  | samples : Register 16 | outcome : Register 3
  | valid : Register 1 | overrun : Register 1 | rejected : Register 1

structure State where
  resetFirst : Bool := false
  resetSecond : Bool := false
  pageFirst : BitVec 2 := 0
  pageSecond : BitVec 2 := 0
  controlFirst : BitVec 2 := 0
  controlSecond : BitVec 2 := 0
  consumePrev : Bool := false
  clearPrev : Bool := false
  wasActive : Bool := false
  samples : BitVec 16 := 0
  outcome : BitVec 3 := 0
  valid : Bool := false
  overrun : Bool := false
  rejected : Bool := false
  deriving DecidableEq, Repr

def State.values (s : State) : Values Register
  | _, .resetFirst => BitVec.ofBool s.resetFirst | _, .resetSecond => BitVec.ofBool s.resetSecond
  | _, .pageFirst => s.pageFirst | _, .pageSecond => s.pageSecond
  | _, .controlFirst => s.controlFirst | _, .controlSecond => s.controlSecond
  | _, .consumePrev => BitVec.ofBool s.consumePrev | _, .clearPrev => BitVec.ofBool s.clearPrev
  | _, .wasActive => BitVec.ofBool s.wasActive | _, .samples => s.samples | _, .outcome => s.outcome
  | _, .valid => BitVec.ofBool s.valid | _, .overrun => BitVec.ofBool s.overrun
  | _, .rejected => BitVec.ofBool s.rejected

def resetting (i : Chip.Pins) (s : State) : Bool := !(i.rstN && s.resetFirst && s.resetSecond)
def consuming (s : State) : Bool := s.controlSecond.getLsbD 0 && !s.consumePrev
def clearing (s : State) : Bool := s.controlSecond.getLsbD 1 && !s.clearPrev
def arriving (o : Values Machine.Output) (s : State) : Bool :=
  s.wasActive && o (.core .busy) == 0 &&
    (o (.core (.state .mode)) == 5 || o (.core (.state .mode)) == 6 || o (.core (.state .mode)) == 7)
def occupied (s : State) : Bool := s.valid && !consuming s

def next (i : Chip.Pins) (o : Values Machine.Output) (s : State) : State :=
  { resetFirst := i.rstN, resetSecond := s.resetFirst
    pageFirst := i.uiIn.extractLsb' 3 2, pageSecond := s.pageFirst
    controlFirst := i.uiIn.extractLsb' 5 2, controlSecond := s.controlFirst
    consumePrev := if resetting i s then false else s.controlSecond.getLsbD 0
    clearPrev := if resetting i s then false else s.controlSecond.getLsbD 1
    wasActive := if resetting i s then false else o (.core .busy) == 1 || o (.control .start) == 1
    samples := if resetting i s then 0 else if arriving o s && !occupied s
      then sampleValues o else s.samples
    outcome := if resetting i s then 0 else if arriving o s && !occupied s
      then o (.core (.state .mode)) else s.outcome
    valid := !resetting i s && (occupied s || arriving o s)
    overrun := !resetting i s && ((s.overrun && !clearing s) || (arriving o s && occupied s))
    rejected := !resetting i s && ((s.rejected && !clearing s) || o (.control .rejected) == 1) }

abbrev E := Expr (Observed Chip.Pin Machine.Output) Register
def resetExpr : E 1 := .inv (.band (.band (.input (.input .rstN)) (.reg .resetFirst)) (.reg .resetSecond))
def consumeBit : E 1 := .slice 0 1 (by decide) (.reg .controlSecond)
def clearBit : E 1 := .slice 1 1 (by decide) (.reg .controlSecond)
def consumeExpr : E 1 := .band consumeBit (.inv (.reg .consumePrev))
def clearExpr : E 1 := .band clearBit (.inv (.reg .clearPrev))
def busy : E 1 := .input (.output (.core .busy))
def mode : E 3 := .input (.output (.core (.state .mode)))
def arrival : E 1 := .band (.reg .wasActive) (.band (.zero busy)
  (Execution.bor (Execution.bor (.equal mode (.lit 5)) (.equal mode (.lit 6))) (.equal mode (.lit 7))))
def occupiedExpr : E 1 := .band (.reg .valid) (.inv consumeExpr)
def accepts : E 1 := .band arrival (.inv occupiedExpr)

def sampleExpr : E 16 := collect (fun k => .input (.output (.core (.state (.sample k)))))

def resultStatus : E 8 :=
  .concat (.reg Register.outcome) (.concat (.lit (2 : BitVec 2))
    (.concat (.reg Register.rejected) (.concat (.reg Register.overrun) (.reg Register.valid))))

def observer : Observer Chip.Pin Machine.Output Register Chip.Output where
  next := fun r => match r with
    | .resetFirst => .input (.input .rstN) | .resetSecond => .reg .resetFirst
    | .pageFirst => .slice 3 2 (by decide) (.input (.input .uiIn)) | .pageSecond => .reg .pageFirst
    | .controlFirst => .slice 5 2 (by decide) (.input (.input .uiIn)) | .controlSecond => .reg .controlFirst
    | .consumePrev => .mux resetExpr (.lit 0) consumeBit
    | .clearPrev => .mux resetExpr (.lit 0) clearBit
    | .wasActive => .mux resetExpr (.lit 0) (Execution.bor busy (.input (.output (.control .start))))
    | .samples => .mux resetExpr (.lit 0)
        (.mux accepts sampleExpr (.reg .samples))
    | .outcome => .mux resetExpr (.lit 0) (.mux accepts mode (.reg .outcome))
    | .valid => .band (.inv resetExpr) (Execution.bor occupiedExpr arrival)
    | .overrun => .band (.inv resetExpr) (Execution.bor
        (.band (.reg .overrun) (.inv clearExpr)) (.band arrival occupiedExpr))
    | .rejected => .band (.inv resetExpr) (Execution.bor
        (.band (.reg .rejected) (.inv clearExpr)) (.input (.output (.control .rejected))))
  output := fun p => match p with
    | .uoOut => .mux (.equal (.reg .pageSecond) (.lit 1)) (.slice 0 8 (by decide) (.reg .samples))
        (.mux (.equal (.reg .pageSecond) (.lit 2)) (.slice 8 8 (by decide) (.reg .samples))
          (.mux (.equal (.reg .pageSecond) (.lit 3))
            resultStatus
            ((Chip.outputs .uoOut).bind (fun o => .input (.output o)) (fun r => nomatch r))))
    | .uioOut => (Chip.outputs .uioOut).bind (fun o => .input (.output o)) (fun r => nomatch r)
    | .uioOe => (Chip.outputs .uioOe).bind (fun o => .input (.output o)) (fun r => nomatch r)

def netlist (n : Netlist R Machine.Output Machine.Input) :=
  observer.wrap (Chip.pinMap.wrap (Feeder.sampler.wrap (Serial.receiver.wrap n)))

private theorem sampleExpr_correct (o : Values Machine.Output) (i : Chip.Pins) (s : State) :
    sampleExpr.eval (Observed.values i.values o) s.values = sampleValues o := rfl

private theorem bit_value (v : BitVec 1) : BitVec.ofBool (v == 1#1) = v := by
  rcases BitVec.eq_zero_or_eq_one v with h | h <;> simp [h]

private theorem bit_slice (v : BitVec n) (k : Nat) :
    v.extractLsb' k 1 = BitVec.ofBool (v.getLsbD k) := by
  rw [BitVec.getLsbD_eq_extractLsb', bit_value]

private theorem bit_and_one (v : BitVec 1) : v &&& 1#1 = v := BitVec.and_allOnes

theorem next_correct (i : Chip.Pins) (o : Values Machine.Output) (s : State) (r : Register w) :
    (observer.next r).eval (Observed.values i.values o) s.values = (next i o s).values r := by
  cases r
  all_goals simp only [observer, sampleExpr_correct, next, resetExpr, consumeBit, clearBit,
    consumeExpr, clearExpr, busy, mode, arrival, occupiedExpr, accepts, resetting, consuming,
    clearing, arriving, occupied, Execution.bor, Expr.eval, State.values, Chip.Pins.values, Observed.values]
  all_goals simp only [bit_slice, BitVec.ofBool_and_ofBool, BitVec.not_ofBool, Reactive.bool_one,
    Bool.not_and, Bool.not_or, Bool.not_not, Bool.and_assoc, Bool.or_assoc,
    Bool.beq_eq_decide_eq, apply_ite BitVec.ofBool]
  all_goals try rfl
  case rejected =>
    rcases BitVec.eq_zero_or_eq_one (o (.control .rejected)) with h | h
    all_goals simp [h, bit_and_one, BitVec.not_ofBool, BitVec.ofBool_and_ofBool, Bool.not_or,
      Bool.not_and, Bool.and_assoc]
  case wasActive =>
    rcases BitVec.eq_zero_or_eq_one (o (.core .busy)) with hb | hb <;>
      rcases BitVec.eq_zero_or_eq_one (o (.control .start)) with hs | hs
    all_goals simp [hb, hs]

theorem reset_empty (i : Chip.Pins) (o : Values Machine.Output) (s : State)
    (h : resetting i s = true) :
    (next i o s).valid = false ∧ (next i o s).overrun = false ∧
      (next i o s).rejected = false ∧ (next i o s).samples = 0 := by
  simp [next, h]

theorem unread_stable (i : Chip.Pins) (o : Values Machine.Output) (s : State)
    (hr : resetting i s = false) (hv : s.valid = true) (hc : consuming s = false) :
    (next i o s).valid = true ∧ (next i o s).samples = s.samples ∧
      (next i o s).outcome = s.outcome := by
  simp [next, occupied, hr, hv, hc]

def shown (o : Values Machine.Output) (s : State) : Values Chip.Output
  | _, .uoOut => if s.pageSecond == 1 then s.samples.extractLsb' 0 8
      else if s.pageSecond == 2 then s.samples.extractLsb' 8 8
      else if s.pageSecond == 3 then s.outcome ++ ((2 : BitVec 2) ++
        (BitVec.ofBool s.rejected ++ (BitVec.ofBool s.overrun ++ BitVec.ofBool s.valid)))
      else Chip.shown o .uoOut
  | _, .uioOut => Chip.shown o .uioOut
  | _, .uioOe => Chip.shown o .uioOe

theorem output_correct (i : Chip.Pins) (o : Values Machine.Output) (s : State) (p : Chip.Output w) :
    (observer.output p).eval (Observed.values i.values o) s.values = shown o s p := by
  cases p
  all_goals simp only [observer, shown, resultStatus, Chip.shown, Chip.outputs, Expr.eval_bind,
    Expr.eval, Observed.values, State.values]
  all_goals simp only [Bool.beq_eq_decide_eq, Reactive.bool_one]
  rfl

theorem core_unchanged (n : Netlist R Machine.Output Machine.Input) (p : Chip.Pins)
    (r : Values (Chip.Register R)) (s : State) (x : Chip.Register R w) :
    (netlist n).step p.values (Extended.values r s.values) (.inner x) =
      (Chip.netlist n).step p.values r x := by
  simp only [netlist, Observer.inner_step, Chip.netlist, Netlist.mapOutputs_step]
  rfl

def registers : Array (Sigma Register) :=
  #[⟨1, .resetFirst⟩, ⟨1, .resetSecond⟩, ⟨2, .pageFirst⟩, ⟨2, .pageSecond⟩,
    ⟨2, .controlFirst⟩, ⟨2, .controlSecond⟩, ⟨1, .consumePrev⟩, ⟨1, .clearPrev⟩,
    ⟨1, .wasActive⟩, ⟨16, .samples⟩, ⟨3, .outcome⟩, ⟨1, .valid⟩, ⟨1, .overrun⟩, ⟨1, .rejected⟩]

def label : {w : Nat} → Register w → String
  | _, .resetFirst => "result_reset_first" | _, .resetSecond => "result_reset_second"
  | _, .pageFirst => "result_page_first" | _, .pageSecond => "result_page_second"
  | _, .controlFirst => "result_control_first" | _, .controlSecond => "result_control_second"
  | _, .consumePrev => "result_consume_prev" | _, .clearPrev => "result_clear_prev"
  | _, .wasActive => "result_was_active" | _, .samples => "result_samples" | _, .outcome => "result_outcome"
  | _, .valid => "result_valid" | _, .overrun => "result_overrun" | _, .rejected => "result_rejected"

end Pinwheel.Hardware.HostResult
