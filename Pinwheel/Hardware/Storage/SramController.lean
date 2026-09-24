import Pinwheel.Hardware.Storage.ChipBackend
import Pinwheel.Hardware.Storage.Sram
import Pinwheel.Hardware.Memory.Sram

/-! Experimental SRAM controller expressions shared by proofs and emission.
`SramExecution` proves initialized execution with replicated digital SRAM arrays.
The external Verilog macro binding and emitted-chip read-back remain separate. -/
namespace Pinwheel.Hardware.Storage.SramController
open Pinwheel.Hardware Pinwheel.Hardware.Storage Pinwheel.Hardware.Loader
open Pinwheel.Hardware.Storage.Backend (fresh)

/-- SRAM responses pass through the input adapters without being sampled again. -/
inductive Reads (I : Nat → Type) : Nat → Type where
  | base : I w → Reads I w
  | q : Bool → Reads I 64

def bypass (f : Feeder J X I) : Feeder (Reads J) X (Reads I) where
  input := fun p => match p with
    | .base p => (f.input p).bind (fun q => .input (.base q)) (.reg)
    | .q b => .input (.q b)
  next := fun r => (f.next r).bind (fun q => .input (.base q)) (.reg)

inductive Port : Nat → Type where
  | address : Bool → Port 9
  | data : Port 64
  | write : Port 1
  | read : Port 1

inductive Out (O : Nat → Type) : Nat → Type where
  | base : O w → Out O w
  | port : Port w → Out O w

inductive Extra : Nat → Type where
  | scratch : BitVec 5 → Extra 55
  | startWord : Extra 64
  | startPending : Extra 1

abbrev Register := Extended Backend.Register Extra
abbrev Input := Reads Machine.Input
abbrev E := Expr Input Register
abbrev W := WithWire Input 64

def inject (e : Expr Machine.Input Register w) : E w :=
  e.bind (fun p => .input (.base p)) (.reg)

def base (e : Expr Machine.Input Backend.Register w) : E w :=
  e.bind (fun p => .input (.base p)) (fun r => .reg (.inner r))

def liftW (e : Expr Backend.Policy.WS Backend.Register w) : Expr W Register w :=
  e.bind (fun p => match p with
    | .input p => .input (.input (.base p))
    | .wire => .input .wire) (fun r => .reg (.inner r))

def sched (e : Reactive.E w) : Expr W Register w := liftW (Backend.Policy.schedW e)
def commit : E 1 := inject Backend.Policy.commit
def selected : E 1 := base Backend.BankSelect.selected
def cursor : E 9 := .reg (.inner (.control .cursor))
def push : E 1 := base (Backend.BankSelect.lift (Cache.liftExpr Machine.pushGate))
def dictionaryWrite : E 1 := .band push (.ult cursor (.lit 32))
def indexWrite : E 1 := .band push (.band (.inv (.ult cursor (.lit 64))) (.ult cursor (.lit 320)))
def write (direct : Bool) : E 1 := if direct then indexWrite else dictionaryWrite

/-- A commit reads word zero on that edge. Its response bypasses the saved
start word on the following edge, so commit immediately followed by start is
legal. Saving it then protects subsequent restarts during inactive-bank writes. -/
def successor : E 64 :=
  Sram.successorExpr (inject Backend.Policy.running) (inject Backend.Policy.branch)
    (fun b => .input (.q b))
    (Sram.startExpr (.reg (.extra .startPending)) (.input (.q false)) (.reg (.extra .startWord)))

def address0 : Expr W Register 8 :=
  .mux (sched Dispatch.dispatchingExpr) (sched (Dispatch.enteredExpr false))
    (.mux (fresh commit) (.lit 0) (sched (Dispatch.heldExpr false)))

def readAddress (direct : Bool) (b : Bool) : Expr W Register 9 :=
  let pc := if b then sched (Dispatch.candidateExpr true) else address0
  if direct then .concat (fresh selected) pc else
    let index : Expr W Register 5 := .mux (fresh selected)
      (Execution.readTree 8 (fun k => .reg (.inner (.index true k))) pc)
      (Execution.readTree 8 (fun k => .reg (.inner (.index false k))) pc)
    .concat (.lit (0#3)) (.concat (fresh selected) index)

def writeAddress (direct : Bool) : E 9 :=
  let bank : E 1 := .inv (.reg (.inner (.control .active)))
  if direct then .concat bank (.slice 0 8 (by decide) (.sub cursor (.lit 64)))
  else .concat (.lit (0#3)) (.concat bank (.slice 0 5 (by decide) cursor))

def writeData (direct : Bool) : E 64 :=
  if direct then Dense.expandExpr (Execution.readTree 5
    (fun k => .reg (.extra (.scratch k))) (.slice 0 5 (by decide) (.input (.base .data))))
  else .input (.base .data)

def request (direct : Bool) : {w : Nat} → Port w → Expr W Register w
  | _, .address b => .mux (fresh (write direct)) (fresh (writeAddress direct)) (readAddress direct b)
  | _, .data => fresh (writeData direct)
  | _, .write => fresh (write direct)
  | _, .read => .inv (fresh (write direct))

def body (direct : Bool) : Circuit W Register (Out Machine.Output) where
  next := fun r => match r with
    | .inner r => liftW (Backend.Policy.core.next r)
    | .extra r => match r with
      | .startPending => fresh commit
      | .startWord => Sram.startExpr (.reg (.extra .startPending))
          (.input (.input (.q false))) (.reg (.extra .startWord))
      | .scratch k => .mux
          (fresh (.band dictionaryWrite (.equal cursor (.lit (BitVec.ofNat 9 k.toNat)))))
          (fresh (Dense.compressExpr (.input (.base .data)))) (.reg (.extra (.scratch k)))
  output := fun o => match o with
    | .base o => liftW (Backend.Policy.core.output o)
    | .port p => request direct p

def core (direct : Bool) : Netlist Register (Out Machine.Output) Input :=
  .letWire successor (.finish (body direct))


def inputValues (i : Machine.Inputs) (q : Bool → BitVec 64) : Values Input
  | _, .base p => i.values p
  | _, .q b => q b

def registerValues (s : Backend.State) (extra : Values Extra) : Values Register
  | _, .inner r => s.values r
  | _, .extra r => extra r

theorem base_eval (e : Expr Machine.Input Backend.Register w) (i : Machine.Inputs)
    (s : Backend.State) (q : Bool → BitVec 64) (extra : Values Extra) :
    (base e).eval (inputValues i q) (registerValues s extra) = e.eval i.values s.values := by
  simp only [base, Expr.eval_bind, Expr.eval, inputValues, registerValues]

theorem liftW_eval (e : Expr Backend.Policy.WS Backend.Register w) (i : Machine.Inputs)
    (s : Backend.State) (q : Bool → BitVec 64) (extra : Values Extra) (word : BitVec 64) :
    (liftW e).eval (WithWire.values (inputValues i q) word) (registerValues s extra) =
      e.eval (WithWire.values i.values word) s.values := by
  simp only [liftW, Expr.eval_bind, Expr.eval, registerValues]
  congr 1
  funext w p
  cases p <;> rfl
  done

/-- The emitted controller uses the same accepted-cursor transition as the
loader contract, independently of the current SRAM response words. -/
theorem control_next (i : Machine.Inputs) (s : Backend.State) (q : Bool → BitVec 64)
    (extra : Values Extra) (r : Loader.Register w) :
    (core false).step (inputValues i q) (registerValues s extra) (.inner (.control r)) =
      (Loader.next (Machine.controlInput (Backend.adapt i s) s.reference.machine) s.control).values r := by
  simp only [core, Netlist.step, Circuit.step, body, liftW_eval]
  exact Backend.Policy.core_step _ i s (.control r)

/-- The emitted hybrid write enable agrees with the response model after the
existing capacity/admission input adaptation. -/
theorem hybrid_write_correct (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values Extra) :
    (write false).eval (inputValues i q) (registerValues s extra) =
      BitVec.ofBool (Sram.writing (Backend.adapt i s) s.reference.machine) := by
  simp only [write, Bool.false_eq_true, if_false, dictionaryWrite, push, Expr.eval, base_eval]
  rw [Backend.BankSelect.lift_correct, Cache.lift_correct]
  simp only [Machine.pushGate, Expr.eval_bind, Machine.control_correct,
    Machine.controlReg, Expr.eval, Machine.State.values, Loader.push_correct]
  simp [Sram.writing, cursor, Expr.eval, registerValues, Backend.State.values,
    Loader.State.values, Backend.State.reference, Backend.State.small, Small.State.reference]

/-- These are the actual core output ports consumed by the Verilog binding. -/
def portValues (direct : Bool) (i : Values Input) (s : Values Register) : Values Port :=
  fun p => (core direct).observe i s (.port p)

theorem read_write_exclusive (direct : Bool) (i : Values Input) (s : Values Register) :
    portValues direct i s .read = ~~~portValues direct i s .write := rfl

theorem hybrid_port_write (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values Extra) :
    portValues false (inputValues i q) (registerValues s extra) .write =
      BitVec.ofBool (Sram.writing (Backend.adapt i s) s.reference.machine) := by
  exact hybrid_write_correct i s q extra

/-- The hybrid binding consumes the low six bits of the nine-bit address port. -/
theorem hybrid_write_address (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values Extra) :
    ((writeAddress false).eval (inputValues i q) (registerValues s extra)).extractLsb' 0 6 =
      Memory.Sram.bankAddress (!s.control.active) (s.control.cursor.extractLsb' 0 5) := by
  cases h : s.control.active <;> simp [writeAddress, Expr.eval, registerValues,
    Backend.State.values, Loader.State.values, cursor, Memory.Sram.bankAddress, h]
  all_goals exact BitVec.extractLsb'_append_eq_right

/-- Logical requests corresponding to the hybrid binding's address truncation.
Write addresses/data are broadcast; the two reads use independent addresses. -/
def hybridRequest (i : Values Input) (s : Values Register) : Memory.Request 6 64 2 :=
  ⟨⟨decide ((write false).eval i s = 1), ((writeAddress false).eval i s).extractLsb' 0 6,
      (writeData false).eval i s⟩,
    fun port => ((readAddress false (port.val == 1)).eval
      (WithWire.values i (successor.eval i s)) s).extractLsb' 0 6⟩

/-- Both physical address ports select the broadcast write address on writes,
and the corresponding independent read address otherwise. -/
theorem hybrid_port_address (i : Values Input) (s : Values Register) (b : Bool) :
    (portValues false i s (.address b)).extractLsb' 0 6 =
      if (hybridRequest i s).write.enable then (hybridRequest i s).write.address
      else (hybridRequest i s).read (if b then 1 else 0) := by
  cases b <;> simp [portValues, core, Netlist.observe, Circuit.observe, body,
    request, Expr.eval, Backend.fresh_correct, hybridRequest, apply_ite]
  all_goals split <;> simp_all

/-- The actual hybrid address expression makes every upload write leave the
active bank of every physical copy unchanged, regardless of initial contents. -/
theorem hybrid_preserves_active (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values Extra)
    (arrays : Fin 2 → Memory.Sram.State 6 64) (port : Fin 2) (k : BitVec 5) :
    (Memory.Sram.step (hybridRequest (inputValues i q) (registerValues s extra)) arrays port).contents
        (Memory.Sram.bankAddress s.control.active k) =
      (arrays port).contents (Memory.Sram.bankAddress s.control.active k) := by
  simpa only [Memory.Sram.step, hybridRequest, hybrid_write_address] using
    Memory.Sram.inactive_write_preserves_active (arrays port) s.control.active
      (s.control.cursor.extractLsb' 0 5) k
      ((writeData false).eval (inputValues i q) (registerValues s extra))
      (decide ((write false).eval (inputValues i q) (registerValues s extra) = 1))
      ((hybridRequest (inputValues i q) (registerValues s extra)).read port)

theorem hybrid_request_enable (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values Extra) :
    (hybridRequest (inputValues i q) (registerValues s extra)).write.enable =
      Sram.writing (Backend.adapt i s) s.reference.machine := by
  simp [hybridRequest, hybrid_write_correct]

/-- A commit drives the physical read enable, so its first-word response can
feed the existing immediate-start bypass on the following edge. -/
theorem hybrid_commit_reads (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values Extra)
    (hc : Machine.committing (Backend.adapt i s) s.reference.machine = true) :
    portValues false (inputValues i q) (registerValues s extra) .read = 1 := by
  rw [read_write_exclusive, hybrid_port_write]
  simpa using congrArg BitVec.ofBool (Sram.commit_reads (Backend.adapt i s) s.reference.machine hc)

theorem selected_eval (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values Extra) :
    selected.eval (inputValues i q) (registerValues s extra) =
      BitVec.ofBool (Machine.selected (Backend.adapt i s) s.reference.machine) := by
  simp only [selected, base_eval, Backend.BankSelect.selected,
    Backend.BankSelect.lift_correct, Cache.lift_correct, Machine.selected_correct]

/-- Each hybrid read uses the selected bank's five-bit index at the controller's
chosen program address. Selection includes the new bank on the commit edge. -/
theorem hybrid_read_address (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values Extra) (word : BitVec 64) (b : Bool) :
    let bank := Machine.selected (Backend.adapt i s) s.reference.machine
    let pc := (if b then sched (Dispatch.candidateExpr true) else address0).eval
      (WithWire.values (inputValues i q) word) (registerValues s extra)
    ((readAddress false b).eval (WithWire.values (inputValues i q) word)
      (registerValues s extra)).extractLsb' 0 6 =
        Memory.Sram.bankAddress bank ((s.indices bank)[pc.toNat]) := by
  simp only [readAddress, Bool.false_eq_true, if_false, Expr.eval, Backend.fresh_correct,
    selected_eval, Execution.readTree_correct, registerValues, Backend.State.values]
  cases h : Machine.selected (Backend.adapt i s) s.reference.machine <;>
    simp [Memory.Sram.bankAddress]
  all_goals exact BitVec.extractLsb'_append_eq_right

theorem hybrid_port_data (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values Extra) :
    portValues false (inputValues i q) (registerValues s extra) .data = i.data := rfl

/-- Each accepted dictionary write initializes the addressed inactive-bank
word in both copies with the actual host data word. -/
theorem hybrid_broadcast_write (i : Machine.Inputs) (s : Backend.State)
    (q : Bool → BitVec 64) (extra : Values Extra)
    (arrays : Fin 2 → Memory.Sram.State 6 64) (port : Fin 2)
    (hw : Sram.writing (Backend.adapt i s) s.reference.machine = true) :
    (Memory.Sram.step (hybridRequest (inputValues i q) (registerValues s extra)) arrays port).contents
        (Memory.Sram.bankAddress (!s.control.active) (s.control.cursor.extractLsb' 0 5)) = i.data := by
  have hrequest : (hybridRequest (inputValues i q) (registerValues s extra)).write.enable = true :=
    (hybrid_request_enable i s q extra).trans hw
  simpa only [hybridRequest, hybrid_write_address, writeData, Bool.false_eq_true, if_false,
    Expr.eval, inputValues, Machine.Inputs.values] using
    Memory.Sram.broadcast_write (hybridRequest (inputValues i q) (registerValues s extra)) arrays hrequest port

end Pinwheel.Hardware.Storage.SramController
