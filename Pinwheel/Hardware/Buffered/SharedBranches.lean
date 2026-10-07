import Pinwheel.Hardware.Buffered.Reactive

/-! Experimental storage adapter for the counted reactive circuit. The execution
equations are reused by expression substitution. Rows hold a four-bit reference
to a separately uploaded full 56-bit branch descriptor; the dictionary has
sixteen entries and every entry must be written in the pending generation.
The shared lookup is factored after row selection without adding an edge. -/
namespace Pinwheel.Hardware.Buffered.SharedBranches
open Pinwheel.Hardware
abbrev Base := Reactive.Register
abbrev Input := Reactive.Input
abbrev Output := Reactive.Output

inductive Register : Nat → Type where
  | row : BitVec 6 → Register 92
  | branch : BitVec 4 → Register 56
  | branchWritten : Register 16
  | core : Base w → Register w

abbrev E := Expr Input Register

def both (a b : E 1) : E 1 := .band a b
def pack : {n : Nat} → (Fin n → E 1) → E n
  | 0, _ => .lit 0
  | 1, f => f 0
  | n+2, f => Expr.concat (a := n+1) (b := 1) (pack (fun k => f k.succ)) (f 0)

def branchAt (k : E 4) : E 56 :=
  Execution.readTree 4 (fun a => .reg (.branch a)) k

def expandRow (row : E 92) : E 144 :=
  .concat (branchAt (.slice 88 4 (by decide) row)) (.slice 0 88 (by decide) row)

def registerExpr : {w : Nat} → Base w → E w
  | _, .word k => expandRow (.reg (.row k))
  | _, r => .reg (.core r)

def expandState (s : Values Register) : Values Base
  | _, .word k => s (.branch ((s (.row k)).extractLsb' 88 4)) ++ (s (.row k)).extractLsb' 0 88
  | _, r => s (.core r)

def raw (e : Reactive.E w) : E w := e.bind (fun p => .input p) registerExpr
def cmd (n : BitVec 3) : E 1 := .equal (.input .command) (.lit n)
def rowShape : E 1 := .zero (.slice 4 52 (by decide) (.input .branch))
def tableShape : E 1 := .zero (.slice 4 2 (by decide) (.input .address))
def tableCovered : E 1 := .equal (.reg .branchWritten) (.lit 65535)
def free : E 1 := raw Reactive.free
def resetting : E 1 := raw Reactive.resetting

/-- Table writes are represented as row writes only to the inherited control
equations. The actual row and both coverage masks have adapter updates below. -/
def inputExpr : {w : Nat} → Input w → E w
  | _, .command => .mux (cmd 6)
      (.mux tableShape (.lit 1) (.lit 6))
      (.mux (both (cmd 1) (.inv rowShape)) (.lit 6)
        (.mux (both (cmd 2) (.inv tableCovered)) (.lit 6) (.input .command)))
  | _, .branch => .mux (cmd 1) (branchAt (.slice 0 4 (by decide) (.input .branch))) (.input .branch)
  | _, p => .input p

def mappedInput (i : Values Input) (s : Values Register) : Values Input := fun p =>
  (inputExpr p).eval i s

/-! A small typed factorization. A tree selecting old full rows becomes a tree
selecting compact rows, followed by one dictionary lookup. Every other Expr
constructor is translated exactly as Expr.bind. -/
inductive Rewritten : Nat → Type where
  | plain : E w → Rewritten w
  | packed : E 92 → Rewritten 144

def Rewritten.expression : Rewritten w → E w
  | .plain e => e
  | .packed e => expandRow e

def merge (c : E 1) (t f : Rewritten w) : Rewritten w :=
  match t, f with
  | .packed x, .packed y => .packed (.mux c x y)
  | t, f => .plain (.mux c t.expression f.expression)

def rewrite : Reactive.E w → Rewritten w
  | .input p => .plain (inputExpr p)
  | .reg (.word k) => .packed (.reg (.row k))
  | .reg r => .plain (.reg (.core r))
  | .lit v => .plain (.lit v)
  | .concat x y => .plain (.concat (rewrite x).expression (rewrite y).expression)
  | .inv x => .plain (.inv (rewrite x).expression)
  | .band x y => .plain (.band (rewrite x).expression (rewrite y).expression)
  | .sub x y => .plain (.sub (rewrite x).expression (rewrite y).expression)
  | .slice start len h x => .plain (.slice start len h (rewrite x).expression)
  | .equal x y => .plain (.equal (rewrite x).expression (rewrite y).expression)
  | .ult x y => .plain (.ult (rewrite x).expression (rewrite y).expression)
  | .zero x => .plain (.zero (rewrite x).expression)
  | .mux c t f => merge (rewrite c).expression (rewrite t) (rewrite f)

/-! Executable graph-sharing optimization. The kernel still sees the ordinary
rewrite above. A per-adaptation cache retains source expression objects, checks
cached widths, and expands each packed node at most once. Finite evaluation and
emitter parity checks guard this implementation boundary; no universal native
correctness theorem is claimed. -/
namespace MemoAdapt
structure Entry (w : Nat) where
  rewritten : Rewritten w
  expression : Option (E w) := none

structure Cache where
  entries : Std.HashMap (Nat × USize) (Sigma Entry) := {}
  retained : Array (Sigma Reactive.E) := #[]

abbrev M := StateM Cache

private def checked (w : Nat) : Sigma Entry → Option (Entry w)
  | ⟨v, e⟩ => if h : v = w then some (h ▸ e) else none

private unsafe def force (e : Reactive.E w) (r : Rewritten w) : M (E w) := do
  let key := (w, ptrAddrUnsafe e)
  if let some entry := ((← get).entries[key]?).bind (checked w) then
    if let some value := entry.expression then return value
  let value := r.expression
  modify fun s => {s with entries := s.entries.insert key ⟨w, ⟨r, some value⟩⟩}
  return value

private unsafe def merged (c : E 1) (told fold : Reactive.E w)
    (t f : Rewritten w) : M (Rewritten w) :=
  match t, f with
    | .packed x, .packed y => pure (.packed (.mux c x y))
    | t, f => do
      let et ← force told t
      let ef ← force fold f
      pure (.plain (.mux c et ef))

private unsafe def visit (e : Reactive.E w) : M (Rewritten w) := do
  let key := (w, ptrAddrUnsafe e)
  if let some entry := ((← get).entries[key]?).bind (checked w) then
    return entry.rewritten
  -- The same source object stays alive throughout this rewrite invocation.
  modify fun s => {s with retained := s.retained.push ⟨w, e⟩}
  let value ← (match (motive := (w : Nat) → Reactive.E w → M (Rewritten w)) w, e with
    | _, .input p => pure (.plain (inputExpr p))
    | _, .reg (.word k) => pure (.packed (.reg (.row k)))
    | _, .reg r => pure (.plain (.reg (.core r)))
    | _, .lit v => pure (.plain (.lit v))
    | _, .concat x y => do
      let rx ← visit x
      let ry ← visit y
      let ex ← force x rx
      let ey ← force y ry
      pure (.plain (.concat ex ey))
    | _, .inv x => do
      let r ← visit x
      pure (.plain (.inv (← force x r)))
    | _, .band x y => do
      let rx ← visit x
      let ry ← visit y
      let ex ← force x rx
      let ey ← force y ry
      pure (.plain (.band ex ey))
    | _, .sub x y => do
      let rx ← visit x
      let ry ← visit y
      let ex ← force x rx
      let ey ← force y ry
      pure (.plain (.sub ex ey))
    | _, .slice start len h x => do
      let r ← visit x
      pure (.plain (.slice start len h (← force x r)))
    | _, .equal x y => do
      let rx ← visit x
      let ry ← visit y
      let ex ← force x rx
      let ey ← force y ry
      pure (.plain (.equal ex ey))
    | _, .ult x y => do
      let rx ← visit x
      let ry ← visit y
      let ex ← force x rx
      let ey ← force y ry
      pure (.plain (.ult ex ey))
    | _, .zero x => do
      let r ← visit x
      pure (.plain (.zero (← force x r)))
    | _, .mux c t f => do
      let rc ← visit c
      let ec ← force c rc
      let rt ← visit t
      let rf ← visit f
      merged ec t f rt rf)
  modify fun s => {s with entries := s.entries.insert key ⟨w, ⟨value, none⟩⟩}
  return value

unsafe def adaptMemo (e : Reactive.E w) : E w :=
  let build : M (E w) := do
    let r ← visit e
    force e r
  build.run' {}

end MemoAdapt

@[implemented_by MemoAdapt.adaptMemo]
def adapt (e : Reactive.E w) : E w := (rewrite e).expression
def writing : E 1 := adapt Reactive.writing
def rowWriting : E 1 := both writing (cmd 1)
def tableWriting : E 1 := both writing (cmd 6)
def committing : E 1 := adapt Reactive.committing
def firstWriting : E 1 := both writing (.inv (.reg (.core .pending)))

def rowWrittenNext : E 64 := .mux resetting (.lit 0)
  (.mux writing (pack fun k => .mux
    (both rowWriting (.equal (.input .address) (.lit (BitVec.ofNat 6 k.val)))) (.lit 1)
    (.mux firstWriting (.lit 0) (.slice k.val 1 (by omega) (.reg (.core .written)))))
    (.reg (.core .written)))

def branchWrittenNext : E 16 := .mux resetting (.lit 0)
  (.mux writing (pack fun k => .mux
    (both tableWriting
      (.equal (.slice 0 4 (by decide) (.input .address)) (.lit (BitVec.ofNat 4 k.val)))) (.lit 1)
    (.mux firstWriting (.lit 0) (.slice k.val 1 (by omega) (.reg .branchWritten))))
    (.reg .branchWritten))

@[simp] def next_pending : E 1 := adapt (Reactive.next .pending)
@[simp] def next_valid : E 1 := adapt (Reactive.next .valid)
@[simp] def next_count : E 7 := adapt (Reactive.next .count)
@[simp] def next_idleLevels : E 3 := adapt (Reactive.next .idleLevels)
@[simp] def next_idleEnabled : E 3 := adapt (Reactive.next .idleEnabled)
@[simp] def next_generation : E 16 := adapt (Reactive.next .generation)
@[simp] def next_transfer : E 16 := adapt (Reactive.next .transfer)
@[simp] def next_phase : E 3 := adapt (Reactive.next .phase)
@[simp] def next_retained : E 1 := adapt (Reactive.next .retained)
@[simp] def next_pc : E 7 := adapt (Reactive.next .pc)
@[simp] def next_virtualPC : E 10 := adapt (Reactive.next .virtualPC)
@[simp] def next_virtualSpan : E 11 := adapt (Reactive.next .virtualSpan)
@[simp] def next_currentControl : E 22 := adapt (Reactive.next .currentControl)
@[simp] def next_outer : E 3 := adapt (Reactive.next .outer)
@[simp] def next_inner : E 3 := adapt (Reactive.next .inner)
@[simp] def next_remaining : E 8 := adapt (Reactive.next .remaining)
@[simp] def next_levels : E 3 := adapt (Reactive.next .levels)
@[simp] def next_enabled : E 3 := adapt (Reactive.next .enabled)
@[simp] def next_txData : E 32 := adapt (Reactive.next .txData)
@[simp] def next_txLength : E 6 := adapt (Reactive.next .txLength)
@[simp] def next_txConsumed : E 6 := adapt (Reactive.next .txConsumed)
@[simp] def next_rxData : E 32 := adapt (Reactive.next .rxData)
@[simp] def next_rxLength : E 6 := adapt (Reactive.next .rxLength)
@[simp] def next_rxCapacity : E 6 := adapt (Reactive.next .rxCapacity)
@[simp] def next_stage1 : E 2 := adapt (Reactive.next .stage1)
@[simp] def next_stage2 : E 2 := adapt (Reactive.next .stage2)
@[simp] def next_waitLeft : E 8 := adapt (Reactive.next .waitLeft)
@[simp] def next_scratch : E 16 := adapt (Reactive.next .scratch)
@[simp] def next_cachedDuration : E 8 := adapt (Reactive.next .cachedDuration)
@[simp] def next_cachedBudget : E 8 := adapt (Reactive.next .cachedBudget)
@[simp] def next_cachedCheck : E 4 := adapt (Reactive.next .cachedCheck)
@[simp] def next_cachedWait : E 2 := adapt (Reactive.next .cachedWait)
@[simp] def next_cachedTerminal : E 6 := adapt (Reactive.next .cachedTerminal)
@[simp] def next_cachedBranch : E 54 := adapt (Reactive.next .cachedBranch)

def coreNext : {w : Nat} → Base w → E w
  | _, .word k => adapt (Reactive.next (.word k))
  | _, .written => rowWrittenNext
  | _, .pending => next_pending
  | _, .valid => next_valid
  | _, .count => next_count
  | _, .idleLevels => next_idleLevels
  | _, .idleEnabled => next_idleEnabled
  | _, .generation => next_generation
  | _, .transfer => next_transfer
  | _, .phase => next_phase
  | _, .retained => next_retained
  | _, .pc => next_pc
  | _, .virtualPC => next_virtualPC
  | _, .virtualSpan => next_virtualSpan
  | _, .currentControl => next_currentControl
  | _, .outer => next_outer
  | _, .inner => next_inner
  | _, .remaining => next_remaining
  | _, .levels => next_levels
  | _, .enabled => next_enabled
  | _, .txData => next_txData
  | _, .txLength => next_txLength
  | _, .txConsumed => next_txConsumed
  | _, .rxData => next_rxData
  | _, .rxLength => next_rxLength
  | _, .rxCapacity => next_rxCapacity
  | _, .stage1 => next_stage1
  | _, .stage2 => next_stage2
  | _, .waitLeft => next_waitLeft
  | _, .scratch => next_scratch
  | _, .cachedDuration => next_cachedDuration
  | _, .cachedBudget => next_cachedBudget
  | _, .cachedCheck => next_cachedCheck
  | _, .cachedWait => next_cachedWait
  | _, .cachedTerminal => next_cachedTerminal
  | _, .cachedBranch => next_cachedBranch

def next : {w : Nat} → Register w → E w
  | _, .row k => .mux (both committing
      (.inv (.ult (.lit (BitVec.ofNat 7 k.toNat)) (.input .count)))) (.lit 0)
    (.mux (both rowWriting (.equal (.input .address) (.lit k)))
      (Expr.concat (a := 4) (b := 88) (.slice 0 4 (by decide) (.input .branch))
        (Expr.concat (a := 24) (b := 64) (.input .control) (.input .word))) (.reg (.row k)))
  | _, .branch k => .mux (both tableWriting
      (.equal (.slice 0 4 (by decide) (.input .address)) (.lit k)))
    (.input .branch) (.reg (.branch k))
  | _, .branchWritten => branchWrittenNext
  | _, .core r => coreNext r

@[simp] def out_valid : E 1 := adapt (Reactive.circuit.output .valid)
@[simp] def out_busy : E 1 := adapt (Reactive.circuit.output .busy)
@[simp] def out_retained : E 1 := adapt (Reactive.circuit.output .retained)
@[simp] def out_pending : E 1 := adapt (Reactive.circuit.output .pending)
@[simp] def out_rejected : E 1 := adapt (Reactive.circuit.output .rejected)
@[simp] def out_mode : E 2 := adapt (Reactive.circuit.output .mode)
@[simp] def out_pc : E 8 := adapt (Reactive.circuit.output .pc)
@[simp] def out_remaining : E 8 := adapt (Reactive.circuit.output .remaining)
@[simp] def out_levels : E 3 := adapt (Reactive.circuit.output .levels)
@[simp] def out_enabled : E 3 := adapt (Reactive.circuit.output .enabled)
@[simp] def out_txConsumed : E 6 := adapt (Reactive.circuit.output .txConsumed)
@[simp] def out_rxLength : E 6 := adapt (Reactive.circuit.output .rxLength)
@[simp] def out_rxData : E 32 := adapt (Reactive.circuit.output .rxData)
@[simp] def out_readValid : E 1 := adapt (Reactive.circuit.output .readValid)
@[simp] def out_readBit : E 1 := adapt (Reactive.circuit.output .readBit)
@[simp] def out_generation : E 16 := adapt (Reactive.circuit.output .generation)
@[simp] def out_transfer : E 16 := adapt (Reactive.circuit.output .transfer)
@[simp] def out_exhausted : E 1 := adapt (Reactive.circuit.output .exhausted)
@[simp] def out_stage1 : E 2 := adapt (Reactive.circuit.output .stage1)
@[simp] def out_stage2 : E 2 := adapt (Reactive.circuit.output .stage2)
@[simp] def out_virtualPC : E 10 := adapt (Reactive.circuit.output .virtualPC)
@[simp] def out_env0 : E 3 := adapt (Reactive.circuit.output .env0)
@[simp] def out_env1 : E 3 := adapt (Reactive.circuit.output .env1)
@[simp] def out_phase : E 3 := adapt (Reactive.circuit.output .phase)
@[simp] def out_waitLeft : E 8 := adapt (Reactive.circuit.output .waitLeft)
@[simp] def out_scratch : E 16 := adapt (Reactive.circuit.output .scratch)

def output : {w : Nat} → Output w → E w
  | _, .valid => out_valid
  | _, .busy => out_busy
  | _, .retained => out_retained
  | _, .pending => out_pending
  | _, .rejected => out_rejected
  | _, .mode => out_mode
  | _, .pc => out_pc
  | _, .remaining => out_remaining
  | _, .levels => out_levels
  | _, .enabled => out_enabled
  | _, .txConsumed => out_txConsumed
  | _, .rxLength => out_rxLength
  | _, .rxData => out_rxData
  | _, .readValid => out_readValid
  | _, .readBit => out_readBit
  | _, .generation => out_generation
  | _, .transfer => out_transfer
  | _, .exhausted => out_exhausted
  | _, .stage1 => out_stage1
  | _, .stage2 => out_stage2
  | _, .virtualPC => out_virtualPC
  | _, .env0 => out_env0
  | _, .env1 => out_env1
  | _, .phase => out_phase
  | _, .waitLeft => out_waitLeft
  | _, .scratch => out_scratch

def circuit : Circuit Input Register Output where
  next := next
  output := output

def inputs := Reactive.inputs
def outputs := Reactive.outputs
def inputLabel : {w : Nat} → Input w → String := Reactive.inputLabel
def outputLabel : {w : Nat} → Output w → String := Reactive.outputLabel
def registerLabel : {w : Nat} → Register w → String
  | _, .row k => s!"row{k.toNat}"
  | _, .branch k => s!"branch{k.toNat}"
  | _, .branchWritten => "branch_written"
  | _, .core r => Reactive.registerLabel r
def registers : Array (Sigma Register) :=
  Array.ofFn (fun k : Fin 64 => ⟨92,.row (BitVec.ofFin k)⟩) ++
  Array.ofFn (fun k : Fin 16 => ⟨56,.branch (BitVec.ofFin k)⟩) ++
  #[⟨16,.branchWritten⟩] ++ Reactive.registers.filterMap (fun ⟨w,r⟩ => match r with
    | .word _ => none
    | r => some ⟨w,.core r⟩)
def registerIndex : {w : Nat} → Register w → Nat
  | _, .row k => k.toNat
  | _, .branch k => 64 + k.toNat
  | _, .branchWritten => 80
  | _, .core r => 17 + Reactive.registerIndex r
def moduleText : Except String String := MemoEmit.moduleText "pinwheel_buffered_shared_branches"
  circuit inputs registers outputs inputLabel registerLabel outputLabel

end Pinwheel.Hardware.Buffered.SharedBranches
