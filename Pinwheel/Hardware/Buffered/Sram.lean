import Pinwheel.Hardware.Buffered.SharedBranches
import Pinwheel.Hardware.Buffered.SramCandidates
import Pinwheel.Hardware.Buffered.MemoBind
import Pinwheel.Hardware.Memory.Sram

/-! Hybrid instruction SRAM controller. Two registered responses serve the two
successors of the current counted state. Requests use the prospective post-edge
state, so one-cycle branches renew their candidates without a bubble. Metadata
and dictionary stay combinational. Row zero has an instruction mirror updated
on accepted upload writes; START does not depend on stale macro Q.
This is a digital controller, not macro or address-path timing qualification. -/
namespace Pinwheel.Hardware.Buffered.Sram
open Pinwheel.Hardware
abbrev Base := Reactive.Register

inductive Input : Nat → Type where
  | base : Reactive.Input w → Input w
  | q : Bool → Input 64

inductive Register : Nat → Type where
  | metadata : BitVec 6 → Register 28
  | branch : BitVec 4 → Register 56
  | branchWritten : Register 16
  | core : Base w → Register w
  | startWord : Register 64

inductive Port : Nat → Type where
  | address : Bool → Port 6
  | data : Port 64
  | write : Port 1
  | read : Port 1

inductive Output : Nat → Type where
  | base : Reactive.Output w → Output w
  | port : Port w → Output w

abbrev E := Expr Input Register

/-- For register-only control equations; row values are not inspected here. -/
def controlRegister : {w : Nat} → SharedBranches.Register w → E w
  | _, .row k => .concat (.reg (.metadata k)) (.lit (0 : BitVec 64))
  | _, .branch k => .reg (.branch k)
  | _, .branchWritten => .reg .branchWritten
  | _, .core r => .reg (.core r)

def control (e : SharedBranches.E w) : E w :=
  MemoBind.bind (fun p => .input (.base p)) controlRegister e

def starting : E 1 := control (SharedBranches.adapt Reactive.starting)
def entryPC : E 7 := control (SharedBranches.adapt Reactive.entryPC)
def branchDecision : E 1 := control (SharedBranches.adapt Reactive.branchBit)
def rowWriting : E 1 := control SharedBranches.rowWriting
def tableWriting : E 1 := control SharedBranches.tableWriting
def committing : E 1 := control SharedBranches.committing

def instruction : E 64 := .mux starting (.reg .startWord)
  (.mux branchDecision (.input (.q true)) (.input (.q false)))

/-- Project the entire compact tail before dictionary expansion. Physical SRAM
cells are not cleared by COMMIT. Upload-prefix bank equality is not claimed. -/
def rowExpr (k : BitVec 6) : E 92 :=
  .mux (.ult (.lit (BitVec.ofNat 7 k.toNat)) (.reg (.core .count)))
    (.concat (.reg (.metadata k)) instruction) (.lit 0)

def registerExpr : {w : Nat} → SharedBranches.Register w → E w
  | _, .row k => rowExpr k
  | _, .branch k => .reg (.branch k)
  | _, .branchWritten => .reg .branchWritten
  | _, .core r => .reg (.core r)

def adapt (e : SharedBranches.E w) : E w :=
  MemoBind.bind (fun p => .input (.base p)) registerExpr e

@[simp] def next_pending : E 1 := adapt SharedBranches.next_pending
@[simp] def next_valid : E 1 := adapt SharedBranches.next_valid
@[simp] def next_count : E 7 := adapt SharedBranches.next_count
@[simp] def next_idleLevels : E 3 := adapt SharedBranches.next_idleLevels
@[simp] def next_idleEnabled : E 3 := adapt SharedBranches.next_idleEnabled
@[simp] def next_generation : E 16 := adapt SharedBranches.next_generation
@[simp] def next_transfer : E 16 := adapt SharedBranches.next_transfer
@[simp] def next_phase : E 3 := adapt SharedBranches.next_phase
@[simp] def next_retained : E 1 := adapt SharedBranches.next_retained
@[simp] def next_pc : E 7 := adapt SharedBranches.next_pc
@[simp] def next_virtualPC : E 10 := adapt SharedBranches.next_virtualPC
@[simp] def next_virtualSpan : E 11 := adapt SharedBranches.next_virtualSpan
@[simp] def next_currentControl : E 22 := adapt SharedBranches.next_currentControl
@[simp] def next_outer : E 3 := adapt SharedBranches.next_outer
@[simp] def next_inner : E 3 := adapt SharedBranches.next_inner
@[simp] def next_remaining : E 8 := adapt SharedBranches.next_remaining
@[simp] def next_levels : E 3 := adapt SharedBranches.next_levels
@[simp] def next_enabled : E 3 := adapt SharedBranches.next_enabled
@[simp] def next_txData : E 32 := adapt SharedBranches.next_txData
@[simp] def next_txLength : E 6 := adapt SharedBranches.next_txLength
@[simp] def next_txConsumed : E 6 := adapt SharedBranches.next_txConsumed
@[simp] def next_rxData : E 32 := adapt SharedBranches.next_rxData
@[simp] def next_rxLength : E 6 := adapt SharedBranches.next_rxLength
@[simp] def next_rxCapacity : E 6 := adapt SharedBranches.next_rxCapacity
@[simp] def next_stage1 : E 2 := adapt SharedBranches.next_stage1
@[simp] def next_stage2 : E 2 := adapt SharedBranches.next_stage2
@[simp] def next_waitLeft : E 8 := adapt SharedBranches.next_waitLeft
@[simp] def next_scratch : E 16 := adapt SharedBranches.next_scratch
@[simp] def next_cachedDuration : E 8 := adapt SharedBranches.next_cachedDuration
@[simp] def next_cachedBudget : E 8 := adapt SharedBranches.next_cachedBudget
@[simp] def next_cachedCheck : E 4 := adapt SharedBranches.next_cachedCheck
@[simp] def next_cachedWait : E 2 := adapt SharedBranches.next_cachedWait
@[simp] def next_cachedTerminal : E 6 := adapt SharedBranches.next_cachedTerminal
@[simp] def next_cachedBranch : E 54 := adapt SharedBranches.next_cachedBranch
@[simp] def next_written : E 64 := control SharedBranches.rowWrittenNext
@[simp] def next_branchWritten : E 16 := control SharedBranches.branchWrittenNext

def coreNext : {w : Nat} → Base w → E w
  | _, .word _ => .lit 0
  | _, .written => next_written
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

/-- Both hypothetical branch arms of the actual prospective core transition.
No sampler prediction or response/address tag registers are introduced. -/
def readAddressFalse : E 6 :=
  .slice 0 6 (by decide)
    (MemoBind.bind (fun _ => .lit 0) coreNext (SramCandidates.candidate false))
def readAddressTrue : E 6 :=
  .slice 0 6 (by decide)
    (MemoBind.bind (fun _ => .lit 0) coreNext (SramCandidates.candidate true))
def readAddress (b : Bool) : E 6 := if b then readAddressTrue else readAddressFalse

def next : {w : Nat} → Register w → E w
  | _, .metadata k => .mux
      (.band committing (.inv (.ult (.lit (BitVec.ofNat 7 k.toNat)) (.input (.base .count)))))
      (.lit 0)
      (.mux (.band rowWriting (.equal (.input (.base .address)) (.lit k)))
        (Expr.concat (a := 4) (b := 24)
          (.slice 0 4 (by decide) (.input (.base .branch))) (.input (.base .control)))
        (.reg (.metadata k)))
  | _, .branch k => .mux
      (.band tableWriting (.equal (.slice 0 4 (by decide) (.input (.base .address))) (.lit k)))
      (.input (.base .branch)) (.reg (.branch k))
  | _, .branchWritten => next_branchWritten
  | _, .core r => coreNext r
  | _, .startWord => .mux
      (.band rowWriting (.zero (.input (.base .address)))) (.input (.base .word)) (.reg .startWord)

def request : {w : Nat} → Port w → E w
  | _, .address b => .mux rowWriting (.input (.base .address)) (readAddress b)
  | _, .data => .input (.base .word)
  | _, .write => rowWriting
  | _, .read => .inv rowWriting

def output : {w : Nat} → Output w → E w
  | _, .base o => adapt (SharedBranches.output o)
  | _, .port p => request p

def circuit : Circuit Input Register Output := ⟨next, output⟩

def inputs : Array (Sigma Input) :=
  SharedBranches.inputs.map (fun ⟨w,p⟩ => ⟨w,.base p⟩) ++ #[⟨64,.q false⟩,⟨64,.q true⟩]
def ports : Array (Sigma Port) :=
  #[⟨6,.address false⟩,⟨6,.address true⟩,⟨64,.data⟩,⟨1,.write⟩,⟨1,.read⟩]
def outputs : Array (Sigma Output) :=
  SharedBranches.outputs.map (fun ⟨w,o⟩ => ⟨w,.base o⟩) ++ ports.map (fun ⟨w,p⟩ => ⟨w,.port p⟩)
def registers : Array (Sigma Register) :=
  Array.ofFn (fun k : Fin 64 => ⟨28,.metadata (BitVec.ofFin k)⟩) ++
  Array.ofFn (fun k : Fin 16 => ⟨56,.branch (BitVec.ofFin k)⟩) ++
  #[⟨16,.branchWritten⟩] ++ Reactive.registers.filterMap (fun ⟨w,r⟩ => match r with
    | .word _ => none | r => some ⟨w,.core r⟩) ++ #[⟨64,.startWord⟩]
def registerIndex : {w : Nat} → Register w → Nat
  | _, .metadata k => k.toNat
  | _, .branch k => 64 + k.toNat
  | _, .branchWritten => 80
  | _, .core r => 17 + Reactive.registerIndex r
  | _, .startWord => 116

def inputLabel : {w : Nat} → Input w → String
  | _, .base p => SharedBranches.inputLabel p
  | _, .q b => if b then "mem_q1" else "mem_q0"
def registerLabel : {w : Nat} → Register w → String
  | _, .metadata k => s!"metadata{k.toNat}"
  | _, .branch k => s!"branch{k.toNat}"
  | _, .branchWritten => "branch_written"
  | _, .core r => Reactive.registerLabel r
  | _, .startWord => "start_word"
def portLabel : {w : Nat} → Port w → String
  | _, .address b => if b then "mem_addr1" else "mem_addr0"
  | _, .data => "mem_data" | _, .write => "mem_write" | _, .read => "mem_read"
def outputLabel : {w : Nat} → Output w → String
  | _, .base o => SharedBranches.outputLabel o
  | _, .port p => portLabel p

def moduleText : Except String String := MemoEmit.moduleText
  "pinwheel_buffered_shared_branches_sram_controller" circuit inputs registers outputs
  inputLabel registerLabel outputLabel

end Pinwheel.Hardware.Buffered.Sram
