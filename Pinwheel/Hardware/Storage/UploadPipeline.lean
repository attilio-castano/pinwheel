import Pinwheel.Hardware.Storage.SramCoverage
import Pinwheel.Hardware.Storage.SramAssembly

/-! Experimental one-entry upload stage, tied to the existing loader requests.
The stage holds a write across running/start edges, where SRAM reads have priority.
This file checks the stage's schedule and memory view and emits an opt-in RTL
variant. The default assembly is unchanged. A composed execution refinement and
physical benefit remain separate obligations. -/
namespace Pinwheel.Hardware.Storage.UploadPipeline
open Pinwheel.Hardware Loader

abbrev Pending := Memory.Write 6 64

/-- Running, start and commit edges retain their read port. -/
def drain (i : Loader.Inputs) (c : Loader.State) : Bool :=
  !(i.busy || Loader.start i c || Loader.commit i c)

def incoming (i : Loader.Inputs) (c : Loader.State) : Pending :=
  (SramCoverage.request i c (fun _ => 0)).write

def next (i : Loader.Inputs) (c : Loader.State) (p : Pending) : Pending :=
  let n := if drain i c then incoming i c else p
  {n with enable := !i.init && n.enable}

def issued (i : Loader.Inputs) (c : Loader.State) (p : Pending) : Pending :=
  {p with enable := !i.init && p.enable && drain i c}

/-- A deferred dictionary write can only belong to the first 32 accepted pushes
or a reset/restarted cursor. This excludes an outstanding write at commit. -/
def Bounded (c : Loader.State) (p : Pending) : Prop :=
  p.enable = true → c.cursor.toNat ≤ 32

/-- Every enqueue also drains the old entry, so a full entry is never lost. -/
theorem enqueue_drains (i : Loader.Inputs) (c : Loader.State)
    (h : (incoming i c).enable = true) : drain i c = true := by
  simp_all [incoming, SramCoverage.request, Loader.push, Loader.enabled,
    drain, Loader.start, Loader.commit, Bool.and_assoc]
  done

/-- A queued write never steals a read from a running program or immediate start. -/
theorem reserved_read (i : Loader.Inputs) (c : Loader.State) (p : Pending)
    (h : i.busy = true ∨ Loader.start i c = true ∨ Loader.commit i c = true) :
    (issued i c p).enable = false := by
  rcases h with h | h | h <;> simp [issued, drain, h]
  done

/-- One-entry occupancy stays within the dictionary portion of the real loader. -/
theorem bounded_next (i : Loader.Inputs) (c : Loader.State) (p : Pending)
    (h : Bounded c p) : Bounded (Loader.next i c) (next i c p) := by
  by_cases hw : (incoming i c).enable = true
  all_goals simp_all [Bounded, next, incoming, SramCoverage.request, drain,
    Loader.next, Loader.push, Loader.start, Loader.commit, Loader.enabled, Bool.and_assoc]
  all_goals repeat' (first | omega | split <;> try simp_all)
  all_goals intro hp
  all_goals repeat' (first | omega | split <;> try simp_all)
  done

theorem commit_empty (i : Loader.Inputs) (c : Loader.State) (p : Pending)
    (h : Bounded c p) (hc : Loader.commit i c = true) : p.enable = false := by
  have cursor := (Loader.commit_requires_complete i c hc).2.2.2.2.2
  simpa [Bounded, cursor] using h
  done

/-- The logical contents include the accepted write still held in the stage. -/
def view (memory : Memory.Contents 6 64) (p : Pending) : Memory.Contents 6 64 :=
  memory.write p

/-- Draining and refilling preserves every accepted word, including writes to
the same address and arbitrarily long pauses. Read availability is separate. -/
theorem view_next (i : Loader.Inputs) (c : Loader.State) (p : Pending)
    (memory : Memory.Contents 6 64) (hi : i.init = false) :
    view (memory.write (issued i c p)) (next i c p) =
      (view memory p).write (incoming i c) := by
  by_cases hd : drain i c = true
  all_goals have h := enqueue_drains i c
  all_goals simp_all [view, issued, next]
  done

inductive Register : Nat → Type where
  | valid : Register 1
  | address : Register 6
  | data : Register 64

abbrev PortInput := Observed SramController.Input (SramController.Out Machine.Output)
abbrev E := Expr PortInput Register

def drainExpr : E 1 := .inv (Execution.bor
  (.input (.output (.base (.core .busy))))
  (Execution.bor (.input (.output (.base (.control .start))))
    (.input (.output (.base (.control .commit))))))

def issuedExpr : E 1 := .band (.inv (.input (.input (.base .init))))
  (.band (.reg .valid) drainExpr)

/-- Output-side staging reuses the existing typed controller/port assembly.
The original core transition is unchanged; its SRAM responses come from the
new request schedule and therefore still need a composed refinement. -/
def observer : Observer SramController.Input (SramController.Out Machine.Output)
    Register (SramController.Out Machine.Output) where
  next := fun r => match r with
    | .valid => .band (.inv (.input (.input (.base .init))))
        (.mux drainExpr (.input (.output (.port .write))) (.reg .valid))
    | .address => .mux drainExpr
        (.slice 0 6 (by decide) (.input (.output (.port (.address false))))) (.reg .address)
    | .data => .mux drainExpr (.input (.output (.port .data))) (.reg .data)
  output := fun p => match p with
    | .base o => .input (.output (.base o))
    | .port p => match p with
      | .write => issuedExpr
      | .read => .inv issuedExpr
      | .data => .reg .data
      | .address b => .mux issuedExpr (.concat (.lit (0#3)) (.reg Register.address : E 6))
          (.input (.output (.port (.address b))))

/-- The actual expression emitted at the write port preserves read priority. -/
theorem observer_read_priority (i : Values PortInput) (p : Values Register)
    (h : i (.output (.base (.core .busy))) = 1 ∨
      i (.output (.base (.control .start))) = 1 ∨
      i (.output (.base (.control .commit))) = 1) :
    (observer.output (.port .write)).eval i p = 0 := by
  rcases h with h | h | h <;> simp [observer, issuedExpr, drainExpr, Expr.eval, Execution.bor, h]
  done

def registers : Array (Sigma Register) := #[⟨1,.valid⟩, ⟨6,.address⟩, ⟨64,.data⟩]

def label : {w : Nat} → Register w → String
  | _, .valid => "upload_pending"
  | _, .address => "upload_address"
  | _, .data => "upload_data"

def core := observer.wrap (SramController.core false)

def coreRegisters : Array (Sigma (Extended SramController.Register Register)) := (SramAssembly.registers false).map
  (fun ⟨w,r⟩ => ⟨w, Extended.inner r⟩) ++ registers.map (fun ⟨w,r⟩ => ⟨w, Extended.extra r⟩)

def coreLabel : {w : Nat} → Extended SramController.Register Register w → String
  | _, .inner r => Backend.Policy.registerLabel SramAssembly.extraLabel r
  | _, .extra r => label r

def coreText : Except String String :=
  Netlist.moduleText "pinwheel_sram_core_controller" core
    (SramAssembly.inputs Machine.inputs) coreRegisters (SramAssembly.outputs Machine.outputs)
    (SramAssembly.inputLabel Machine.inputLabel) coreLabel (SramAssembly.outputLabel Machine.outputLabel)

def chip := SramAssembly.observer.wrap
  ((SramController.bypass Chip.pinMap).wrap ((SramController.bypass Feeder.sampler).wrap
    ((SramController.bypass Serial.receiver).wrap core)))

abbrev FullRegister := Extended (Chip.Register (Extended SramController.Register Register)) HostResult.Register

def chipRegisters : Array (Sigma FullRegister) :=
  (coreRegisters.map (fun ⟨w,r⟩ => ⟨w, Extended.inner (.inner (.inner (.inner r)))⟩)) ++
  Backend.Policy.serialRegisters.map (fun ⟨w,r⟩ => ⟨w, Extended.inner (.inner (.inner (.extra r)))⟩) ++
  Backend.Policy.sampledRegisterList.map (fun ⟨w,r⟩ => ⟨w, Extended.inner (.inner (.extra r))⟩) ++
  HostResult.registers.map (fun ⟨w,r⟩ => ⟨w, Extended.extra r⟩)

def chipLabel : {w : Nat} → FullRegister w → String
  | _, .inner (.inner (.inner (.inner r))) => coreLabel r
  | _, .inner (.inner (.inner (.extra r))) => Backend.Policy.serialLabel r
  | _, .inner (.inner (.extra r)) => Backend.Policy.sampledRegisterLabel r
  | _, .inner (.extra r) => nomatch r
  | _, .extra r => HostResult.label r

def chipText : Except String String :=
  Netlist.moduleText "pinwheel_sram_controller" chip
    (SramAssembly.inputs Backend.Policy.chipInputs) chipRegisters
    (SramAssembly.outputs Backend.Policy.chipOutputs)
    (SramAssembly.inputLabel Backend.Policy.chipInputLabel) chipLabel
    (SramAssembly.outputLabel Backend.Policy.chipOutputLabel)

end Pinwheel.Hardware.Storage.UploadPipeline
