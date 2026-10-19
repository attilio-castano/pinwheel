import Pinwheel.Hardware.Streaming.SourceRefinement
import Pinwheel.Hardware.Streaming.HostCorrespondence

/-! Inactive loader payload fields do not affect runtime circuit steps or ports.
The input-dependency certificate is structural, with named expression cuts. -/
namespace Pinwheel.Hardware.Streaming.InputCorrespondence
open Pinwheel.Hardware Pinwheel.Program.Streaming

def runtimePort : Core.Input w → Bool
  | .address | .word | .count | .idleLevels | .idleEnabled => false
  | _ => true

def runtime : Expr Core.Input R w → Bool
  | .input port => runtimePort port
  | .reg _ | .lit _ => true
  | .concat x y | .band x y | .sub x y | .equal x y | .ult x y => runtime x && runtime y
  | .inv x | .slice _ _ _ x | .zero x => runtime x
  | .mux condition yes no => runtime condition && runtime yes && runtime no

theorem eval_eq (e : Expr Core.Input R w) (safe : runtime e = true)
    (i j : Values Core.Input) (r : Values R)
    (leaf : ∀ {w} (port : Core.Input w), runtimePort port = true → i port = j port) :
    e.eval i r = e.eval j r := by
  induction e <;> simp_all [runtime,Expr.eval]

theorem command_leaf (c : Host.Command) (port : Core.Input w) (safe : runtimePort port = true) :
    HostCorrespondence.commandValues c port = SourceRefinement.inputs c.runtime port := by
  cases port <;> simp_all [runtimePort,HostCorrespondence.commandValues,SourceRefinement.inputs]

theorem command_eval (e : Core.E a w) (safe : runtime e = true) (c : Host.Command)
    (r : Values (Core.Register a)) :
    e.eval (HostCorrespondence.commandValues c) r = e.eval (SourceRefinement.inputs c.runtime) r :=
  eval_eq e safe _ _ r (command_leaf c)

theorem readTree_runtime (bits : Nat) (words : BitVec bits → Expr Core.Input R w)
    (address : Expr Core.Input R bits) (wordSafe : ∀ k, runtime (words k) = true)
    (addressSafe : runtime address = true) : runtime (Execution.readTree bits words address) = true := by
  induction bits with
  | zero => exact wordSafe 0
  | succ n ih =>
    have high := ih (fun k => words (k ++ 1#1)) (.slice 1 n (by omega) address)
      (fun k => wordSafe (k ++ 1#1)) (by simpa only [runtime] using addressSafe)
    have low := ih (fun k => words (k ++ 0#1)) (.slice 1 n (by omega) address)
      (fun k => wordSafe (k ++ 0#1)) (by simpa only [runtime] using addressSafe)
    simp only [Execution.readTree,runtime,addressSafe,high,low,Bool.and_self]

theorem pack_runtime (n : Nat) (f : Fin n → Core.E a 1)
    (safe : ∀ k, runtime (f k) = true) : runtime (Core.pack f) = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => exact safe 0
      | succ n =>
        simp only [Core.pack,runtime,ih (n+1) (by omega) _ (fun k => safe k.succ),safe,Bool.and_self]

theorem cmd_runtime (n : BitVec 4) : runtime (Core.cmd (a := a) n) = true := rfl
theorem isPhase_runtime (n : BitVec 3) : runtime (Core.isPhase (a := a) n) = true := rfl
theorem inc_runtime (x : Core.E a w) (safe : runtime x = true) : runtime (Core.inc x) = true := by
  simp only [Core.inc,runtime,safe,Bool.and_self]
theorem add_runtime (x y : Core.E a w) (hx : runtime x = true) (hy : runtime y = true) :
    runtime (Core.add x y) = true := by simp only [Core.add,runtime,hx,hy,Bool.and_self]
theorem space_runtime (port : Core.Register a 16) : runtime (Core.space port) = true := rfl


theorem register_runtime (port : Core.Register a w) : runtime (Expr.reg port : Core.E a w) = true := rfl
theorem literal_runtime (value : BitVec w) : runtime (Expr.lit value : Core.E a w) = true := rfl
attribute [local simp] register_runtime literal_runtime
attribute [local simp] runtime runtimePort Core.both Core.either
attribute [local simp] cmd_runtime isPhase_runtime inc_runtime add_runtime space_runtime

theorem field_runtime (start len : Nat) (fits : start+len≤64) :
    runtime (Core.field (a := a) start len fits) = true := by simp [Core.field]
theorem entryField_runtime (start len : Nat) (fits : start+len≤64)
    (entry : runtime (Core.entryWord (a := a)) = true) :
    runtime (Core.entryField (a := a) start len fits) = true := by simp [Core.entryField,entry]
theorem depth_runtime : runtime (Core.depth a) = true := rfl
attribute [local simp] field_runtime depth_runtime

theorem cold_runtime : runtime (Core.cold (a := a)) = true := by
  unfold Core.cold
  simp
attribute [local simp] cold_runtime

theorem warm_runtime : runtime (Core.warm (a := a)) = true := by
  unfold Core.warm
  simp
attribute [local simp] warm_runtime

theorem resetting_runtime : runtime (Core.resetting (a := a)) = true := by
  unfold Core.resetting
  simp
attribute [local simp] resetting_runtime

theorem busy_runtime : runtime (Core.busy (a := a)) = true := by
  unfold Core.busy
  simp
attribute [local simp] busy_runtime

theorem retained_runtime : runtime (Core.retained (a := a)) = true := by
  unfold Core.retained
  simp
attribute [local simp] retained_runtime

theorem owned_runtime : runtime (Core.owned (a := a)) = true := by
  unfold Core.owned
  simp
attribute [local simp] owned_runtime

theorem free_runtime : runtime (Core.free (a := a)) = true := by
  unfold Core.free
  simp
attribute [local simp] free_runtime

theorem identity_runtime : runtime (Core.identity (a := a)) = true := by
  unfold Core.identity
  simp
attribute [local simp] identity_runtime

theorem hostOwner_runtime : runtime (Core.hostOwner (a := a)) = true := by
  unfold Core.hostOwner
  simp
attribute [local simp] hostOwner_runtime

theorem writing_runtime : runtime (Core.writing (a := a)) = true := by
  unfold Core.writing
  simp
attribute [local simp] writing_runtime

theorem starting_runtime : runtime (Core.starting (a := a)) = true := by
  unfold Core.starting
  simp
attribute [local simp] starting_runtime

theorem drained_runtime : runtime (Core.drained (a := a)) = true := by
  unfold Core.drained
  simp
attribute [local simp] drained_runtime

theorem releasing_runtime : runtime (Core.releasing (a := a)) = true := by
  unfold Core.releasing
  simp
attribute [local simp] releasing_runtime

theorem txRoom_runtime : runtime (Core.txRoom (a := a)) = true := by
  unfold Core.txRoom
  simp
attribute [local simp] txRoom_runtime

theorem rxRoom_runtime : runtime (Core.rxRoom (a := a)) = true := by
  unfold Core.rxRoom
  simp
attribute [local simp] rxRoom_runtime

theorem txAvailable_runtime : runtime (Core.txAvailable (a := a)) = true := by
  unfold Core.txAvailable
  simp
attribute [local simp] txAvailable_runtime

theorem txBits16_runtime : runtime (Core.txBits16 (a := a)) = true := by
  unfold Core.txBits16
  simp
attribute [local simp] txBits16_runtime

theorem pushing_runtime : runtime (Core.pushing (a := a)) = true := by
  unfold Core.pushing
  simp
attribute [local simp] pushing_runtime

theorem popping_runtime : runtime (Core.popping (a := a)) = true := by
  unfold Core.popping
  simp
attribute [local simp] popping_runtime

theorem stream_runtime : runtime (Core.stream (a := a)) = true := by
  unfold Core.stream
  simp
attribute [local simp] stream_runtime

theorem transmit_runtime : runtime (Core.transmit (a := a)) = true := by
  unfold Core.transmit
  simp
attribute [local simp] transmit_runtime

theorem receive_runtime : runtime (Core.receive (a := a)) = true := by
  unfold Core.receive
  simp
attribute [local simp] receive_runtime

theorem lastCell_runtime : runtime (Core.lastCell (a := a)) = true := by
  unfold Core.lastCell
  simp
attribute [local simp] lastCell_runtime

theorem credit_runtime : runtime (Core.credit (a := a)) = true := by
  unfold Core.credit
  simp
attribute [local simp] credit_runtime

theorem reserving_runtime : runtime (Core.reserving (a := a)) = true := by
  unfold Core.reserving
  simp
attribute [local simp] reserving_runtime

theorem takingTX_runtime : runtime (Core.takingTX (a := a)) = true := by
  unfold Core.takingTX
  simp
attribute [local simp] takingTX_runtime

theorem loadingTX_runtime : runtime (Core.loadingTX (a := a)) = true := by
  unfold Core.loadingTX
  simp
attribute [local simp] loadingTX_runtime

theorem txHeadWord_runtime : runtime (Core.txHeadWord (a := a)) = true := by
  unfold Core.txHeadWord
  apply readTree_runtime
  · intro k; rfl
  · simp
attribute [local simp] txHeadWord_runtime

theorem txHeadBits_runtime : runtime (Core.txHeadBits (a := a)) = true := by
  unfold Core.txHeadBits
  apply readTree_runtime
  · intro k; rfl
  · simp
attribute [local simp] txHeadBits_runtime

theorem txSource_runtime : runtime (Core.txSource (a := a)) = true := by
  unfold Core.txSource
  simp
attribute [local simp] txSource_runtime

theorem txSourceBits_runtime : runtime (Core.txSourceBits (a := a)) = true := by
  unfold Core.txSourceBits
  simp
attribute [local simp] txSourceBits_runtime

theorem nextBit_runtime : runtime (Core.nextBit (a := a)) = true := by
  unfold Core.nextBit
  simp
attribute [local simp] nextBit_runtime

theorem capture_runtime : runtime (Core.capture (a := a)) = true := by
  unfold Core.capture
  simp
attribute [local simp] capture_runtime

theorem capturingRX_runtime : runtime (Core.capturingRX (a := a)) = true := by
  unfold Core.capturingRX
  simp
attribute [local simp] capturingRX_runtime

theorem inputBit_runtime : runtime (Core.inputBit (a := a)) = true := by
  unfold Core.inputBit
  simp
attribute [local simp] inputBit_runtime

theorem assembled_runtime : runtime (Core.assembled (a := a)) = true := by
  unfold Core.assembled
  simp
attribute [local simp] assembled_runtime

theorem emittingRX_runtime : runtime (Core.emittingRX (a := a)) = true := by
  unfold Core.emittingRX
  simp
attribute [local simp] emittingRX_runtime

theorem rxHeadWord_runtime : runtime (Core.rxHeadWord (a := a)) = true := by
  unfold Core.rxHeadWord
  apply readTree_runtime
  · intro k; rfl
  · simp
attribute [local simp] rxHeadWord_runtime

theorem rxHeadBits_runtime : runtime (Core.rxHeadBits (a := a)) = true := by
  unfold Core.rxHeadBits
  apply readTree_runtime
  · intro k; rfl
  · simp
attribute [local simp] rxHeadBits_runtime

theorem highEnd_runtime : runtime (Core.highEnd (a := a)) = true := by
  unfold Core.highEnd
  simp
attribute [local simp] highEnd_runtime

theorem repeating_runtime : runtime (Core.repeating (a := a)) = true := by
  unfold Core.repeating
  simp
attribute [local simp] repeating_runtime

theorem advancing_runtime : runtime (Core.advancing (a := a)) = true := by
  unfold Core.advancing
  simp
attribute [local simp] advancing_runtime

theorem fetching_runtime : runtime (Core.fetching (a := a)) = true := by
  unfold Core.fetching
  simp
attribute [local simp] fetching_runtime

theorem entryWord_runtime : runtime (Core.entryWord (a := a)) = true := by
  unfold Core.entryWord
  apply readTree_runtime
  · intro k; rfl
  · simp
attribute [local simp] entryWord_runtime

attribute [local simp] entryField_runtime

theorem entryKind_runtime : runtime (Core.entryKind (a := a)) = true := by
  unfold Core.entryKind
  simp
attribute [local simp] entryKind_runtime

theorem entryPulse_runtime : runtime (Core.entryPulse (a := a)) = true := by
  unfold Core.entryPulse
  simp
attribute [local simp] entryPulse_runtime

theorem entryStream_runtime : runtime (Core.entryStream (a := a)) = true := by
  unfold Core.entryStream
  simp
attribute [local simp] entryStream_runtime

theorem entryHalt_runtime : runtime (Core.entryHalt (a := a)) = true := by
  unfold Core.entryHalt
  simp
attribute [local simp] entryHalt_runtime

theorem entryFault_runtime : runtime (Core.entryFault (a := a)) = true := by
  unfold Core.entryFault
  simp
attribute [local simp] entryFault_runtime

theorem entryCanonical_runtime : runtime (Core.entryCanonical (a := a)) = true := by
  unfold Core.entryCanonical
  simp
attribute [local simp] entryCanonical_runtime

theorem entryBounds_runtime : runtime (Core.entryBounds (a := a)) = true := by
  unfold Core.entryBounds
  simp
attribute [local simp] entryBounds_runtime

theorem entryBad_runtime : runtime (Core.entryBad (a := a)) = true := by
  unfold Core.entryBad
  simp
attribute [local simp] entryBad_runtime

theorem entryTerminal_runtime : runtime (Core.entryTerminal (a := a)) = true := by
  unfold Core.entryTerminal
  simp
attribute [local simp] entryTerminal_runtime

theorem entrySkip_runtime : runtime (Core.entrySkip (a := a)) = true := by
  unfold Core.entrySkip
  simp
attribute [local simp] entrySkip_runtime

theorem enteringCell_runtime : runtime (Core.enteringCell (a := a)) = true := by
  unfold Core.enteringCell
  simp
attribute [local simp] enteringCell_runtime

theorem entryLast_runtime : runtime (Core.entryLast (a := a)) = true := by
  unfold Core.entryLast
  simp
attribute [local simp] entryLast_runtime


theorem basePins_runtime (high enabled : Bool) : runtime (Core.basePins (a := a) high enabled) = true := by
  cases high <;> cases enabled <;> simp [Core.basePins]
attribute [local simp] basePins_runtime

theorem entryLow_runtime (enabled : Bool) : runtime (Core.entryLow (a := a) enabled) = true := by
  cases enabled <;> simp [Core.entryLow]
attribute [local simp] entryLow_runtime

theorem driven_runtime (high enabled : Bool) (bit : Core.E a 1) (safe : runtime bit = true) :
    runtime (Core.driven high enabled bit) = true := by
  unfold Core.driven
  apply pack_runtime
  intro k
  cases enabled <;> simp [safe]
attribute [local simp] driven_runtime

theorem nextPins_runtime (enabled : Bool) : runtime (Core.nextPins (a := a) enabled) = true := by
  cases enabled <;> simp [Core.nextPins]
  all_goals exact driven_runtime _ _ _ rfl
attribute [local simp] nextPins_runtime

theorem queueCount_runtime (old : Core.E a 4) (put take : Core.E a 1)
    (ho : runtime old = true) (hp : runtime put = true) (ht : runtime take = true) :
    runtime (Core.queueCount old put take) = true := by simp [Core.queueCount,ho,hp,ht]
attribute [local simp] queueCount_runtime

theorem clearedRuntime_runtime : runtime (Core.clearedRuntime (a := a)) = true := by
  simp [Core.clearedRuntime]
attribute [local simp] clearedRuntime_runtime

def runtimeRegister : Core.Register a w → Bool
  | .word _ | .written | .pending | .valid | .count | .idleLevels | .idleEnabled | .generation => false
  | _ => true

theorem next_runtime (port : Core.Register a w) (safe : runtimeRegister port = true) :
    runtime (Core.next port) = true := by
  cases port <;> simp only [runtimeRegister,Bool.false_eq_true] at safe
  all_goals simp [Core.next,Core.nextRaw]
  all_goals first
    | (apply inc_runtime; rfl)
    | (apply add_runtime <;> simp)
    | (apply queueCount_runtime <;> simp)

def runtimeOutput : Core.Output w → Bool
  | .rejected => false
  | _ => true

theorem output_runtime (port : Core.Output w) (safe : runtimeOutput port = true) :
    runtime (Core.output (a := a) port) = true := by
  cases port <;> simp only [runtimeOutput,Bool.false_eq_true] at safe
  all_goals simp [Core.output]

theorem writing_zero (i : Values Core.Input) (r : Values (Core.Register a))
    (command : i .command ≠ 1#4) : Core.writing.eval i r = 0 := by
  simp [Core.writing,Core.both,Core.cmd,Expr.eval,command]

theorem committing_zero (i : Values Core.Input) (r : Values (Core.Register a))
    (command : i .command ≠ 2#4) : Core.committing.eval i r = 0 := by
  simp [Core.committing,Core.both,Core.cmd,Expr.eval,command]

theorem step_equal (c : Host.Command) (r : Values (Core.Register a))
    (write : c.runtime.command ≠ 1#4) (commit : c.runtime.command ≠ 2#4) (port : Core.Register a w) :
    (Core.circuit a).step (HostCorrespondence.commandValues c) r port =
      (Core.circuit a).step (SourceRefinement.inputs c.runtime) r port := by
  cases safe : runtimeRegister port
  · have writeHost := writing_zero (HostCorrespondence.commandValues c) r write
    have writeSource := writing_zero (SourceRefinement.inputs c.runtime) r write
    have commitHost := committing_zero (HostCorrespondence.commandValues c) r commit
    have commitSource := committing_zero (SourceRefinement.inputs c.runtime) r commit
    have reset := command_eval _ resetting_runtime c r
    cases port <;> simp only [runtimeRegister,Bool.true_eq_false] at safe
    all_goals simp [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.cold,Core.both,Expr.eval,
      writeHost,writeSource,commitHost,commitSource,reset,
      HostCorrespondence.commandValues,SourceRefinement.inputs]
  · exact command_eval _ (next_runtime port safe) c r

theorem observe_equal (c : Host.Command) (r : Values (Core.Register a))
    (write : c.runtime.command ≠ 1#4) (commit : c.runtime.command ≠ 2#4) (port : Core.Output w) :
    (Core.circuit a).observe (HostCorrespondence.commandValues c) r port =
      (Core.circuit a).observe (SourceRefinement.inputs c.runtime) r port := by
  cases safe : runtimeOutput port
  · cases port <;> simp only [runtimeOutput,Bool.true_eq_false] at safe
    have writeHost := writing_zero (HostCorrespondence.commandValues c) r write
    have writeSource := writing_zero (SourceRefinement.inputs c.runtime) r write
    have commitHost := committing_zero (HostCorrespondence.commandValues c) r commit
    have commitSource := committing_zero (SourceRefinement.inputs c.runtime) r commit
    simp only [Core.circuit,Circuit.observe,Core.output,Core.rejected,Core.both,Core.either,Expr.eval,
      writeHost,writeSource,commitHost,commitSource,
      command_eval _ resetting_runtime c r,command_eval _ starting_runtime c r,
      command_eval _ releasing_runtime c r,command_eval _ pushing_runtime c r,
      command_eval _ popping_runtime c r]
    rfl
  · exact command_eval _ (output_runtime port safe) c r


theorem step_values (c : Host.Command) (r : Values (Core.Register a))
    (write : c.runtime.command ≠ 1#4) (commit : c.runtime.command ≠ 2#4) :
    @Circuit.step _ _ _ (Core.circuit a) (HostCorrespondence.commandValues c) r =
      @Circuit.step _ _ _ (Core.circuit a) (SourceRefinement.inputs c.runtime) r := by
  funext w port
  exact step_equal c r write commit port

theorem observe_values (c : Host.Command) (r : Values (Core.Register a))
    (write : c.runtime.command ≠ 1#4) (commit : c.runtime.command ≠ 2#4) :
    @Circuit.observe _ _ _ (Core.circuit a) (HostCorrespondence.commandValues c) r =
      @Circuit.observe _ _ _ (Core.circuit a) (SourceRefinement.inputs c.runtime) r := by
  funext w port
  exact observe_equal c r write commit port

theorem step_runtime (c : Host.Command) (r : Values (Core.Register a))
    (input : SourceRefinement.RuntimeInput c.runtime) :
    @Circuit.step _ _ _ (Core.circuit a) (HostCorrespondence.commandValues c) r =
      @Circuit.step _ _ _ (Core.circuit a) (SourceRefinement.inputs c.runtime) r :=
  step_values c r input.2.2.1 input.2.2.2

theorem observe_runtime (c : Host.Command) (r : Values (Core.Register a))
    (input : SourceRefinement.RuntimeInput c.runtime) :
    @Circuit.observe _ _ _ (Core.circuit a) (HostCorrespondence.commandValues c) r =
      @Circuit.observe _ _ _ (Core.circuit a) (SourceRefinement.inputs c.runtime) r :=
  observe_values c r input.2.2.1 input.2.2.2

theorem source_step (image : SourceRefinement.Image p) (s : State a) (c : Host.Command) (ha : a ≤ 3)
    (input : SourceRefinement.RuntimeInput c.runtime) (bounds : s.Structural) :
    @Circuit.step _ _ _ (Core.circuit a) (HostCorrespondence.commandValues c) (SourceRefinement.values image s) =
      @SourceRefinement.values p a image (step p c.runtime s) := by
  exact (step_runtime c (SourceRefinement.values image s) input).trans
    (SourceRefinement.step_values image s c.runtime ha input bounds)

end Pinwheel.Hardware.Streaming.InputCorrespondence
