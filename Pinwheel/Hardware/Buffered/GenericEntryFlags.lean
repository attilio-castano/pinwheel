import Pinwheel.Hardware.Buffered.GenericEffectFacts
import Pinwheel.Hardware.Buffered.GenericWord
import Pinwheel.Hardware.Buffered.GenericRelation
import Pinwheel.Hardware.Buffered.SpiEntryControls

/-! Actual entry flags agree with the source-only effect result for every
buffered instruction. Comparisons use the represented TX/RX lengths and prefix
counts, including the consumed-before-overflow case. -/
namespace Pinwheel.Hardware.Buffered.GenericEntryFlags
open Pinwheel.Hardware Pinwheel.Program
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

private def either (x y : BitVec 1) : BitVec 1 := ~~~(~~~x &&& ~~~y)
private def phase (p n : BitVec 3) : BitVec 1 := BitVec.ofBool (decide (p = n))

private theorem held_certificate : ∀ (p : BitVec 3) (checked ready remaining wait : BitVec 1),
    either (phase p 1 &&& remaining)
      (either (phase p 2 &&& ready)
        (either (phase p 3 &&& (checked &&& remaining))
          (phase p 4 &&& (checked &&& remaining)))) = 1 →
      phase p 3 &&& ~~~checked = 0 ∧
        either (phase p 2 &&& (~~~ready &&& remaining))
          (phase p 4 &&& (~~~checked &&& wait)) = 0 := by
  decide +kernel

private theorem dispatch_certificate : ∀ d : BitVec 1,
    ~~~(0 : BitVec 1) &&& either 0 d = 1 → d = 1 := by
  decide +kernel

theorem entering_dispatch (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (entering : Reactive.entering.eval i r = 1) :
    Reactive.dispatch.eval i r = 1 := by
  have controls := SpiCircuit.quiet_controls i r quiet
  apply dispatch_certificate
  simpa only [Reactive.entering, Reactive.both, Reactive.either, Expr.eval,
    controls.1, controls.2.2.1, either] using entering

theorem entering_held (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (entering : Reactive.entering.eval i r = 1) :
    Reactive.heldFault.eval i r = 0 ∧ Reactive.heldTimeout.eval i r = 0 := by
  have dispatch := entering_dispatch i r quiet entering
  have value :
      either (phase (r .phase) 1 &&& BitVec.ofBool (decide (r .remaining = 0)))
        (either (phase (r .phase) 2 &&& Reactive.waitReady.eval i r)
          (either (phase (r .phase) 3 &&&
            (Reactive.checkedReady.eval i r &&& BitVec.ofBool (decide (r .remaining = 0))))
            (phase (r .phase) 4 &&&
              (Reactive.checkedReady.eval i r &&& BitVec.ofBool (decide (r .remaining = 0)))))) = 1 := by
    exact dispatch
  exact held_certificate (r .phase) (Reactive.checkedReady.eval i r) (Reactive.waitReady.eval i r)
      (BitVec.ofBool (decide (r .remaining = 0))) (BitVec.ofBool (decide (r .waitLeft = 0)))
      value

theorem preEntry (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (entering : Reactive.entering.eval i r = 1)
    (legal : Reactive.legalEntry.eval i r = 1) : SpiEntryControls.PreEntry i r :=
  ⟨(SpiCircuit.quiet_controls i r quiet).1, entering, legal,
    (entering_held i r quiet entering).1, (entering_held i r quiet entering).2⟩

def runs (instruction : Program.Buffered.Instruction) : Bool :=
  match instruction.operation with | .halt | .fault _ => false | _ => true

def completes (instruction : Program.Buffered.Instruction) : Bool :=
  match instruction.operation with | .halt => true | _ => false

def timesOut (instruction : Program.Buffered.Instruction) : Bool :=
  match instruction.operation with | .fault reason => reason == .timeout | _ => false

def underflows (instruction : Program.Buffered.Instruction) (e : Transfer.Execution) : Bool :=
  GenericEffects.consumes instruction.operation && !decide (e.txConsumed < e.request.tx.length)

def overflows (instruction : Program.Buffered.Instruction) (e : Transfer.Execution) : Bool :=
  runs instruction && !underflows instruction e && instruction.append.isSome &&
    !decide (e.rx.length < e.request.rxLimit)

structure Flags (instruction : Program.Buffered.Instruction) (e : Transfer.Execution)
    (sampled : Engine.Reactive.Inputs) (i : Values Reactive.Input)
    (r : Values Reactive.Register) : Prop where
  running : Reactive.runEntry.eval i r = BitVec.ofBool (runs instruction)
  underflow : Reactive.underflow.eval i r = BitVec.ofBool (underflows instruction e)
  overflow : Reactive.overflow.eval i r = BitVec.ofBool (overflows instruction e)
  consuming : Reactive.consuming.eval i r =
    BitVec.ofBool (GenericEffects.result instruction e sampled).consume
  appending : Reactive.appending.eval i r =
    BitVec.ofBool (GenericEffects.result instruction e sampled).receive
  complete : Reactive.entryComplete.eval i r = BitVec.ofBool (completes instruction)
  failed : Reactive.entryFailed.eval i r =
    BitVec.ofBool (GenericEffects.result instruction e sampled).outcome.isSome
  timeout : Reactive.entryTimeout.eval i r = BitVec.ofBool (timesOut instruction)
  stopping : Reactive.stopping.eval i r =
    BitVec.ofBool (GenericEffects.finalOutcome instruction e sampled).isSome
  heldFault : Reactive.heldFault.eval i r = 0
  heldTimeout : Reactive.heldTimeout.eval i r = 0

private theorem append_some_nonzero : ∀ input : Fin 2,
    GenericEncoding.append (some input) ≠ 0#2 := by
  decide +kernel

private theorem one_and (x : BitVec 1) : 1#1 &&& x = x := BitVec.allOnes_and
private theorem append_none : GenericEncoding.append none = 0#2 := rfl

theorem flags (instruction : Program.Buffered.Instruction) (e : Transfer.Execution)
    (sampled : Engine.Reactive.Inputs) (payload : BitVec 32)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (quiet : SpiCircuit.Quiet i) (entering : Reactive.entering.eval i r = 1)
    (legal : Reactive.legalEntry.eval i r = 1)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction)
    (data : Refinement.Datapath payload r e) : Flags instruction e sampled i r := by
  have h := preEntry i r quiet entering legal
  have starting := (SpiCircuit.quiet_controls i r quiet).2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.heldFault, h.heldTimeout⟩
  all_goals rcases instruction with ⟨operation, append, preserveLevels, preserveEnabled⟩
  all_goals cases operation
  all_goals cases append
  all_goals by_cases available : e.txConsumed < e.request.tx.length
  all_goals by_cases room : e.rx.length < e.request.rxLimit
  all_goals simp [Reactive.runEntry, Reactive.entryTerminal, Reactive.isKind, Reactive.kind,
    Reactive.underflow, Reactive.overflow, Reactive.consuming, Reactive.appending,
    Reactive.entryComplete, Reactive.entryFailed, Reactive.stopping, Reactive.entryTimeout,
    Reactive.entryConsumed, Reactive.entryTxLength, Reactive.entryRxLength, Reactive.entryCapacity,
    Reactive.wantsRx, Reactive.both, Reactive.either, Expr.eval, h.resetting, h.entering,
    h.legal, h.heldFault, h.heldTimeout, starting, word, GenericWord.kind_field,
    GenericWord.append_field, GenericWord.timeout_field, GenericEncoding.instruction,
    GenericEncoding.action, GenericEncoding.empty, append_some_nonzero, append_none, one_and,
    data.consumed, data.txLength,
    data.rxLength, data.rxCapacity, available, room, runs, completes, timesOut,
    underflows, overflows, GenericEffects.result, GenericEffects.consumes,
    GenericEffects.finalOutcome, Program.Buffered.Failure.outcome]

end Pinwheel.Hardware.Buffered.GenericEntryFlags
