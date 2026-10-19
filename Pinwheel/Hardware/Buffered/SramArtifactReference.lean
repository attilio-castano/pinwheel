import Pinwheel.Hardware.Buffered.SramExecution

/-! A factored proof reference for artifact interpretation. The existing
storage rewrite is bypassed using its checked semantic theorem. This adds no
controller behavior and makes no claim about the native emitter. -/
namespace Pinwheel.Hardware.Buffered.SramArtifactReference
open Pinwheel.Hardware

def input (p : Reactive.Input w) : Sram.E w :=
  MemoBind.bind (fun q => .input (.base q)) Sram.registerExpr
    (SharedBranches.inputExpr p)

def register (r : Reactive.Register w) : Sram.E w :=
  MemoBind.bind (fun q => .input (.base q)) Sram.registerExpr
    (SharedBranches.registerExpr r)

def adapt (e : Reactive.E w) : Sram.E w := MemoBind.bind input register e

theorem input_correct (p : Reactive.Input w) (i : Values Sram.Input)
    (s : Values Sram.Register) :
    (input p).eval i s =
      SharedBranches.mappedInput (fun q => i (.base q))
        (SramExecution.selectedShared i s) p := by
  simp only [input, MemoBind.eval_bind, Expr.eval, SharedBranches.mappedInput]
  rfl
  done

theorem register_correct (r : Reactive.Register w) (i : Values Sram.Input)
    (s : Values Sram.Register) :
    (register r).eval i s =
      SharedBranches.expandState (SramExecution.selectedShared i s) r := by
  simp only [register, MemoBind.eval_bind, Expr.eval, SharedBranches.registerExpr_correct]
  rfl
  done

theorem adapt_correct (e : Reactive.E w) (i : Values Sram.Input)
    (s : Values Sram.Register) :
    (adapt e).eval i s = (Sram.adapt (SharedBranches.adapt e)).eval i s := by
  simp only [adapt, MemoBind.eval_bind, input_correct, register_correct,
    SramExecution.adapt_correct, SharedBranches.adapt_correct]
  done

def coreNext : {w : Nat} → Reactive.Register w → Sram.E w
  | _, .word _ => .lit 0
  | _, .written => Sram.next_written
  | _, r => adapt (Reactive.next r)

theorem coreNext_correct (r : Reactive.Register w) (i : Values Sram.Input)
    (s : Values Sram.Register) :
    (coreNext r).eval i s = (Sram.coreNext r).eval i s := by
  cases r with
  | word _ => rfl
  | written => rfl
  | _ => exact adapt_correct _ i s
  done

def readAddress (b : Bool) : Sram.E 6 :=
  .slice 0 6 (by decide)
    (MemoBind.bind (fun _ => .lit 0) coreNext (SramCandidates.candidate b))

theorem readAddress_correct (b : Bool) (i : Values Sram.Input)
    (s : Values Sram.Register) :
    (readAddress b).eval i s = (Sram.readAddress b).eval i s := by
  cases b <;> simp only [readAddress, Sram.readAddress, Sram.readAddressFalse,
    Sram.readAddressTrue, Bool.false_eq_true, ↓reduceIte,
    MemoBind.eval_bind, Expr.eval, coreNext_correct]
  done

def next : {w : Nat} → Sram.Register w → Sram.E w
  | _, .core r => coreNext r
  | _, r => Sram.next r

theorem next_correct (r : Sram.Register w) (i : Values Sram.Input)
    (s : Values Sram.Register) :
    (next r).eval i s = Sram.circuit.step i s r := by
  cases r with
  | core r => exact coreNext_correct r i s
  | _ => rfl
  done

def request : {w : Nat} → Sram.Port w → Sram.E w
  | _, .address b => .mux Sram.rowWriting (.input (.base .address)) (readAddress b)
  | _, p => Sram.request p

theorem request_correct (p : Sram.Port w) (i : Values Sram.Input)
    (s : Values Sram.Register) :
    (request p).eval i s = (Sram.request p).eval i s := by
  cases p with
  | address b => simp only [request, Sram.request, Expr.eval, readAddress_correct]
  | _ => rfl
  done

def output : {w : Nat} → Sram.Output w → Sram.E w
  | _, .base o => adapt (Reactive.circuit.output o)
  | _, .port p => request p

theorem output_correct (o : Sram.Output w) (i : Values Sram.Input)
    (s : Values Sram.Register) :
    (output o).eval i s = Sram.circuit.observe i s o := by
  cases o with
  | base o => cases o <;> exact adapt_correct _ i s
  | port p => exact request_correct p i s
  done

def circuit : Circuit Sram.Input Sram.Register Sram.Output := ⟨next, output⟩

end Pinwheel.Hardware.Buffered.SramArtifactReference
