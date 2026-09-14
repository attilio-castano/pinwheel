import Pinwheel.Hardware.Reactive.Core

namespace Pinwheel.Hardware.Reactive.Core

theorem direct_represents (p : Program) : represents p (Execution.directValues (Execution.imageWords p)) direct := by
  intro i s address
  simp [direct, Execution.readTree_correct, Expr.eval, memoryReg, values, Execution.directValues,
    Execution.imageWords, Engine.Reactive.Program.fetch]
  done

theorem indexed_represents (p : Program) (image : Execution.Indexed)
    (h : image.expand = Execution.imageWords p) : represents p (Execution.indexedValues image) indexed := by
  intro i s address
  simp [indexed, Execution.readTree_correct, Expr.eval, memoryReg, values, Execution.indexedValues]
  simpa [Execution.Indexed.expand, Execution.imageWords, Engine.Reactive.Program.fetch] using
    congrArg (fun words => words[(address.eval i.values (values s (Execution.indexedValues image) p.idle (BitVec.ofFin p.last))).toNat]) h
  done

theorem base_correct (p : Program) (memory : Values M) (f : Frontend M) (h : represents p memory f)
    (i : Inputs) (s : Reactive.State) (port : Reactive.Input w) :
    (baseInputs f port).eval i.values (values s memory p.idle (BitVec.ofFin p.last)) =
      ({feed p s i.request.reset i.request.start i.request.incoming with successor := 4} : Reactive.Inputs).values port := by
  cases port <;> simp [baseInputs, coreReg, Expr.eval, values,
    Inputs.values, Reactive.Inputs.values, feed]
  exact h i s (coreReg .pc)
  done

theorem address_correct (p : Program) (memory : Values M) (f : Frontend M) (h : represents p memory f)
    (i : Inputs) (s : Reactive.State) :
    (addressB f).eval i.values (values s memory p.idle (BitVec.ofFin p.last)) =
      targetValue (feed p s i.request.reset i.request.start i.request.incoming) s := by
  simp only [addressB, Expr.eval_bind, base_correct p memory f h, coreReg, Expr.eval, values]
  exact Reactive.target_correct _ s
  done

theorem inputs_correct (p : Program) (memory : Values M) (f : Frontend M) (h : represents p memory f)
    (i : Inputs) (s : Reactive.State) (port : Reactive.Input w) :
    (schedulerInputs f port).eval i.values (values s memory p.idle (BitVec.ofFin p.last)) =
      (feed p s i.request.reset i.request.start i.request.incoming).values port := by
  cases port <;> simp only [schedulerInputs, base_correct p memory f h, Reactive.Inputs.values]
  rw [h i s (addressB f), address_correct p memory f h]
  rfl
  done

theorem core_next (p : Program) (memory : Values M) (f : Frontend M) (h : represents p memory f)
    (i : Inputs) (m : Model) (r : Reactive.Register w) :
    (circuit f).step i.values (values (embed m) memory p.idle (BitVec.ofFin p.last)) (.core r) =
      (embed (Engine.Reactive.step p m i.request.reset i.request.start i.request.incoming)).values r := by
  simp only [Circuit.step, circuit, Expr.eval_bind, inputs_correct p memory f h,
    coreReg, Expr.eval, values]
  rw [Reactive.next_correct, Reactive.step_refines]
  done

theorem busy_correct (i : Inputs) (s : Reactive.State) (memory : Values M)
    (idle : Engine.Reactive.Pins) (last : BitVec 8) :
    (busy (M := M)).eval i.values (values s memory idle last) = BitVec.ofBool (runningValue s) := by
  simp only [busy, Expr.eval_bind, coreReg, Expr.eval, values]
  exact Reactive.running_correct ⟨false, false, 0, {}, 0, 0, 0⟩ s
  done

theorem blocked_correct (i : Inputs) (s : Reactive.State) (memory : Values M)
    (idle : Engine.Reactive.Pins) (last : BitVec 8) :
    (blocked (M := M)).eval i.values (values s memory idle last) =
      BitVec.ofBool (runningValue s || i.request.reset || i.request.start) := by
  cases hb : runningValue s <;> cases hr : i.request.reset <;> cases hs : i.request.start <;>
    simp [blocked, Expr.eval, busy_correct, Inputs.values, hb, hr, hs]
  done

def Protected (i : Inputs) (s : Reactive.State) : Prop :=
  i.write = false ∨ runningValue s = true ∨ i.request.reset = true ∨ i.request.start = true

theorem memory_write_hold (i : Inputs) (s : Reactive.State) (memory : Values M)
    (idle : Engine.Reactive.Pins) (last : BitVec 8) (h : Protected i s)
    (old new : Expr Execution.Input M w) (bank : Bool) (address : BitVec 8) :
    ((Execution.writeWord old new bank address).bind memoryInputs memoryReg).eval
      i.values (values s memory idle last) =
    (old.bind memoryInputs memoryReg).eval i.values (values s memory idle last) := by
  simp only [Expr.eval_bind, Execution.writeWord, Expr.eval, Execution.accept, memoryInputs,
    blocked_correct, Inputs.values]
  rcases h with h | h | h | h <;> simp [h]
  done

theorem metadata_hold (i : Inputs) (s : Reactive.State) (memory : Values M)
    (idle : Engine.Reactive.Pins) (last : BitVec 8) (h : Protected i s) (address : BitVec 8) :
    (metadataWrite (M := M) address).eval i.values (values s memory idle last) = 0 := by
  rcases h with h | h | h | h <;>
    simp [metadataWrite, Expr.eval, blocked_correct, Inputs.values, h]
  done

def Stable (f : Frontend M) : Prop :=
  ∀ (i : Inputs) (s : Reactive.State) (memory : Values M) (idle : Engine.Reactive.Pins) (last : BitVec 8),
    Protected i s → ∀ {w : Nat} (r : M w),
    ((f.next r).bind memoryInputs memoryReg).eval i.values (values s memory idle last) = memory r

theorem direct_stable : Stable direct := by
  intro i s memory idle last h w r
  cases r
  exact memory_write_hold i s memory idle last h _ _ _ _
  done

theorem indexed_stable : Stable indexed := by
  intro i s memory idle last h w r
  cases r <;> exact memory_write_hold i s memory idle last h _ _ _ _
  done

theorem machine_next (p : Program) (memory : Values M) (f : Frontend M)
    (hr : represents p memory f) (hs : Stable f) (i : Inputs) (m : Model) (hp : Protected i (embed m)) :
    ((circuit f).step i.values (values (embed m) memory p.idle (BitVec.ofFin p.last)) : Values (Register M)) =
      (fun {_} r => values (embed (Engine.Reactive.step p m i.request.reset i.request.start i.request.incoming))
        memory p.idle (BitVec.ofFin p.last) r) := by
  funext w r
  cases r with
  | core r => exact core_next p memory f hr i m r
  | memory r => exact hs i (embed m) memory p.idle (BitVec.ofFin p.last) hp r
  | _ => simp [Circuit.step, circuit, Expr.eval, metadata_hold i (embed m) memory p.idle (BitVec.ofFin p.last) hp, values]
  done

def run (f : Frontend M) (v : Values (Register M)) : List Inputs → Values (Register M)
  | [] => v
  | i :: rest => run f ((circuit f).step i.values v) rest

/-- A fixed-program execution allows attempted writes whenever hardware blocks them. -/
def Admissible (p : Program) (m : Model) : List Inputs → Prop
  | [] => True
  | i :: rest => Protected i (embed m) ∧
      Admissible p (Engine.Reactive.step p m i.request.reset i.request.start i.request.incoming) rest

/-- Complete register-bank correspondence, including unchanged instruction stores and metadata. -/
theorem machine_run (p : Program) (memory : Values M) (f : Frontend M)
    (hr : represents p memory f) (hs : Stable f) (m : Model) (requests : List Inputs)
    (hp : Admissible p m requests) :
    (run f (values (embed m) memory p.idle (BitVec.ofFin p.last)) requests : Values (Register M)) =
      (fun {_} r => values (embed (modelRun p m (requests.map Inputs.request))) memory p.idle (BitVec.ofFin p.last) r) := by
  induction requests generalizing m with
  | nil => rfl
  | cons i rest ih =>
    simp only [run, machine_next p memory f hr hs i m hp.1, List.map_cons, modelRun]
    exact ih _ hp.2
  done

theorem direct_run (p : Program) (m : Model) (requests : List Inputs) (h : Admissible p m requests) :
    (run direct (values (embed m) (Execution.directValues (Execution.imageWords p)) p.idle (BitVec.ofFin p.last)) requests : Values (Register Execution.DirectReg)) =
      (fun {_} r => values (embed (modelRun p m (requests.map Inputs.request)))
        (Execution.directValues (Execution.imageWords p)) p.idle (BitVec.ofFin p.last) r) := by
  exact machine_run p _ direct (direct_represents p) direct_stable m requests h
  done

theorem indexed_run (p : Program) (image : Execution.Indexed) (hi : image.expand = Execution.imageWords p)
    (m : Model) (requests : List Inputs) (h : Admissible p m requests) :
    (run indexed (values (embed m) (Execution.indexedValues image) p.idle (BitVec.ofFin p.last)) requests : Values (Register Execution.IndexedReg)) =
      (fun {_} r => values (embed (modelRun p m (requests.map Inputs.request)))
        (Execution.indexedValues image) p.idle (BitVec.ofFin p.last) r) := by
  exact machine_run p _ indexed (indexed_represents p image hi) indexed_stable m requests h
  done

end Pinwheel.Hardware.Reactive.Core
