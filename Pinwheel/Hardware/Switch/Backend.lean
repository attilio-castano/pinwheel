import Pinwheel.Hardware.Switch.Certified
import Pinwheel.Hardware.Stream.Backend

namespace Pinwheel.Hardware.Switch.WithFifo

open Physical Stream.BackendAPI
set_option backward.isDefEq.respectTransparency false

abbrev Control (n m w : Nat) :=
  Stream.Joint (Bank (m+1) (Stream.CellReg w 1)) (Bank (m+1) (Lane 1 (n+1)))
abbrev Register (n m w : Nat) (R : Nat → Type) :=
  Stream.Joint (Bank (n+1) R) (Control n m w)

def registers (f : Fifo width depth) (n m w : Nat) : Interface (Register n m w f.Register) :=
  indexedInterface (Stream.Joint.interface (Bank.interface (n+1) f.registers)
    (Stream.Joint.interface (Bank.interface (m+1) (Stream.CellReg.interface w 1))
      (Bank.interface (m+1) (lanePorts 1 (n+1)).interface))) "reg_"

variable (e : DestinationEncoding (m+1)) (f : Fifo (e.width+w) depth)
abbrev Wire (n m dw w : Nat) (R : Nat → Type) := Expr (In n m dw w) (Register n m w R)

def localReg (k : Fin (n+1)) (r : R b) : Wire n m dw w R b := .reg (.left (.at k r))

/-- The router asks for the queued offer with reset deasserted. Tying the
other probe pins low makes this path acyclic even for an opaque FIFO. The
actual FIFO step and admission path use the live ready/valid wires below. -/
def headPort (k : Fin (n+1)) (p : Stream.Out (e.width+w) b) : Wire n m e.width w f.Register b :=
  (f.circuit.output p).bind (fun _ => .lit 0) (localReg k)

/-- The existing router expressions use one valid bit and one word per head.
Substitution expands these leaves into public FIFO output expressions. -/
def source : {b : Nat} → Structural.Register n m e.width w 1 b → Wire n m e.width w f.Register b
  | _, .left (.at k (.valid _)) => headPort e f k Stream.outValid
  | _, .left (.at k (.data _)) => headPort e f k Stream.outData
  | _, .right r => .reg (.right r)

def route (x : Structural.Wire n m e.width w 1 b) : Wire n m e.width w f.Register b :=
  x.bind (fun p => .input p) (source e f)

def fifoInput (k : Fin (n+1)) (p : Stream.In (e.width+w) b) : Wire n m e.width w f.Register b :=
  route e f (Structural.fifoInput e w 1 k p)

def circuit (n : Nat) : Circuit (In n m e.width w) (Register n m w f.Register) (Out n m w) where
  next := fun {b} r => match b, r with
    | _, .left (.at k r) => (f.circuit.next r).bind (fifoInput e f k) (localReg k)
    | _, .right r => route e f ((Structural.circuit e n w 1).next (.right r))
  output := fun {b} p => match b, p with
    | _, .left (.at k) => .band (route e f (Structural.admissible e w 1 k))
        ((f.circuit.output Stream.inReady).bind (fifoInput e f k) (localReg k))
    | _, .right p => route e f ((Structural.circuit e n w 1).output (.right p))

def localState (r : Values (Register n m w R)) (k : Fin (n+1)) : Values R :=
  fun p => r (.left (.at k p))

private def heads (s : State n m α) : State n m α :=
  { s with queues := fun k => (s.queues k).head?.toList }

private theorem valid_heads (s : State n m α) (h : Valid depth s) : Valid 1 (heads s) :=
  ⟨fun k => by cases he : (s.queues k).head? <;> simp [heads, he], h.2⟩

private theorem grant_heads (i : Input n m α) (s : State n m α) (o : Fin m) :
    grant i (heads s) o = grant i s o := by
  have req : request (heads s) o = request s o := by
    funext k
    simp [request, heads]
  simp only [grant, req]
  rfl

private theorem queueInput_heads (i : Input n m α) (s : State n m α) (k : Fin (n+1)) :
    queueInput i (heads s) k = queueInput i s k := by simp [queueInput, pulled, grant_heads]

private theorem control_step (s : State n (m+1) (BitVec w)) (i : Input n (m+1) (BitVec w))
    (p : Control n m w b) :
    Structural.encode (depth := 1) e (step 1 i (heads s)) (.right p) =
    Structural.encode (depth := 1) e (step depth i s) (.right p) := by
  have hs (o : Fin (m+1)) : slotInput i (heads s) o = slotInput i s o := by
    simp only [slotInput, selectedDelivery, grant_heads]
    simp [heads]
  cases p with
  | left p => cases p with
    | «at» o p => simp only [Structural.encode, Structural.slotValue, step, hs] <;> rfl
  | right p => cases p with
    | «at» o p => cases p; simp only [Structural.encode, step, grant_heads] <;> rfl

structure Rel (r : Values (Register n m w f.Register)) (s : State n (m+1) (BitVec w)) : Prop where
  valid : Valid depth s
  queues : ∀ k, f.proof.Rel (localState r k) ((s.queues k).map (PacketEncoding.pack e))
  control : ∀ {b} (p : Control n m w b), r (.right p) = Structural.encode (depth := 1) e s (.right p)

private theorem source_eval (i : Values (In n m e.width w)) (h : Rel e f r s) :
    (fun {b} (p : Structural.Register n m e.width w 1 b) => (source e f p).eval i r) =
      @Structural.encode _ _ _ 1 e (heads s) := by
  funext b p
  cases p with
  | right p =>
    apply (h.control p).trans
    cases p with
    | left q => cases q; rfl
    | right q => cases q with
      | «at» o q => cases q; rfl
  | left p => cases p with
    | «at» k p =>
      have obs := f.proof.observe (fun _ => 0) _ _ (h.queues k)
      cases p with
      | valid j =>
        have hj : j = 0 := Fin.ext (by omega)
        subst j
        simp only [source, headPort, Expr.eval_bind, Expr.eval, localReg]
        exact (congrFun (congrFun obs _) Stream.outValid).trans (by
          cases he : s.queues k <;> simp [pins, Stream.Machine.component, Stream.queue,
            Stream.outputValues, Stream.decodeInput, Stream.outValid, Structural.encode, heads,
            PacketEncoding.cells, Stream.cells, he])
      | data j =>
        have hj : j = 0 := Fin.ext (by omega)
        subst j
        simp only [source, headPort, Expr.eval_bind, Expr.eval, localReg]
        exact (congrFun (congrFun obs _) Stream.outData).trans (by
          cases he : s.queues k <;> simp [pins, Stream.Machine.component, Stream.queue,
            Stream.outputValues, Stream.decodeInput, Stream.outData, Structural.encode, heads,
            PacketEncoding.cells, Stream.cells, he])

private theorem route_eval (i : Values (In n m e.width w)) (h : Rel e f r s)
    (x : Structural.Wire n m e.width w 1 b) :
    (route e f x).eval i r = x.eval i (Structural.encode e (heads s)) := by
  simp only [route, Expr.eval_bind, Expr.eval, source_eval e f i h]

private theorem input_eval (i : Values (In n m e.width w)) (h : Rel e f r s) (k : Fin (n+1)) :
    (fun {b} (p : Stream.In (e.width+w) b) => (fifoInput e f k p).eval i r) =
      @Stream.inputValues _ (Stream.mapInput (PacketEncoding.pack e) (queueInput (decode (readPins i)) s k)) := by
  simp only [fifoInput, route_eval e f i h, Structural.fifoInput_eval e _ (valid_heads _ h.valid),
    queueInput_heads]

private theorem queue_step (i : Values (In n m e.width w)) (r : Values (Register n m w f.Register))
    (k : Fin (n+1)) :
    @localState _ _ _ _ ((circuit e f n).step i r) k =
      @Circuit.step _ _ _ f.circuit (fun p => (fifoInput e f k p).eval i r) (localState r k) := by
  funext b p
  simp only [localState, Circuit.step, circuit, Expr.eval_bind, localReg, Expr.eval]
  rfl

def refinement (n : Nat) : Timed.Refinement (circuit e f n).component (Physical.component e depth) where
  Rel := Rel e f
  step := by
    intro i r s h
    refine ⟨valid_preserved depth _ s h.valid, ?_, ?_⟩
    · intro k
      change f.proof.Rel (localState ((circuit e f n).step i r) k) _
      rw [queue_step, input_eval e f i h]
      have hs := f.proof.step (Stream.inputValues (Stream.mapInput (PacketEncoding.pack e)
        (queueInput (decode (readPins i)) s k))) _ _ (h.queues k)
      simpa only [pins, Stream.decode_encode, Stream.queue_map_step, Physical.component, step, Circuit.component] using hs
    · intro b p
      exact (route_eval e f i h _).trans
        ((Structural.step_eq e _ (valid_heads s h.valid) i (.right p)).trans (control_step e _ _ p))
  observe := by
    intro i r s h
    funext b p
    cases p with
    | left p => cases p with
      | «at» k =>
        simp only [Circuit.component, Circuit.observe, circuit, Expr.eval, route_eval e f i h,
          Structural.admissible_eval, Expr.eval_bind, input_eval e f i h, localReg]
        have obs := f.proof.observe (Stream.inputValues (Stream.mapInput (PacketEncoding.pack e)
          (queueInput (decode (readPins i)) s k))) _ _ (h.queues k)
        apply (congrArg (fun x => BitVec.ofBool (Physical.admissible (readPins i) k) &&& x)
          (congrFun (congrFun obs _) Stream.inReady)).trans
        simp only [pins, Stream.decode_encode, Stream.queue_map_observe, Stream.outputValues,
          Stream.inReady, Stream.outputPorts, lanePorts, BitVec.ofBool_and_ofBool]
        cases hr : (decode (readPins i)).reset <;>
          simp [Physical.component, Physical.observe, Switch.observe, Stream.Machine.component,
            Switch.queueInput, hr, Bool.and_comm]
    | right p =>
      apply (route_eval e f i h _).trans
      apply (Structural.output_eq e _ (valid_heads s h.valid) (by decide) i (.right p)).trans
      cases p with
      | left q => cases q; rfl
      | right q => cases q; rfl

theorem recover (i : Values (In n m e.width w)) (r : Values (Register n m w f.Register))
    (hr : i Physical.reset = 1) : Rel e f ((circuit e f n).step i r) Switch.initial := by
  refine ⟨initial_valid depth, ?_, ?_⟩
  · intro k
    rw [queue_step]
    apply f.recover
    exact hr
  · intro b p
    simp only [Circuit.step, circuit, route, Expr.eval_bind, Expr.eval]
    apply Structural.reset_eq e i _ hr (.right p)

theorem initialized_trace (i : Values (In n m e.width w)) (r : Values (Register n m w f.Register))
    (hr : i Physical.reset = 1) (traffic : List (Values (In n m e.width w))) :
    (circuit e f n).component.trace ((circuit e f n).step i r) traffic =
      (Physical.component e depth).trace Switch.initial traffic :=
  (refinement e f n).trace_eq _ _ (recover e f i r hr) traffic

theorem artifact_initialized_trace
    (rtl : Timed.Component (Values (In n m e.width w)) (Values (Register n m w f.Register))
      (Values (Out n m w))) (a : Artifact.Correspondence (circuit e f n) rtl)
    (i : Values (In n m e.width w)) (r : Values (Register n m w f.Register))
    (hr : i Physical.reset = 1) (traffic : List (Values (In n m e.width w))) :
    rtl.trace (rtl.step i r) traffic = (Physical.component e depth).trace Switch.initial traffic := by
  rw [a.refinement.trace_eq _ _ rfl, a.step_eq]
  exact initialized_trace e f i r hr traffic

theorem interchangeable (g : Fifo (e.width+w) depth) (i : Values (In n m e.width w))
    (a : Values (Register n m w f.Register)) (b : Values (Register n m w g.Register))
    (hr : i Physical.reset = 1) (traffic : List (Values (In n m e.width w))) :
    (circuit e f n).component.trace ((circuit e f n).step i a) traffic =
      (circuit e g n).component.trace ((circuit e g n).step i b) traffic :=
  (initialized_trace e f i a hr traffic).trans (initialized_trace e g i b hr traffic).symm

end Pinwheel.Hardware.Switch.WithFifo
