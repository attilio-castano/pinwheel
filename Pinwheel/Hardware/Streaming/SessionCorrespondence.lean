import Pinwheel.Hardware.Streaming.SourceRefinement
import Pinwheel.Hardware.Streaming.InputCorrespondence
import Pinwheel.Hardware.Streaming.HostCorrespondence
import Pinwheel.Hardware.Streaming.Package
import Pinwheel.Hardware.Streaming.TinyWiring
import Pinwheel.Program.StreamingSession

namespace Pinwheel.Hardware.Streaming.SessionCorrespondence
open Pinwheel.Hardware Pinwheel.Program.Streaming
open SourceRefinement
set_option linter.unusedSimpArgs false

private theorem and_bool (x y : Bool) :
    BitVec.ofBool x &&& BitVec.ofBool y = BitVec.ofBool (x && y) := by
  cases x <;> cases y <;> rfl
private theorem inv_bool (x : Bool) : ~~~BitVec.ofBool x = BitVec.ofBool (!x) := by
  cases x <;> rfl
private theorem or_bool (x y : Bool) :
    ~~~(~~~BitVec.ofBool x &&& ~~~BitVec.ofBool y) = BitVec.ofBool (x || y) := by
  cases x <;> cases y <;> rfl
private theorem bit_roundtrip : ∀ x : BitVec 1, BitVec.ofBool (x.getLsbD 0) = x := by
  decide +kernel
private theorem one_and : ∀ x : BitVec 1, 1#1 &&& x = x := by
  decide +kernel
private theorem boundary_eval (image : Image p) (s : State a) (i : Input) :
    (Core.isPhase 2).eval (inputs i) (values image s) = BitVec.ofBool (s.phase == .boundary) :=
  isPhase_eval image s i .boundary

theorem observe_correct (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (hs : s.Structural) (port : Core.Output w) :
    (Core.circuit a).observe (inputs i) (values image s) port =
      HostCorrespondence.statusValues (s.status (image.pending.getLsbD 0) i) port := by
  cases port <;> try rfl
  case pending => exact (bit_roundtrip _).symm
  case busy => exact busy_eval image s i
  case retained => exact retained_eval image s i
  case fault => exact isPhase_eval image s i .fault
  case stalled =>
    change (Core.both (Core.isPhase 2) (.inv Core.credit)).eval _ _ = _
    simp only [Core.both,Expr.eval,boundary_eval,
      credit_eval image s i ha,inv_bool,and_bool,HostCorrespondence.statusValues,State.status]
  case waitingTX =>
    change (Core.both (Core.isPhase 2) (Core.both Core.transmit (.inv Core.txAvailable))).eval _ _ = _
    simp only [Core.both,Expr.eval,boundary_eval,transmit_eval,
      txAvailable_eval image s i ha,inv_bool,and_bool,HostCorrespondence.statusValues,State.status,
      Bool.and_assoc]
  case waitingRX =>
    change (Core.both (Core.isPhase 2) (Core.both Core.receive (.inv Core.rxRoom))).eval _ _ = _
    simp only [Core.both,Expr.eval,boundary_eval,receive_eval,
      rxRoom_eval image s i ha,inv_bool,and_bool,HostCorrespondence.statusValues,State.status,
      Bool.and_assoc]
  case rxData =>
    change (Expr.mux (Expr.zero (Expr.reg Core.Register.rxCount)) (.lit 0) Core.rxHeadWord).eval _ _ = _
    simp only [Expr.eval,values,rxHeadWord_eval,HostCorrespondence.statusValues,State.status]
    have count := queue_count_toNat s.rx ha
    have zero : (BitVec.ofNat 4 s.rx.count.val = 0#4) ↔ s.rx.count.val = 0 := by
      constructor
      · intro h; have h' := congrArg BitVec.toNat h; change (BitVec.ofNat 4 s.rx.count.val).toNat = 0 at h'; rwa [count] at h'
      · intro h; rw [h]
    by_cases h : s.rx.count.val = 0 <;> simp [zero,h,Queue.readable]
  case rxBits =>
    change (Expr.mux (Expr.zero (Expr.reg Core.Register.rxCount)) (.lit 0) Core.rxHeadBits).eval _ _ = _
    simp only [Expr.eval,values,rxHeadBits_eval,HostCorrespondence.statusValues,State.status]
    have count := queue_count_toNat s.rx ha
    have zero : (BitVec.ofNat 4 s.rx.count.val = 0#4) ↔ s.rx.count.val = 0 := by
      constructor
      · intro h; have h' := congrArg BitVec.toNat h; change (BitVec.ofNat 4 s.rx.count.val).toNat = 0 at h'; rwa [count] at h'
      · intro h; rw [h]
    by_cases h : s.rx.count.val = 0 <;> simp [zero,h,Queue.readable]
  case rejected =>
    change Core.rejected.eval (inputs i) (values image s) = _
    simp only [Core.rejected,Core.both,Core.either,Core.cmd,Expr.eval,
      resetting_eval image s i hi,writing_eval image s i hi,committing_eval image s i hi,
      starting_eval image s i hi,releasing_eval image s i ha hi,
      pushing_eval image s i ha hi hs,popping_eval image s i ha hi,
      inputs,HostCorrespondence.statusValues,State.status]
    simp only [show (1#1 : BitVec 1) = BitVec.ofBool true from rfl,
      show (0#1 : BitVec 1) = BitVec.ofBool false from rfl,
      BitVec.not_not,inv_bool,and_bool,or_bool]
    simp [one_and,inv_bool,and_bool,or_bool,bne,Bool.beq_eq_decide_eq,Bool.and_assoc,Bool.or_assoc]
    rfl

def pins (i : Session.Pins) : Package.Pins :=
  ⟨BitVec.ofBool i.initialize,BitVec.ofBool i.csn,BitVec.ofBool i.sck,i.mosi,i.rawInputs⟩

def values (image : Image p) (s : Session.State a) : Package.State a :=
  ⟨HostCorrespondence.values s.host,SourceRefinement.values image s.core⟩

theorem host_inputs (i : Session.Pins) (t : Host.Status) :
    @Package.Pins.inputs (pins i) (HostCorrespondence.statusValues t) =
      @HostCorrespondence.inputs (i.host t) := by
  funext w port
  cases port <;> rfl

theorem core_inputs (image : Image p) (s : Session.State a) (i : Session.Pins) :
    (fun {w} => (values image s).coreInputs (.typed a) (pins i) (w := w)) =
      @HostCorrespondence.commandValues (s.command i) := by
  funext w port
  have hi : @Package.Pins.inputs (pins i) (fun _ => 0) =
      @HostCorrespondence.inputs (i.host {}) := by
    funext k input
    cases input <;> try rfl
    case status output => cases output <;> rfl
  change Frontend.circuit.observe ((pins i).inputs (fun _ => 0))
    (HostCorrespondence.values s.host) (.core port) = _
  rw [hi]
  exact HostCorrespondence.coreInput_eval (i.host {}) s.host port

def physicalPins (p : TinyWiring.Pins) : Session.Pins :=
  { «initialize» := !(p.ena.getLsbD 0 && p.rstN.getLsbD 0)
    csn := p.ui.getLsbD 0, sck := p.ui.getLsbD 1
    mosi := p.ui.extractLsb' 5 3 ++ p.ui.extractLsb' 2 1
    rawInputs := p.ui.extractLsb' 3 2 }

theorem physical_pins_correct (p : TinyWiring.Pins) :
    TinyWiring.Description.enginePins (TinyWiring.canonical a) p = pins (physicalPins p) := by
  cases p with
  | mk ui uio ena rstN =>
    have init : ~~~(ena &&& rstN) = BitVec.ofBool (!(ena.getLsbD 0 && rstN.getLsbD 0)) := by
      rw [← bit_roundtrip ena,← bit_roundtrip rstN,and_bool,inv_bool]
      cases ena.getLsbD 0 <;> cases rstN.getLsbD 0 <;> rfl
    have csn : ui.extractLsb' 0 1 = BitVec.ofBool (ui.getLsbD 0) := by
      exact (bit_roundtrip _).symm.trans (by simp only [BitVec.getLsbD_extractLsb']; rfl)
    have sck : ui.extractLsb' 1 1 = BitVec.ofBool (ui.getLsbD 1) := by
      exact (bit_roundtrip _).symm.trans (by simp only [BitVec.getLsbD_extractLsb']; rfl)
    change Package.Pins.mk (~~~(ena &&& rstN)) (ui.extractLsb' 0 1)
      (ui.extractLsb' 1 1) _ _ = _
    rw [init,csn,sck]
    rfl

theorem core_status (image : Image p) (s : Session.State a) (i : Session.Pins) (ha : a ≤ 3)
    (hi : Session.RuntimeInput s i) (hs : s.core.Structural) :
    (fun {w} => (values image s).status (.typed a) (pins i) (w := w)) =
      @HostCorrespondence.statusValues (s.core.status (image.pending.getLsbD 0) (s.command i).runtime) := by
  unfold Package.State.status
  rw [core_inputs]
  funext w port
  exact (InputCorrespondence.observe_equal (s.command i) (SourceRefinement.values image s.core)
    hi.2.2.1 hi.2.2.2 port).trans (observe_correct image s.core (s.command i).runtime ha hi hs port)

theorem frontend_inputs (image : Image p) (s : Session.State a) (i : Session.Pins) (ha : a ≤ 3)
    (hi : Session.RuntimeInput s i) (hs : s.core.Structural) :
    (fun {w} => (values image s).frontendInputs (.typed a) (pins i) (w := w)) =
      @HostCorrespondence.inputs (s.hostInput (image.pending.getLsbD 0) i) := by
  unfold Package.State.frontendInputs
  rw [core_status image s i ha hi hs]
  exact host_inputs i _

theorem step_correct (image : Image p) (s : Session.State a) (i : Session.Pins) (ha : a ≤ 3)
    (hi : Session.RuntimeInput s i) (hs : s.core.Structural) :
    (values image s).step (.typed a) (pins i) =
      values image (s.step p (image.pending.getLsbD 0) i) := by
  have front : @Circuit.step _ _ _ Frontend.circuit
      ((values image s).frontendInputs (.typed a) (pins i)) (HostCorrespondence.values s.host) =
      @HostCorrespondence.values (Host.step (s.hostInput (image.pending.getLsbD 0) i) s.host) := by
    rw [frontend_inputs image s i ha hi hs]
    exact HostCorrespondence.step_values _ _
  have core : @Circuit.step _ _ _ (Core.circuit a)
      ((values image s).coreInputs (.typed a) (pins i)) (SourceRefinement.values image s.core) =
      @SourceRefinement.values p a image (step p (s.command i).runtime s.core) := by
    rw [core_inputs]
    exact InputCorrespondence.source_step image s.core (s.command i) ha hi hs
  exact (congrArg (fun f => Package.State.mk f
    (@Circuit.step _ _ _ (Core.circuit a)
      ((values image s).coreInputs (.typed a) (pins i)) (SourceRefinement.values image s.core))) front).trans
    (congrArg (Package.State.mk (HostCorrespondence.values
      (Host.step (s.hostInput (image.pending.getLsbD 0) i) s.host))) core)

theorem run_correct (image : Image p) (s : Session.State a) (samples : List Session.Pins)
    (ha : a ≤ 3) (hi : Session.RuntimeTrace p (image.pending.getLsbD 0) s samples)
    (hs : s.core.Structural) :
    (values image s).run (.typed a) (samples.map pins) =
      values image (s.run p (image.pending.getLsbD 0) samples) := by
  induction samples generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change ((values image s).step (.typed a) (pins i)).run (.typed a) (rest.map pins) =
      values image ((s.step p (image.pending.getLsbD 0) i).run p (image.pending.getLsbD 0) rest)
    rw [step_correct image s i ha hi.1 hs]
    exact ih _ hi.2 (s.step_structural p _ i hs)

def outputs (s : Session.State a) (pending : Bool) (i : Session.Pins) : Values Package.Output
  | _, .miso => s.host.miso (s.hostInput pending i)
  | _, .ready => BitVec.ofBool (!i.initialize && s.host.ready)
  | _, .busy => BitVec.ofBool s.core.phase.busy
  | _, .levels => s.core.pins.levels
  | _, .enabled => s.core.pins.enabled

theorem outputs_correct (image : Image p) (s : Session.State a) (i : Session.Pins) (ha : a ≤ 3)
    (hi : Session.RuntimeInput s i) (hs : s.core.Structural) (port : Package.Output w) :
    (values image s).observe (.typed a) (pins i) port = outputs s (image.pending.getLsbD 0) i port := by
  cases port with
  | miso =>
    change Frontend.circuit.observe ((values image s).frontendInputs (.typed a) (pins i))
      (HostCorrespondence.values s.host) .miso = _
    rw [frontend_inputs image s i ha hi hs]
    exact HostCorrespondence.observe_correct _ _ .miso
  | ready =>
    change Frontend.circuit.observe ((values image s).frontendInputs (.typed a) (pins i))
      (HostCorrespondence.values s.host) .ready = _
    rw [frontend_inputs image s i ha hi hs]
    exact HostCorrespondence.observe_correct _ _ .ready
  | busy => exact congrArg (fun f : Values Core.Output => f .busy) (core_status image s i ha hi hs)
  | levels => exact congrArg (fun f : Values Core.Output => f .levels) (core_status image s i ha hi hs)
  | enabled => exact congrArg (fun f : Values Core.Output => f .enabled) (core_status image s i ha hi hs)

end Pinwheel.Hardware.Streaming.SessionCorrespondence
