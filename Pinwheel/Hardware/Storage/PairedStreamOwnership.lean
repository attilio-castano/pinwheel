import Pinwheel.Hardware.Storage.PairedStream
import Pinwheel.Hardware.Storage.PairedSession

/-! Ghost ownership for the stream supervisor's effective command history.
The inner ledger and SRAM response invariant are the existing paired proofs;
the added Bool is the represented supervisor bit, not a new hardware state. -/
namespace Pinwheel.Hardware.Storage.PairedStreamOwnership
open Pinwheel.Hardware Loader
set_option backward.isDefEq.respectTransparency false

structure Tracked where
  inner : PairedCoverage.Tracked
  enabled : Bool

def supervisorValues (enabled : Bool) : Values PairedStream.SupervisorRegister
  | _, .enabled => BitVec.ofBool enabled

def registers (s : Tracked) : Values PairedStream.Register :=
  Extended.values s.inner.registers (supervisorValues s.enabled)

def status (s : Tracked) : PairedStream.Status :=
  ⟨s.inner.registers .mode, s.inner.registers .valid == 1,
    s.inner.registers .pending == 1⟩

def policy (s : Tracked) (i : Machine.Inputs) : PairedStream.Transition :=
  PairedStream.step ⟨s.enabled⟩ (status s) i

def effective (s : Tracked) (i : Machine.Inputs) : Machine.Inputs :=
  (policy s i).effective

def advance (s : Tracked) (i : Machine.Inputs) : Tracked :=
  ⟨PairedCoverage.advance s.inner (effective s i).values, (policy s i).state.enabled⟩

def Invariant (s : Tracked) : Prop := PairedRuntime.Invariant s.inner

def EpochInput (i : Machine.Inputs) : Prop := i.init = false ∧ i.command ≠ 3

/-- COMMIT offered during a live reservation is consumed by the supervisor.
A simultaneous reset bypasses that reservation and remains an epoch boundary. -/
def ReservedInput (enabled : Bool) (i : Machine.Inputs) : Prop :=
  i.init = false ∧ (i.command ≠ 3 ∨ enabled = true ∧ i.reset = false)

def modelStatus (s : Tracked) (m : Reactive.Model) : PairedStream.Status :=
  ⟨(Reactive.embed m).mode, (status s).valid, (status s).pending⟩

def modelPolicy (s : Tracked) (m : Reactive.Model) (i : Machine.Inputs) : PairedStream.Transition :=
  PairedStream.step ⟨s.enabled⟩ (modelStatus s m) i

theorem effective_init (s : Tracked) (i : Machine.Inputs) :
    (effective s i).init = i.init := by rfl

theorem effective_reset (s : Tracked) (i : Machine.Inputs) :
    (effective s i).reset = i.reset := by rfl

theorem effective_incoming (s : Tracked) (i : Machine.Inputs) :
    (effective s i).incoming = i.incoming := by rfl

theorem invariant_next (s : Tracked) (i : Machine.Inputs) (h : Invariant s) :
    Invariant (advance s i) := by
  exact PairedRuntime.invariant_next s.inner (effective s i).values h

theorem invariant_initialize (s : Tracked) (i : Machine.Inputs) (hi : i.init = true) :
    Invariant (advance s i) := by
  exact PairedRuntime.invariant_initialize s.inner (effective s i).values
    (by simp [Machine.Inputs.values, effective_init, hi])

theorem initialize_disables (s : Tracked) (i : Machine.Inputs) (hi : i.init = true) :
    (advance s i).enabled = false := by
  simp [advance, policy, PairedStream.step, PairedStream.resetting, hi]

theorem status_related (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (m : Reactive.Model) (h : PairedTimed.Related p image s.inner m) :
    status s = modelStatus s m := by
  have hm := congrArg (fun v : Reactive.State => v.mode) h.2.2
  simp only [PairedEntry.view] at hm
  simp only [status, modelStatus, hm]
  done

theorem policy_related (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (m : Reactive.Model) (i : Machine.Inputs) (h : PairedTimed.Related p image s.inner m) :
    policy s i = modelPolicy s m i := by
  exact congrArg (fun st => PairedStream.step ⟨s.enabled⟩ st i) (status_related p image s m h)

theorem policy_agrees (s : Tracked) (i : Machine.Inputs) :
    PairedStream.policy (PairedClosed.feedback i.values s.inner.memory.q) (registers s) =
      policy s i := by
  rcases i with ⟨init, reset, command, data, incoming⟩
  simp [PairedStream.policy, PairedStream.state, PairedStream.status, PairedStream.rawInput,
    registers, supervisorValues, Extended.values, PairedClosed.feedback, Machine.Inputs.values,
    policy, status]
  cases he : s.enabled <;> cases init <;> cases reset <;> simp_all
  done

theorem effective_rule (s : Tracked) (i : Machine.Inputs) (hi : EpochInput i) :
    PairedCertified.Rule (effective s i).values := by
  rcases hi with ⟨hinit, hcmd⟩
  simp [PairedCertified.Rule, effective, policy, PairedStream.step,
    PairedStream.stopping, PairedStream.resetting, Machine.Inputs.values, hinit]
  repeat (split <;> simp_all [BitVec.ofNat_eq_ofNat])
  done

theorem enabled_effective_rule (s : Tracked) (i : Machine.Inputs) (he : s.enabled = true)
    (hi : i.init = false) (hr : i.reset = false) :
    PairedCertified.Rule (effective s i).values := by
  simp [PairedCertified.Rule, effective, policy, PairedStream.step, PairedStream.stopping,
    PairedStream.resetting, Machine.Inputs.values, he, hi, hr]
  repeat (split <;> simp_all)
  all_goals grind
  done

theorem effective_reserved_rule (s : Tracked) (i : Machine.Inputs)
    (hi : ReservedInput s.enabled i) : PairedCertified.Rule (effective s i).values := by
  rcases hi with ⟨hinit, hcmd | ⟨he, hr⟩⟩
  · exact effective_rule s i ⟨hinit, hcmd⟩
  · exact enabled_effective_rule s i he hinit hr

theorem context_next (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (i : Machine.Inputs) (h : PairedCertified.Context p image s.inner) (hi : EpochInput i) :
    PairedCertified.Context p image (advance s i).inner := by
  exact PairedCertified.context_next p image s.inner (effective s i).values h (effective_rule s i hi)

def coreOutput (s : Tracked) (i : Machine.Inputs) : Values Machine.Output :=
  fun {_} o => PairedController.body.observe
    (PairedCoverage.graphInputs (effective s i).values s.inner) s.inner.registers (.base o)

private theorem bit_get (v : BitVec 1) : BitVec.ofBool v[0] = v := by
  rcases PairedUpload.bit_cases v with h | h <;> simp [h]

theorem core_output_agrees (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (m : Reactive.Model) (i : Machine.Inputs) (h : PairedTimed.Related p image s.inner m) :
    (coreOutput s i : Values Machine.Output) =
      (PairedHost.withExecution (coreOutput s i) m : Values Machine.Output) := by
  funext w o
  cases o with
  | control r => rfl
  | core o =>
    cases o with
    | readA | readB => rfl
    | busy => exact PairedTimedStep.busy_model _ _ _ (PairedCoverage.graph_equations (effective s i).values s.inner) h.2.2
    | state r =>
      have hv := (PairedTimed.graph_observe _ _
        (PairedCoverage.graph_equations (effective s i).values s.inner)).trans h.2.2
      have he := congrArg (fun v : Reactive.State => v.values r) hv
      cases r with
      | sample k =>
        simpa [PairedTimed.observe, Reactive.fromValues, Reactive.State.values,
          coreOutput, PairedHost.withExecution, bit_get] using he
      | _ => exact he
      done
  done

private theorem accepting_wire (g : Values PairedController.GraphInput)
    (rs : Values PairedController.Register)
    (h : PairedSemantics.Equations PairedController.bindings g rs) :
    PairedController.accepting.eval g rs = PairedController.acceptingExpr.eval g rs := by
  simpa only [PairedController.accepting, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .accepting (.concat (.lit (0 : BitVec 63)) PairedController.acceptingExpr)
        (by simp [PairedController.bindings]))

theorem start_value (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (m : Reactive.Model) (i : Machine.Inputs) (h : PairedTimed.Related p image s.inner m)
    (hi : PairedCertified.Rule (effective s i).values) :
    coreOutput s i (.control .start) = BitVec.ofBool
      (!PairedEdges.resetRequested (effective s i).values &&
        !Engine.Reactive.busy m && ((effective s i).command == 5)) := by
  simp only [coreOutput, Circuit.observe, PairedController.body,
    PairedRunning.start_wire _ _ (PairedCoverage.graph_equations (effective s i).values s.inner),
    PairedController.startExpr, PairedController.both, PairedController.cmd, Expr.eval,
    accepting_wire _ _ (PairedCoverage.graph_equations (effective s i).values s.inner),
    PairedController.acceptingExpr, PairedController.either, Expr.eval,
    PairedEdges.resetting_value s.inner (effective s i).values hi,
    PairedTimedStep.busy_model _ _ _ (PairedCoverage.graph_equations (effective s i).values s.inner) h.2.2,
    h.1.valid]
  simp [show PairedCoverage.graphInputs (effective s i).values s.inner (.base .command) =
      (effective s i).command from rfl, Bool.beq_eq_decide_eq, Bool.and_assoc]
  simp only [show (1#1) = BitVec.ofBool true from rfl,
    BitVec.ofBool_and_ofBool, Bool.and_true, Bool.and_assoc]
  done

theorem busy_value (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (m : Reactive.Model) (i : Machine.Inputs) (h : PairedTimed.Related p image s.inner m) :
    coreOutput s i (.core .busy) = BitVec.ofBool (Engine.Reactive.busy m) := by
  exact PairedTimedStep.busy_model _ _ _ (PairedCoverage.graph_equations (effective s i).values s.inner) h.2.2

private theorem bool_one (b : Bool) : (BitVec.ofBool b == (1 : BitVec 1)) = b := by
  cases b <;> rfl

theorem active_value (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (m : Reactive.Model) (i : Machine.Inputs) (h : PairedTimed.Related p image s.inner m)
    (hi : PairedCertified.Rule (effective s i).values) :
    (coreOutput s i (.core .busy) == 1 || coreOutput s i (.control .start) == 1) =
      (Engine.Reactive.busy m ||
        (!PairedEdges.resetRequested (effective s i).values && ((effective s i).command == 5))) := by
  rw [busy_value p image s m i h, start_value p image s m i h hi, bool_one, bool_one]
  cases hb : Engine.Reactive.busy m <;> simp
  done

theorem related_next (p : Execution.Image) (image : PairedImage.Image) (s : Tracked)
    (m : Reactive.Model) (i : Machine.Inputs) (h : PairedTimed.Related p image s.inner m)
    (hi : EpochInput i) :
    PairedTimed.Related p image (advance s i).inner
      ((PairedTimed.reference p).step (effective s i).values m) := by
  exact (PairedTimed.refinement p image).step _ _ _ (effective_rule s i hi) h

/-- Quiet and ordinary loader commands pass unchanged before arming. -/
theorem disabled_pass (s : Tracked) (i : Machine.Inputs) (hs : s.enabled = false)
    (hi : i.command ≠ 6) : effective s i = i ∧ (advance s i).enabled = false := by
  simp only [BitVec.ofNat_eq_ofNat] at hi
  simp [effective, advance, policy, PairedStream.step, PairedStream.arming,
    PairedStream.rearming, PairedStream.stopping, hs, hi]
  done

def run (s : Tracked) (history : List Machine.Inputs) : Tracked := history.foldl advance s

theorem disabled_run (s : Tracked) (history : List Machine.Inputs) (hs : s.enabled = false)
    (hi : ∀ i ∈ history, i.command ≠ 6) :
    (run s history).inner = PairedSession.run s.inner history ∧ (run s history).enabled = false := by
  induction history generalizing s with
  | nil => exact ⟨rfl, hs⟩
  | cons i rest ih =>
    have hp := disabled_pass s i hs (hi i (by simp))
    have ht := ih (advance s i) hp.2 (fun j hj => hi j (by simp [hj]))
    simpa only [run, PairedSession.run, List.foldl_cons, advance, hp.1] using ht
    done

theorem delivered_no_arm {history : List Machine.Inputs} {commands : List (BitVec 3 × BitVec 64)}
    (hd : Machine.Delivers history commands) (hc : ∀ c ∈ commands, c.1 ≠ 6) :
    ∀ i ∈ history, i.command ≠ 6 := by
  induction hd with
  | nil => simp
  | quiet hq _ ih =>
    simp only [List.forall_mem_cons]
    exact ⟨by simp [hq.2.2], ih hc⟩
  | command hcar _ ih =>
    simp only [List.forall_mem_cons] at hc ⊢
    refine ⟨?_, ih hc.2⟩
    rw [hcar.2.2.1]
    split <;> simp_all
    done

theorem upload_admitted (p : Execution.Image) (image : PairedImage.Image)
    (cert : PairedImage.Corresponds p image) (d₀ d₁ : BitVec 64)
    (history : List Machine.Inputs) (s : Tracked) (hs : PairedSession.Stopped s.inner)
    (he : s.enabled = false)
    (hd : Machine.Delivers history (Machine.uploadCommands (PairedImage.upload image) d₀ d₁)) :
    PairedTimed.Related p image (run s history).inner (Engine.Reactive.reset p) ∧
      (run s history).enabled = false := by
  have hc := delivered_no_arm hd (by simp [Machine.uploadCommands]; grind)
  have hr := disabled_run s history he hc
  exact ⟨hr.1.symm ▸ PairedSession.upload_admitted p image cert d₀ d₁ history s.inner hs hd, hr.2⟩
  done

def Reserved (s : Tracked) : Prop :=
  s.enabled = true → s.inner.registers .valid = 1 ∧ s.inner.registers .pending = 0

theorem enabled_next_conditions (s : Tracked) (i : Machine.Inputs)
    (hn : (advance s i).enabled = true) :
    PairedStream.resetting i = false ∧ PairedStream.stopping i = false ∧
      (s.enabled = true ∨ (status s).valid = true ∧ (status s).pending = false) := by
  simp only [advance, policy, PairedStream.step] at hn
  grind [PairedStream.arming]
  done

theorem enabled_next_command (s : Tracked) (i : Machine.Inputs)
    (hn : (advance s i).enabled = true) :
    (effective s i).command = 0 ∨ (effective s i).command = 5 ∨ (effective s i).command = 6 := by
  have hc := enabled_next_conditions s i hn
  simp [effective, policy, PairedStream.step, advance, hc.1, hc.2.1] at *
  grind
  done

private theorem valid_pending_next (s : PairedCoverage.Tracked) (i : Machine.Inputs)
    (hi : i.init = false) (hc : i.command = 0 ∨ i.command = 5 ∨ i.command = 6)
    (hv : s.registers .valid = 1) (hp : s.registers .pending = 0) :
    (PairedUpload.control (PairedCoverage.advance s i.values).registers).valid = true ∧
      (PairedUpload.control (PairedCoverage.advance s i.values).registers).pending = false := by
  change (PairedUpload.control (PairedController.body.step
      (PairedCoverage.graphInputs i.values s) s.registers)).valid = true ∧
    (PairedUpload.control (PairedController.body.step
      (PairedCoverage.graphInputs i.values s) s.registers)).pending = false
  rw [PairedUpload.control_next _ _ (PairedCoverage.graph_equations i.values s)]
  have hz : (PairedUpload.inputs (PairedCoverage.graphInputs i.values s) s.registers).init = false := by
    simp [PairedUpload.inputs, PairedUpload.init_value _ _ (PairedCoverage.graph_equations i.values s),
      show PairedCoverage.graphInputs i.values s (.base .init) = i.values .init from rfl,
      Machine.Inputs.values, hi]
  simp only [BitVec.ofNat_eq_ofNat] at hc hv hp
  rcases hc with hc | hc | hc <;>
    simp [PairedLoader.next, PairedLoader.commit, PairedLoader.push, hz,
      show (PairedUpload.inputs (PairedCoverage.graphInputs i.values s) s.registers).command =
        i.command from rfl, hc, PairedUpload.control, hv, hp, apply_ite]
  done

theorem reserved_next (s : Tracked) (i : Machine.Inputs) (h : Reserved s) :
    Reserved (advance s i) := by
  intro hn
  have hc := enabled_next_conditions s i hn
  have hold : s.inner.registers .valid = 1 ∧ s.inner.registers .pending = 0 := by
    rcases hc.2.2 with he | hs
    · exact h he
    · have hv := (PairedUpload.bit_value (s.inner.registers .valid)).symm
      have hp := (PairedUpload.bit_value (s.inner.registers .pending)).symm
      change (s.inner.registers .valid == 1) = true ∧ (s.inner.registers .pending == 1) = false at hs
      exact ⟨hv.trans (congrArg BitVec.ofBool hs.1), hp.trans (congrArg BitVec.ofBool hs.2)⟩
      done
  have hz := hc.1
  simp [PairedStream.resetting] at hz
  have hnext := valid_pending_next s.inner (effective s i)
    ((effective_init s i).trans hz.1.1) (enabled_next_command s i hn) hold.1 hold.2
  exact ⟨(PairedUpload.bit_value ((advance s i).inner.registers .valid)).symm.trans
      (congrArg BitVec.ofBool hnext.1),
    (PairedUpload.bit_value ((advance s i).inner.registers .pending)).symm.trans
      (congrArg BitVec.ofBool hnext.2)⟩
  done

theorem reserved_disabled (s : Tracked) (h : s.enabled = false) : Reserved s := by
  simp [Reserved, h]

theorem reserved_run (s : Tracked) (history : List Machine.Inputs) (h : Reserved s) :
    Reserved (run s history) := by
  induction history generalizing s with
  | nil => exact h
  | cons i rest ih => exact ih (advance s i) (reserved_next s i h)

theorem quiet_pending (s : PairedCoverage.Tracked) (i : Machine.Inputs) (hq : Machine.Quiet i) :
    (PairedCoverage.advance s i.values).registers .pending = s.registers .pending := by
  have hi : PairedCertified.Rule i.values := by
    simp [PairedCertified.Rule, Machine.Inputs.values, hq.1, hq.2.2]
  simp [PairedCoverage.advance, Circuit.step, PairedController.body, PairedController.next,
    PairedController.cmd, PairedController.either, Expr.eval,
    PairedEdges.resetting_value s i.values hi, PairedCertified.commit_zero s i.values hi,
    PairedEdges.resetRequested, Machine.Inputs.values, hq.2.1, hq.2.2,
    show PairedCoverage.graphInputs i.values s (.base .command) = i.command from rfl]
  done

theorem accepted_pending (s : PairedCoverage.Tracked) (i : Machine.Inputs)
    (hc : PairedLifecycle.Accepted s i.values) :
    (PairedCoverage.advance s i.values).registers .pending = 0 := by
  have accepted : PairedLoader.commit (PairedUpload.inputs (PairedCoverage.graphInputs i.values s) s.registers)
      (PairedUpload.control s.registers) = true := by
    simpa only [PairedLifecycle.Accepted,
      PairedUpload.commit_value _ _ (PairedCoverage.graph_equations i.values s), Reactive.bool_one] using hc
  obtain ⟨hi, hr, hb, hcmd, _, _⟩ := PairedLoader.commit_requires _ _ accepted
  have hn := congrArg Loader.State.pending
    (PairedUpload.control_next _ _ (PairedCoverage.graph_equations i.values s))
  simp [PairedLoader.next, hi, hr, hb, hcmd, accepted] at hn
  exact (PairedUpload.bit_value ((PairedCoverage.advance s i.values).registers .pending)).symm.trans
    (congrArg BitVec.ofBool hn)
  done

theorem quiet_run_pending (history : List Machine.Inputs) (s : PairedCoverage.Tracked)
    (hp : s.registers .pending = 0) (hd : Machine.Delivers history []) :
    (PairedSession.run s history).registers .pending = 0 := by
  induction history generalizing s with
  | nil => exact hp
  | cons i rest ih =>
    cases hd with
    | quiet hq hd => exact ih _ ((quiet_pending s i hq).trans hp) hd

private theorem finish_upload_pending (p : Execution.Image) (image : PairedImage.Image)
    (cert : PairedImage.Corresponds p image) (d : BitVec 64) (history : List Machine.Inputs)
    (s : PairedCoverage.Tracked) (words rest : List (BitVec 64))
    (hw : PairedImage.upload image = words ++ rest) (hs : PairedSession.Staging words s)
    (hd : Machine.Delivers history (rest.map (fun word => ((2 : BitVec 3), word)) ++ [(3, d)])) :
    (PairedSession.run s history).registers .pending = 0 := by
  induction history generalizing s words rest with
  | nil =>
    cases rest with
    | nil => simp only [List.map_nil, List.nil_append] at hd; cases hd
    | cons word rest => simp only [List.map_cons, List.cons_append] at hd; cases hd
  | cons i tail ih =>
    cases rest with
    | nil =>
      simp only [List.map_nil, List.nil_append, List.append_nil] at hd hw
      cases hd with
      | quiet hq hd =>
        exact ih (PairedCoverage.advance s i.values) words [] (by simpa using hw)
          (PairedSession.staging_quiet words s i hs hq) (by simpa using hd)
      | command hc hd =>
        exact quiet_run_pending tail _
          (accepted_pending s i (PairedSession.commit_accepted image s i d (hw ▸ hs) hc)) hd
    | cons word rest =>
      simp only [List.map_cons, List.cons_append] at hd
      cases hd with
      | quiet hq hd =>
        exact ih (PairedCoverage.advance s i.values) words (word :: rest) hw
          (PairedSession.staging_quiet words s i hs hq) (by simpa using hd)
      | command hc hd =>
        have hp := PairedSession.staging_push s i words hs
          (PairedSession.push_accepted p image cert s i words word rest hs hw hc)
        exact ih (PairedCoverage.advance s i.values) (words ++ [word]) rest (by simpa using hw)
          (by simpa only [hc.2.2.2] using hp) hd
        done

theorem loader_upload_pending (p : Execution.Image) (image : PairedImage.Image)
    (cert : PairedImage.Corresponds p image) (d₀ d₁ : BitVec 64)
    (history : List Machine.Inputs) (s : PairedCoverage.Tracked) (hs : PairedSession.Stopped s)
    (hd : Machine.Delivers history (Machine.uploadCommands (PairedImage.upload image) d₀ d₁)) :
    (PairedSession.run s history).registers .pending = 0 := by
  induction history generalizing s with
  | nil => cases hd
  | cons i tail ih =>
    cases hd with
    | quiet hq hd =>
      exact ih _ (PairedSession.stopped_next s i hs (by simp only [hq.2.2]; decide)) hd
    | command hc hd =>
      exact finish_upload_pending p image cert d₁ tail (PairedCoverage.advance s i.values) []
        (PairedImage.upload image) rfl (PairedSession.staging_begin s i d₀ hs hc) hd

theorem upload_pending_false (p : Execution.Image) (image : PairedImage.Image)
    (cert : PairedImage.Corresponds p image) (d₀ d₁ : BitVec 64)
    (history : List Machine.Inputs) (s : Tracked) (hs : PairedSession.Stopped s.inner)
    (he : s.enabled = false)
    (hd : Machine.Delivers history (Machine.uploadCommands (PairedImage.upload image) d₀ d₁)) :
    (run s history).inner.registers .pending = 0 := by
  have hr := disabled_run s history he (delivered_no_arm hd (by simp [Machine.uploadCommands]; grind))
  rw [hr.1]
  exact loader_upload_pending p image cert d₀ d₁ history s.inner hs hd

theorem arm_admitted (s : Tracked) (i : Machine.Inputs) (he : s.enabled = false)
    (hv : s.inner.registers .valid = 1) (hp : s.inner.registers .pending = 0)
    (hb : PairedStream.busy (status s) = false) (hi : i.init = false) (hr : i.reset = false)
    (hc : i.command = 6) (hd : i.data = 1) :
    (effective s i).command = 5 ∧ (advance s i).enabled = true := by
  simp only [BitVec.ofNat_eq_ofNat] at hv hp hc hd
  simp [effective, advance, policy, PairedStream.step, PairedStream.arming,
    PairedStream.rearming, PairedStream.stopping, PairedStream.resetting,
    status, he, hv, hp, hi, hr, hc, hd]
  simpa [status, hv, hp] using hb
  done

theorem enabled_next_no_reset (s : Tracked) (i : Machine.Inputs)
    (hn : (advance s i).enabled = true) :
    PairedEdges.resetRequested (effective s i).values = false := by
  have hc := enabled_next_conditions s i hn
  have hz := hc.1
  simp [PairedStream.resetting] at hz
  rcases enabled_next_command s i hn with hcmd | hcmd | hcmd <;>
    simp [PairedEdges.resetRequested, Machine.Inputs.values, effective_reset, hz.1.2, hcmd]

theorem enabling_starts (s : Tracked) (i : Machine.Inputs) (he : s.enabled = false)
    (hn : (advance s i).enabled = true) : (effective s i).command = 5 := by
  have hc := enabled_next_conditions s i hn
  simp [advance, policy, PairedStream.step, he, hc.1, hc.2.1] at hn
  simp [effective, policy, PairedStream.step, he, hc.1, hc.2.1, hn]
  done

end Pinwheel.Hardware.Storage.PairedStreamOwnership
