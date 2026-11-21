import Pinwheel.Hardware.Stream.Queue
import Pinwheel.Hardware.Stream.Multiport
import Pinwheel.Hardware.Arbitration.RoundRobin

/-! A round-robin merge with one output holding register and no input queues.
Source provenance is logical: a later hardware encoding may erase the source
tag while retaining payload, slot validity, and the round-robin cursor.
-/
namespace Pinwheel.Hardware.Stream.BufferedMerge

structure Delivery (extraInputs : Nat) (α : Type) where
  source : Fin (extraInputs+1)
  payload : α
  deriving DecidableEq, Repr

structure State (extraInputs : Nat) (α : Type) where
  cursor : Fin (extraInputs+1)
  slot : Option (Delivery extraInputs α)
  deriving DecidableEq, Repr

abbrev Input (n : Nat) (α : Type) := Multiport.Input (n+1) 1 α
abbrev Output (n : Nat) (α : Type) := Multiport.Output (n+1) 1 (Delivery n α)

def initial : State n α := ⟨0, none⟩
def request (i : Input n α) (source : Fin (n+1)) : Bool := (i.offered source).isSome
def canLoad (i : Input n α) (s : State n α) : Bool := s.slot.isNone || i.ready 0

/-- A grant is an actual input acceptance, not just a combinational winner. -/
def grant (i : Input n α) (s : State n α) : Option (Fin (n+1)) :=
  if i.reset then none else if canLoad i s then
    Arbitration.RoundRobin.grant s.cursor (request i) else none

def selected (i : Input n α) (s : State n α) : Option (Delivery n α) :=
  (grant i s).bind (fun source => (i.offered source).map (fun payload => ⟨source, payload⟩))

def slotInput (i : Input n α) (s : State n α) : Stream.Input (Delivery n α) :=
  ⟨i.reset, selected i s, i.ready 0⟩

def step (i : Input n α) (s : State n α) : State n α :=
  ⟨if i.reset then 0 else ((grant i s).map Arbitration.RoundRobin.next).getD s.cursor,
    (elastic id).step (slotInput i s) s.slot⟩

def observe (i : Input n α) (s : State n α) : Output n α :=
  ⟨fun source => grant i s == some source, fun _ => if i.reset then none else s.slot⟩

def component : Timed.Component (Input n α) (State n α) (Output n α) := ⟨step, observe⟩

theorem grant_active (i : Input n α) (s : State n α) (winner : Fin (n+1))
    (h : grant i s = some winner) : i.reset = false ∧ canLoad i s = true := by
  cases hr : i.reset <;> cases hc : canLoad i s <;> simp_all [grant]

theorem grant_requested (i : Input n α) (s : State n α) (winner : Fin (n+1))
    (h : grant i s = some winner) : request i winner = true := by
  have active := grant_active i s winner h
  exact Arbitration.RoundRobin.grant_requested (by simpa [grant, active.1, active.2] using h)

theorem grant_offered (i : Input n α) (s : State n α) (winner : Fin (n+1))
    (h : grant i s = some winner) : ∃ payload, i.offered winner = some payload := by
  have requested := grant_requested i s winner h
  cases he : i.offered winner <;> simp_all [request]

theorem ready_iff (i : Input n α) (s : State n α) (source : Fin (n+1)) :
    (observe i s).ready source = true ↔ grant i s = some source := by
  simp [observe]

theorem unique_ready (i : Input n α) (s : State n α) (a b : Fin (n+1))
    (ha : (observe i s).ready a = true) (hb : (observe i s).ready b = true) : a = b :=
  Option.some.inj ((ready_iff i s a).mp ha |>.symm.trans ((ready_iff i s b).mp hb))

theorem accepted_iff_grant (i : Input n α) (s : State n α) (source : Fin (n+1)) :
    Multiport.accepted i (observe i s) source ≠ [] ↔ grant i s = some source := by
  cases hr : i.reset
  · cases hg : grant i s with
    | none => simp [Multiport.accepted, observe, hr, hg]
    | some winner =>
      obtain ⟨payload, hp⟩ := grant_offered i s winner hg
      by_cases he : winner = source
      · subst source
        simp [Multiport.accepted, observe, hr, hg, hp]
      · simp [Multiport.accepted, observe, hr, hg, he]
  · simp [Multiport.accepted, grant, hr]

theorem blocked_ready (i : Input n α) (s : State n α) (hc : canLoad i s = false)
    (source : Fin (n+1)) : (observe i s).ready source = false := by
  simp [observe, grant, hc]

theorem reset_state (i : Input n α) (s : State n α) (hr : i.reset = true) :
    step i s = initial := by
  simp [step, initial, elastic, slotInput, hr]

theorem reset_observe (i : Input n α) (s : State n α) (hr : i.reset = true) :
    observe i s = ⟨fun _ => false, fun _ => none⟩ := by
  simp [observe, grant, hr]

theorem capacity (s : State n α) : s.slot.toList.length ≤ 1 := by
  cases s.slot <;> simp

theorem selected_blocked (i : Input n α) (s : State n α) (hc : canLoad i s = false) :
    selected i s = none := by
  simp [selected, grant, hc]

theorem stalled (i : Input n α) (s : State n α)
    (hr : i.reset = false) (hd : i.ready 0 = false) (hv : s.slot.isSome = true) :
    (step i s).slot = s.slot :=
  elastic_stalled id (slotInput i s) s.slot hr hd hv

theorem cursor_after (i : Input n α) (s : State n α) (hr : i.reset = false) :
    (step i s).cursor = ((grant i s).map Arbitration.RoundRobin.next).getD s.cursor := by
  simp [step, hr]

theorem cursor_after_grant (i : Input n α) (s : State n α) (winner : Fin (n+1))
    (h : grant i s = some winner) : (step i s).cursor = Arbitration.RoundRobin.next winner := by
  simp [cursor_after i s (grant_active i s winner h).1, h]

theorem cursor_without_grant (i : Input n α) (s : State n α)
    (hr : i.reset = false) (h : grant i s = none) : (step i s).cursor = s.cursor := by
  simp [cursor_after i s hr, h]

/-- Updating to the next cursor need not change its value when there is only
one input. The condition is acceptance, not a comparison of cursor values. -/
theorem cursor_after_accept (i : Input n α) (s : State n α) (source : Fin (n+1))
    (h : Multiport.accepted i (observe i s) source ≠ []) :
    (step i s).cursor = Arbitration.RoundRobin.next source :=
  cursor_after_grant i s source ((accepted_iff_grant i s source).mp h)

theorem cursor_without_accept (i : Input n α) (s : State n α) (hr : i.reset = false)
    (h : ∀ source, Multiport.accepted i (observe i s) source = []) :
    (step i s).cursor = s.cursor := by
  cases hg : grant i s with
  | none => exact cursor_without_grant i s hr hg
  | some winner => exact False.elim (((accepted_iff_grant i s winner).mpr hg) (h winner))

theorem slot_after_grant (i : Input n α) (s : State n α) (winner : Fin (n+1)) (payload : α)
    (hg : grant i s = some winner) (hp : i.offered winner = some payload) :
    (step i s).slot = some ⟨winner, payload⟩ := by
  have ha := grant_active i s winner hg
  have available : (s.slot.isNone || i.ready 0) = true := ha.2
  simp only [step, elastic, slotInput, ha.1, Bool.false_eq_true, if_false, available,
    if_true, selected, hg, Option.bind_some, hp, Option.map_some, id_eq]

def emitted (i : Input n α) (s : State n α) : List (Delivery n α) :=
  if i.reset then [] else if i.ready 0 then s.slot.toList else []

/-- Reuse the elastic register's conservation theorem, including simultaneous
output consumption and input replacement. -/
theorem slot_balance (i : Input n α) (s : State n α) (hr : i.reset = false) :
    s.slot.toList ++ (selected i s).toList = emitted i s ++ (step i s).slot.toList := by
  have h := (elasticContract (id : Delivery n α → Delivery n α)).balance
    (slotInput i s) s.slot True.intro hr
  simp only [elasticContract, Machine.component, elastic, Stream.accepted,
    Stream.emitted, slotInput, step, emitted, hr, Bool.false_eq_true, if_false, List.map_id] at h ⊢
  cases hc : canLoad i s with
  | false => simpa [selected_blocked i s hc] using h
  | true =>
    have available : (s.slot.isNone || i.ready 0) = true := hc
    simpa only [available, if_true, id_eq] using h

/-- The source tag determines which input ledger receives the selected item. -/
theorem selected_source (i : Input n α) (s : State n α) (source : Fin (n+1))
    (hr : i.reset = false) :
    (selected i s).toList.filter (fun delivery => delivery.source == source) =
      (Multiport.accepted i (observe i s) source).map (fun payload => (⟨source, payload⟩ : Delivery n α)) := by
  cases hg : grant i s with
  | none => simp [selected, Multiport.accepted, observe, hr, hg]
  | some winner =>
    obtain ⟨payload, hp⟩ := grant_offered i s winner hg
    by_cases he : winner = source
    · subst source
      simp [selected, Multiport.accepted, observe, hr, hg, hp]
    · simp [selected, Multiport.accepted, observe, hr, hg, hp, he]

def pending (s : State n α) (source : Fin (n+1)) (_ : Fin 1) : List (Delivery n α) :=
  s.slot.toList.filter (fun delivery => delivery.source == source)

def flowContract : Multiport.Contract (component (n := n) (α := α))
    (fun _ => 0) Delivery.source (fun source payload => ⟨source, payload⟩) where
  pending := pending
  Valid := fun _ => True
  preserved := fun _ _ _ => True.intro
  reset_empty := by
    intro i s hr source destination
    simp [component, reset_state i s hr, pending, initial]
  balance := by
    intro i s _ hr source destination
    have hd : destination = 0 := Fin.ext (by omega)
    subst destination
    have h := congrArg (fun xs : List (Delivery n α) => xs.filter (fun delivery => delivery.source == source))
      (slot_balance i s hr)
    have filterAll (xs : List α) : xs.filter (fun _ => true) = xs :=
      List.filter_eq_self.mpr (fun _ _ => rfl)
    simp only [List.filter_append, selected_source i s source hr] at h
    simpa [component, pending, Multiport.forDestination, Multiport.fromSource, filterAll,
      Multiport.emitted, observe, emitted, hr] using h

/-- Per-source order and conservation throughout each reset epoch. Distinct
sources may interleave; equal payloads keep their distinct logical origins. -/
theorem transactions (inputs : List (Input n α)) :
    let result := Multiport.runHistory component initial {} inputs
    ∀ source destination,
      (Multiport.forDestination (fun _ => 0) destination (result.2.inputs source)).map
        (fun payload => (⟨source, payload⟩ : Delivery n α)) =
      Multiport.fromSource Delivery.source source (result.2.outputs destination) ++
        pending result.1 source destination :=
  flowContract.history initial {} True.intro (fun _ _ => rfl) inputs

def winners : State n α → List (Input n α) → List (Fin (n+1))
  | _, [] => []
  | s, i :: rest => (grant i s).toList ++ winners (step i s) rest

/-- Empty slots can refill even when downstream is not ready. Full stalled
slots and reset edges do not count as arbitration opportunities. -/
def opportunities : State n α → List (Input n α) → Nat
  | _, [] => 0
  | s, i :: rest => (if !i.reset && canLoad i s then 1 else 0) + opportunities (step i s) rest

def Persistent (target : Fin (n+1)) (inputs : List (Input n α)) : Prop :=
  ∀ i ∈ inputs, i.reset = false ∧ request i target = true

/-- Every accepted grant to a different source decreases the persistent
requester's round-robin distance. Priority itself is reused from RoundRobin. -/
theorem served_within_distance (target : Fin (n+1)) (s : State n α)
    (inputs : List (Input n α)) (h : Persistent target inputs)
    (enough : Arbitration.RoundRobin.distance s.cursor target < opportunities s inputs) :
    target ∈ winners s inputs := by
  induction inputs generalizing s with
  | nil => simp [opportunities] at enough
  | cons i rest ih =>
    have hi := h i (by simp)
    have hp : Persistent target rest := fun j hj => h j (by simp [hj])
    cases hg : grant i s with
    | none =>
      have blocked : canLoad i s = false := by
        cases hc : canLoad i s with
        | false => rfl
        | true =>
          have hn : Arbitration.RoundRobin.grant s.cursor (request i) = none := by
            simpa [grant, hi.1, hc] using hg
          have absent := (Arbitration.RoundRobin.grant_none_iff _ _).mp hn target
          simp [hi.2] at absent
      simp only [winners, hg, Option.toList_none, List.nil_append]
      apply ih _ hp
      simpa [opportunities, hi.1, blocked, cursor_after i s hi.1, hg] using enough
    | some winner =>
      simp only [winners, hg, Option.toList_some, List.singleton_append, List.mem_cons]
      by_cases he : winner = target
      · exact Or.inl he.symm
      · right
        apply ih _ hp
        have active := grant_active i s winner hg
        have chosen : Arbitration.RoundRobin.grant s.cursor (request i) = some winner := by
          simpa [grant, hi.1, active.2] using hg
        have decreases := Arbitration.RoundRobin.grant_progress chosen hi.2 he
        simp only [opportunities, hi.1, Bool.not_false, active.2, Bool.and_self, if_true] at enough
        rw [cursor_after_grant i s winner hg]
        omega

/-- A persistent request is accepted within N eligible slot-refill
opportunities. This is not a bound in clocks or a downstream delivery theorem. -/
theorem bounded_fairness (target : Fin (n+1)) (s : State n α)
    (inputs : List (Input n α)) (h : Persistent target inputs)
    (enough : n+1 ≤ opportunities s inputs) : target ∈ winners s inputs :=
  served_within_distance target s inputs h
    (Nat.lt_of_lt_of_le (Arbitration.RoundRobin.distance_lt _ _) enough)

end Pinwheel.Hardware.Stream.BufferedMerge
