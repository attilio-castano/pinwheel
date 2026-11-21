import Pinwheel.Hardware.Stream.Queue
import Pinwheel.Hardware.Arbitration.RoundRobin

namespace Pinwheel.Hardware.Switch

/-- The first switch campaign routes single-flit packets. -/
structure Packet (outputs : Nat) (α : Type) where
  destination : Fin outputs
  payload : α
  deriving Repr, DecidableEq

structure Delivery (extraInputs outputs : Nat) (α : Type) where
  source : Fin (extraInputs + 1)
  packet : Packet outputs α
  deriving Repr, DecidableEq

/-- There are extraInputs+1 input queues and outputs holding slots. Destination
is retained logically in slots; a hardware encoding may erase it after proving
the routing invariant. -/
structure State (extraInputs outputs : Nat) (α : Type) where
  queues : Fin (extraInputs + 1) → List (Packet outputs α)
  slots : Fin outputs → Option (Delivery extraInputs outputs α)
  cursor : Fin outputs → Fin (extraInputs + 1)

structure Input (extraInputs outputs : Nat) (α : Type) where
  reset : Bool
  offered : Fin (extraInputs + 1) → Option (Packet outputs α)
  ready : Fin outputs → Bool

structure Output (extraInputs outputs : Nat) (α : Type) where
  ready : Fin (extraInputs + 1) → Bool
  offered : Fin outputs → Option (Delivery extraInputs outputs α)

def initial : State n m α := ⟨fun _ => [], fun _ => none, fun _ => 0⟩

def request (s : State n m α) (o : Fin m) (k : Fin (n + 1)) : Bool :=
  (s.queues k).head?.any (fun p => decide (p.destination = o))

def canLoad (i : Input n m α) (s : State n m α) (o : Fin m) : Bool :=
  (s.slots o).isNone || i.ready o

/-- Grants refer exclusively to pre-edge queue heads. A full stalled output
does not arbitrate; its winner cannot change its held transaction. -/
def grant (i : Input n m α) (s : State n m α) (o : Fin m) : Option (Fin (n + 1)) :=
  if i.reset then none else if canLoad i s o then
    Arbitration.RoundRobin.grant (s.cursor o) (request s o) else none

def selectedDelivery (i : Input n m α) (s : State n m α) (o : Fin m) : Option (Delivery n m α) :=
  (grant i s o).bind (fun k => (s.queues k).head?.map (fun p => ⟨k, p⟩))

def pulled (i : Input n m α) (s : State n m α) (k : Fin (n + 1)) : Bool :=
  (List.finRange m).any (fun o => grant i s o == some k)

def queueInput (i : Input n m α) (s : State n m α) (k : Fin (n + 1)) : Stream.Input (Packet m α) :=
  ⟨i.reset, i.offered k, pulled i s k⟩

def slotInput (i : Input n m α) (s : State n m α) (o : Fin m) : Stream.Input (Delivery n m α) :=
  ⟨i.reset, selectedDelivery i s o, i.ready o⟩

def step (depth : Nat) (i : Input n m α) (s : State n m α) : State n m α where
  queues := fun k => (Stream.queue depth).step (queueInput i s k) (s.queues k)
  slots := fun o => (Stream.elastic id).step (slotInput i s o) (s.slots o)
  cursor := fun o => if i.reset then 0 else
    (grant i s o).map Arbitration.RoundRobin.next |>.getD (s.cursor o)

def observe (depth : Nat) (i : Input n m α) (s : State n m α) : Output n m α where
  ready := fun k => if i.reset then false else (Stream.queue depth).ready (pulled i s k) (s.queues k)
  offered := fun o => if i.reset then none else s.slots o

def component (depth : Nat) : Timed.Component (Input n m α) (State n m α) (Output n m α) :=
  ⟨step depth, observe depth⟩

def Valid (depth : Nat) (s : State n m α) : Prop :=
  (∀ k, (s.queues k).length ≤ depth) ∧
  (∀ o p, s.slots o = some p → p.packet.destination = o)

theorem initial_valid (depth : Nat) : Valid depth (initial : State n m α) := by
  simp [Valid, initial]

theorem requested_head (s : State n m α) (o : Fin m) (k : Fin (n + 1))
    (h : request s o k = true) : ∃ p, (s.queues k).head? = some p ∧ p.destination = o := by
  cases he : (s.queues k).head? <;> simp_all [request]

theorem request_unique (s : State n m α) (a b : Fin m) (k : Fin (n + 1))
    (ha : request s a k = true) (hb : request s b k = true) : a = b := by
  rcases requested_head s a k ha with ⟨p, hp, hpa⟩
  rcases requested_head s b k hb with ⟨q, hq, hqb⟩
  have he : p = q := Option.some.inj (hp.symm.trans hq)
  exact hpa.symm.trans (he ▸ hqb)

theorem grant_requested (i : Input n m α) (s : State n m α) (o : Fin m) (k : Fin (n + 1))
    (h : grant i s o = some k) : request s o k = true := by
  simp only [grant] at h
  split at h
  · contradiction
  · split at h
    · exact Arbitration.RoundRobin.grant_requested h
    · contradiction

theorem grant_unique (i : Input n m α) (s : State n m α) (a b : Fin m) (k : Fin (n + 1))
    (ha : grant i s a = some k) (hb : grant i s b = some k) : a = b :=
  request_unique s a b k (grant_requested i s a k ha) (grant_requested i s b k hb)

theorem selected_routed (i : Input n m α) (s : State n m α) (o : Fin m) (d : Delivery n m α)
    (h : selectedDelivery i s o = some d) : d.packet.destination = o := by
  cases hg : grant i s o with
  | none => simp [selectedDelivery, hg] at h
  | some k =>
    rcases requested_head s o k (grant_requested i s o k hg) with ⟨p, hp, hpo⟩
    have he : d = ⟨k, p⟩ := by simpa [selectedDelivery, hg, hp] using h.symm
    exact he ▸ hpo

theorem queues_bounded (depth : Nat) (i : Input n m α) (s : State n m α)
    (h : ∀ k, (s.queues k).length ≤ depth) :
    ∀ k, ((step depth i s).queues k).length ≤ depth :=
  fun k => (Stream.queueContract depth).preserved (queueInput i s k) (s.queues k) (h k)

theorem slots_routed (depth : Nat) (i : Input n m α) (s : State n m α)
    (h : ∀ o d, s.slots o = some d → d.packet.destination = o) :
    ∀ o d, (step depth i s).slots o = some d → d.packet.destination = o := by
  intro o d hd
  simp only [step, Stream.elastic, slotInput] at hd
  split at hd
  · contradiction
  · split at hd
    · exact selected_routed i s o d (by simpa using hd)
    · exact h o d hd

theorem valid_preserved (depth : Nat) (i : Input n m α) (s : State n m α)
    (h : Valid depth s) : Valid depth (step depth i s) :=
  ⟨queues_bounded depth i s h.1, slots_routed depth i s h.2⟩

theorem slot_stalled (depth : Nat) (i : Input n m α) (s : State n m α) (o : Fin m)
    (hr : i.reset = false) (hd : i.ready o = false) (hv : (s.slots o).isSome = true) :
    (step depth i s).slots o = s.slots o :=
  Stream.elastic_stalled id (slotInput i s o) (s.slots o) hr hd hv

theorem reset_state (depth : Nat) (i : Input n m α) (s : State n m α) (hr : i.reset = true) :
    step depth i s = initial := by
  simp [step, initial, queueInput, slotInput, Stream.queue, Stream.elastic, hr]

theorem reset_observe (depth : Nat) (i : Input n m α) (s : State n m α) (hr : i.reset = true) :
    observe depth i s = ⟨fun _ => false, fun _ => none⟩ := by
  simp [observe, hr]

theorem pulled_iff (i : Input n m α) (s : State n m α) (k : Fin (n + 1)) :
    pulled i s k = true ↔ ∃ o, grant i s o = some k := by
  simp [pulled]

theorem selected_head (i : Input n m α) (s : State n m α) (o : Fin m) (d : Delivery n m α)
    (h : selectedDelivery i s o = some d) :
    grant i s o = some d.source ∧ (s.queues d.source).head? = some d.packet := by
  cases hg : grant i s o with
  | none => simp [selectedDelivery, hg] at h
  | some k =>
    rcases requested_head s o k (grant_requested i s o k hg) with ⟨p, hp, _⟩
    have he : d = ⟨k, p⟩ := by simpa [selectedDelivery, hg, hp] using h.symm
    subst d
    exact ⟨rfl, hp⟩

theorem selected_of_grant (i : Input n m α) (s : State n m α) (o : Fin m) (k : Fin (n + 1))
    (h : grant i s o = some k) :
    selectedDelivery i s o = (s.queues k).head?.map (fun p => ⟨k, p⟩) := by
  simp [selectedDelivery, h]

def acceptedAt (depth : Nat) (i : Input n m α) (s : State n m α) (k : Fin (n + 1)) : List (Packet m α) :=
  if (observe depth i s).ready k then (i.offered k).toList else []

def emittedAt (i : Input n m α) (s : State n m α) (o : Fin m) : List (Delivery n m α) :=
  if i.reset then [] else if i.ready o then (s.slots o).toList else []

def transferredFrom (i : Input n m α) (s : State n m α) (k : Fin (n + 1)) : List (Packet m α) :=
  if pulled i s k then (s.queues k).head?.toList else []

/-- Per-input FIFO order, including same-edge replacement of a full queue. -/
theorem queue_balance (depth : Nat) (i : Input n m α) (s : State n m α) (k : Fin (n + 1))
    (hv : (s.queues k).length ≤ depth) (hr : i.reset = false) :
    s.queues k ++ acceptedAt depth i s k = transferredFrom i s k ++ (step depth i s).queues k := by
  have h := (Stream.queueContract depth).balance (queueInput i s k) (s.queues k) hv hr
  simpa [Stream.queueContract, Stream.accepted, Stream.emitted, Stream.Machine.component,
    Stream.queue, queueInput, acceptedAt, transferredFrom, observe, step, hr] using h

theorem selected_blocked (i : Input n m α) (s : State n m α) (o : Fin m)
    (h : canLoad i s o = false) : selectedDelivery i s o = none := by
  simp [selectedDelivery, grant, h]

/-- Every selected packet enters its output holding register exactly once. -/
theorem slot_balance (depth : Nat) (i : Input n m α) (s : State n m α) (o : Fin m)
    (hr : i.reset = false) :
    (s.slots o).toList ++ (selectedDelivery i s o).toList =
      emittedAt i s o ++ ((step depth i s).slots o).toList := by
  have h := (Stream.elasticContract (id : Delivery n m α → Delivery n m α)).balance
    (slotInput i s o) (s.slots o) True.intro hr
  simp only [Stream.elasticContract, Stream.Machine.component, Stream.elastic, Stream.accepted,
    Stream.emitted, slotInput, step, emittedAt, hr, Bool.false_eq_true, if_false, List.map_id] at h ⊢
  cases hc : canLoad i s o with
  | false =>
    have he := selected_blocked i s o hc
    simpa [he] using h
  | true =>
    have hc' : ((s.slots o).isNone || i.ready o) = true := hc
    simpa only [hc', if_true, id_eq] using h

theorem selected_iff (i : Input n m α) (s : State n m α) (o : Fin m) (k : Fin (n + 1))
    (p : Packet m α) : selectedDelivery i s o = some ⟨k, p⟩ ↔
      pulled i s k = true ∧ (s.queues k).head? = some p ∧ p.destination = o := by
  constructor
  · intro h
    have hs := selected_head i s o ⟨k, p⟩ h
    exact ⟨(pulled_iff i s k).mpr ⟨o, hs.1⟩, hs.2, selected_routed i s o ⟨k, p⟩ h⟩
  · rintro ⟨ht, hp, hpo⟩
    rcases (pulled_iff i s k).mp ht with ⟨a, ha⟩
    rcases requested_head s a k (grant_requested i s a k ha) with ⟨q, hq, hqa⟩
    have he : q = p := Option.some.inj (hq.symm.trans hp)
    have hao : a = o := hqa.symm.trans (he ▸ hpo)
    rw [hao] at ha
    simp [selectedDelivery, ha, hp]

/-- Internal transport appears once in the emitting source's ledger and once
in the receiving output's ledger. Other destinations and origins contribute []. -/
theorem transfer_exchange (i : Input n m α) (s : State n m α) (k : Fin (n + 1)) (o : Fin m) :
    ((transferredFrom i s k).filter (fun p => p.destination == o)).map (fun p => (⟨k, p⟩ : Delivery n m α)) =
      (selectedDelivery i s o).toList.filter (fun d => d.source == k) := by
  cases hs : selectedDelivery i s o with
  | none =>
    cases ht : pulled i s k <;> cases hp : (s.queues k).head? <;>
      simp [transferredFrom, ht, hp]
    intro hpo
    have he := (selected_iff i s o k _).mpr ⟨ht, hp, hpo⟩
    simp [hs] at he
  | some d =>
    by_cases hk : d.source = k
    · have hsel : selectedDelivery i s o = some ⟨k, d.packet⟩ := by simpa [← hk] using hs
      rcases (selected_iff i s o k d.packet).mp hsel with ⟨ht, hp, hpo⟩
      simp [transferredFrom, ht, hp, hpo, hk]
      exact Option.some.inj (hsel.symm.trans hs)
    · cases ht : pulled i s k <;> cases hp : (s.queues k).head? <;>
        simp [transferredFrom, ht, hp, hk]
      intro hpo
      have he := (selected_iff i s o k _).mpr ⟨ht, hp, hpo⟩
      exact hk (congrArg Delivery.source (Option.some.inj (hs.symm.trans he)))

end Pinwheel.Hardware.Switch
