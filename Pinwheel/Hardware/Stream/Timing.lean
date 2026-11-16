import Pinwheel.Hardware.Stream.Properties

namespace Pinwheel.Hardware.Stream

set_option backward.isDefEq.respectTransparency false

/-- A precise no-stall latency contract. Slots are ordered from output toward
input; each edge removes the head and appends the newly accepted mapped input. -/
structure Delay (m : Machine α β S) (f : α → β) (initial : S) (latency : Nat) where
  slots : S → List (Option β)
  Valid : S → Prop
  initial_valid : Valid initial
  initial_slots : slots initial = List.replicate latency none
  positive : 0 < latency
  length : ∀ s, Valid s → (slots s).length = latency
  offer : ∀ s, Valid s → m.offer s = (slots s).head?.join
  ready : ∀ s, Valid s → m.ready true s = true
  step : ∀ i s, Valid s → i.reset = false → i.ready = true →
    Valid (m.step i s) ∧ slots (m.step i s) = (slots s).tail ++ [i.offered.map f]

def delayElastic (f : α → β) : Delay (elastic f) f none 1 where
  slots := fun s => [s]
  Valid := fun _ => True
  initial_valid := True.intro
  initial_slots := rfl
  positive := by decide
  length := fun _ _ => rfl
  offer := fun _ _ => rfl
  ready := by intros; simp [elastic]
  step := by intros; simp_all [elastic]

def delayQueue (depth : Nat) (hd : 0 < depth) : Delay (queue depth (α := α)) id [] 1 where
  slots := fun q => [q.head?]
  Valid := fun q => q.length ≤ 1
  initial_valid := by simp
  initial_slots := rfl
  positive := by decide
  length := fun _ _ => rfl
  offer := fun _ _ => rfl
  ready := by
    intro s h
    simp only [queue, if_true, decide_eq_true_eq, List.length_tail]
    omega
  step := by
    intro i s h hr hd'
    have ht : s.tail = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_tail]; omega)
    cases hi : i.offered <;> simp [queue, hr, hd', ht, hd, hi]

theorem option_head_tail (q : List (Option α)) (hn : q ≠ []) :
    q.head?.join :: q.tail = q := by
  cases q <;> simp_all

def Delay.serial {a : Machine α β S} {b : Machine β γ T} {f : α → β} {g : β → γ}
    (da : Delay a f sa na) (db : Delay b g sb nb) :
    Delay (a.serial b) (g ∘ f) (sa, sb) (nb + na) where
  slots := fun s => db.slots s.2 ++ (da.slots s.1).map (Option.map g)
  Valid := fun s => da.Valid s.1 ∧ db.Valid s.2
  initial_valid := ⟨da.initial_valid, db.initial_valid⟩
  initial_slots := by
    simp only [da.initial_slots, db.initial_slots, List.map_replicate, Option.map_none,
      List.replicate_append_replicate]
  positive := by have := da.positive; omega
  length := by intros; simp_all [List.length_append, da.length, db.length]
  offer := by
    intro s h
    have hn : db.slots s.2 ≠ [] := by have := db.length s.2 h.2; have := db.positive; intro he; simp [he] at *; omega
    simp only [Machine.serial, db.offer s.2 h.2]
    cases he : db.slots s.2 <;> simp_all
  ready := by intro s h; simp only [Machine.serial, db.ready s.2 h.2, da.ready s.1 h.1]
  step := by
    intro i s h hr hd
    have hbready : b.ready i.ready s.2 = true := by simpa only [hd] using db.ready s.2 h.2
    have ha := da.step (b.leftInput i s.2) s.1 h.1 hr hbready
    have hb := db.step (a.rightInput i s.1) s.2 h.2 hr hd
    refine ⟨⟨ha.1, hb.1⟩, ?_⟩
    change db.slots (b.step (a.rightInput i s.1) s.2) ++
      (da.slots (a.step (b.leftInput i s.2) s.1)).map (Option.map g) = _
    rw [ha.2, hb.2]
    simp only [Machine.leftInput, Machine.rightInput, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, Option.map_map]
    rw [da.offer s.1 h.1]
    have hna : da.slots s.1 ≠ [] := by
      have := da.length s.1 h.1; have := da.positive
      intro he; simp [he] at *; omega
    have hnb : db.slots s.2 ≠ [] := by
      have := db.length s.2 h.2; have := db.positive
      intro he; simp [he] at *; omega
    cases hea : da.slots s.1 <;> cases heb : db.slots s.2 <;>
      simp_all [List.append_assoc]

def delayPipeline (m : Map wi wo) (extra : Nat) :
    Delay (Design.pipeline m extra).flatten.machine
      (Design.pipeline m extra).flatten.function (Design.pipeline m extra).flatten.initial (extra + 1) := by
  induction extra generalizing wi with
  | zero => exact delayElastic m.function
  | succ n ih => exact (delayElastic m.function).serial (ih (Map.identity wo))

/-- With continuous downstream readiness, an initially empty FIFO contributes
one edge regardless of depth, and each elastic stage contributes one edge. -/
def delayDesign (m : Map wi wo) (depth extra : Nat) (hd : 0 < depth) :
    Delay (Design.buffered m depth hd extra).flatten.machine
      (Design.buffered m depth hd extra).flatten.function
      (Design.buffered m depth hd extra).flatten.initial (extra + 2) :=
  (delayQueue depth hd).serial (delayPipeline m extra)

def noStall (m : Machine α β S) : Timed.Component (Option α) S (Option β) :=
  ⟨fun i s => m.step ⟨false, i, true⟩ s, fun _ s => m.offer s⟩

def shiftModel (f : α → β) : Timed.Component (Option α) (List (Option β)) (Option β) :=
  ⟨fun i s => s.tail ++ [i.map f], fun _ s => s.head?.join⟩

/-- Whole traces agree with a literal latency-element shift register, including
bubbles. This establishes exact latency and one transfer per edge after fill. -/
theorem Delay.noStall_trace {m : Machine α β S} (d : Delay m f initial latency)
    (inputs : List (Option α)) :
    (noStall m).trace initial inputs =
      (shiftModel f).trace (List.replicate latency none) inputs := by
  let r : Timed.Refinement (noStall m) (shiftModel f) := {
    Rel := fun s q => d.Valid s ∧ q = d.slots s
    step := by
      intro i s q h
      rcases h with ⟨hv, rfl⟩
      have hs := d.step ⟨false, i, true⟩ s hv rfl rfl
      exact ⟨hs.1, hs.2.symm⟩
    observe := fun _ s _ h => by simpa only [noStall, shiftModel, h.2] using d.offer s h.1 }
  exact r.trace_eq _ _ ⟨d.initial_valid, d.initial_slots.symm⟩ inputs

/-- Applying no input and accepting all output for n edges. -/
def flush (m : Machine α β S) : Nat → S → S
  | 0, s => s
  | n + 1, s => flush m n (m.step ⟨false, none, true⟩ s)

theorem flush_add (m : Machine α β S) (a b : Nat) (s : S) :
    flush m (a + b) s = flush m b (flush m a s) := by
  induction a generalizing s with
  | zero => simp [flush]
  | succ a ih => simpa only [Nat.succ_add, flush] using ih (m.step ⟨false, none, true⟩ s)

structure Drain (m : Machine α β S) (initial : S) (bound : Nat) where
  Valid : S → Prop
  initial_valid : Valid initial
  ready : ∀ s, Valid s → m.ready true s = true
  preserved : ∀ i s, Valid s → i.reset = false → i.ready = true → Valid (m.step i s)
  empty_offer : m.offer initial = none
  empty_fixed : m.step ⟨false, none, true⟩ initial = initial
  clears : ∀ s, Valid s → flush m bound s = initial

theorem Drain.flush_valid {m : Machine α β S} (d : Drain m initial bound)
    (n : Nat) (s : S) (h : d.Valid s) : d.Valid (flush m n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih _ (d.preserved _ s h rfl rfl)

def drainElastic (f : α → β) : Drain (elastic f) none 1 where
  Valid := fun _ => True
  initial_valid := True.intro
  ready := by intros; simp [elastic]
  preserved := by intros; trivial
  empty_offer := rfl
  empty_fixed := rfl
  clears := by intros; simp [flush, elastic]

theorem flush_queue (depth n : Nat) (q : List α) : flush (queue depth) n q = q.drop n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    have hs : (queue depth).step ⟨false, none, true⟩ q = q.tail := by simp [queue]
    rw [flush, hs, ih, List.drop_tail]

def drainQueue (depth : Nat) (hd : 0 < depth) : Drain (queue depth (α := α)) [] depth where
  Valid := fun q => q.length ≤ depth
  initial_valid := by simp
  ready := by intro s h; simp only [queue, if_true, decide_eq_true_eq, List.length_tail]; omega
  preserved := fun i s h _ _ => (queueContract depth).preserved i s h
  empty_offer := rfl
  empty_fixed := by simp [queue]
  clears := by intro s h; rw [flush_queue]; exact List.drop_eq_nil_iff.mpr h

theorem flush_serial_first {a : Machine α β S} {b : Machine β γ T}
    (da : Drain a sa na) (db : Drain b sb nb) (n : Nat) (s : S × T)
    (h : da.Valid s.1 ∧ db.Valid s.2) :
    (flush (a.serial b) n s).1 = flush a n s.1 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have hr := db.ready s.2 h.2
    have he : b.leftInput (⟨false, none, true⟩ : Input α) s.2 = ⟨false, none, true⟩ := by
      simp only [Machine.leftInput, hr]
    rw [flush]
    rw [ih _ ⟨da.preserved _ _ h.1 rfl hr, db.preserved _ _ h.2 rfl rfl⟩]
    simp only [Machine.serial, he, flush]

theorem flush_serial_empty {a : Machine α β S} {b : Machine β γ T}
    (da : Drain a sa na) (db : Drain b sb nb) (n : Nat) (t : T) (h : db.Valid t) :
    flush (a.serial b) n (sa, t) = (sa, flush b n t) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    have hr := db.ready t h
    have he : (a.serial b).step ⟨false, none, true⟩ (sa, t) =
        (sa, b.step ⟨false, none, true⟩ t) := by
      simp only [Machine.serial, Machine.leftInput, Machine.rightInput, hr, da.empty_offer, da.empty_fixed]
    rw [flush, he, ih _ (db.preserved _ _ h rfl rfl)]
    rfl

def Drain.serial {a : Machine α β S} {b : Machine β γ T}
    (da : Drain a sa na) (db : Drain b sb nb) : Drain (a.serial b) (sa, sb) (na + nb) where
  Valid := fun s => da.Valid s.1 ∧ db.Valid s.2
  initial_valid := ⟨da.initial_valid, db.initial_valid⟩
  ready := by intro s h; simp only [Machine.serial, db.ready _ h.2, da.ready _ h.1]
  preserved := by
    intro i s h hr hd
    exact ⟨da.preserved _ _ h.1 hr (by simpa only [Machine.leftInput, hd] using db.ready _ h.2),
      db.preserved _ _ h.2 hr hd⟩
  empty_offer := db.empty_offer
  empty_fixed := by
    simp only [Machine.serial, Machine.leftInput, Machine.rightInput,
      db.ready _ db.initial_valid, da.empty_offer, da.empty_fixed, db.empty_fixed]
  clears := by
    intro s h
    rw [flush_add]
    have hfst : (flush (a.serial b) na s).1 = sa :=
      (flush_serial_first da db na s h).trans (da.clears s.1 h.1)
    have hvalid : db.Valid (flush (a.serial b) na s).2 := by
      have preserve : ∀ n s, db.Valid s.2 → db.Valid (flush (a.serial b) n s).2 := by
        intro n
        induction n with
        | zero => intro s hs; exact hs
        | succ n ih => intro s hs; exact ih _ (db.preserved _ _ hs rfl rfl)
      exact preserve na s h.2
    have he : flush (a.serial b) na s = (sa, (flush (a.serial b) na s).2) := Prod.ext hfst rfl
    calc
      flush (a.serial b) nb (flush (a.serial b) na s) =
          flush (a.serial b) nb (sa, (flush (a.serial b) na s).2) := congrArg (flush (a.serial b) nb) he
      _ = (sa, flush b nb (flush (a.serial b) na s).2) := flush_serial_empty da db nb _ hvalid
      _ = (sa, sb) := by rw [db.clears _ hvalid]

def Drain.rebound {m : Machine α β S} (d : Drain m initial na) (h : na = nb) : Drain m initial nb :=
  { d with clears := fun s hs => by rw [← h]; exact d.clears s hs }

def drainPipeline (m : Map wi wo) : (extra : Nat) →
    Drain (Design.pipeline m extra).flatten.machine (Design.pipeline m extra).flatten.initial (extra + 1)
  | 0 => drainElastic m.function
  | n + 1 => ((drainElastic m.function).serial (drainPipeline (Map.identity wo) n)).rebound (by omega)

/-- Once input stops and output remains ready, every reachable state drains in
at most D+L edges. This is a conditional progress guarantee, not fairness. -/
def drainDesign (m : Map wi wo) (depth extra : Nat) (hd : 0 < depth) :
    Drain (Design.buffered m depth hd extra).flatten.machine
      (Design.buffered m depth hd extra).flatten.initial (depth + (extra + 1)) :=
  (drainQueue depth hd).serial (drainPipeline m extra)

theorem drainPipeline_valid (m : Map wi wo) (extra : Nat)
    (s : (Design.pipeline m extra).flatten.State) :
    (drainPipeline m extra).Valid s ↔ (Design.pipeline m extra).flatten.contract.Valid s := by
  induction extra generalizing wi with
  | zero => rfl
  | succ n ih => exact and_congr Iff.rfl (ih (Map.identity wo) s.2)

theorem design_drains (m : Map wi wo) (depth extra : Nat) (hd : 0 < depth)
    (s : (Design.buffered m depth hd extra).flatten.State)
    (h : (Design.buffered m depth hd extra).flatten.contract.Valid s) :
    flush (Design.buffered m depth hd extra).flatten.machine (depth + (extra + 1)) s =
      (Design.buffered m depth hd extra).flatten.initial :=
  (drainDesign m depth extra hd).clears s ⟨h.1, (drainPipeline_valid m extra s.2).mpr h.2⟩

end Pinwheel.Hardware.Stream
