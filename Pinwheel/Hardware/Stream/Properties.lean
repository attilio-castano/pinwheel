import Pinwheel.Hardware.Stream.Normalize

namespace Pinwheel.Hardware.Stream

set_option backward.isDefEq.respectTransparency false

def Bounded (c : Certified wi wo) (capacity : Nat) : Prop :=
  ∀ s, c.contract.Valid s → (c.contract.pending s).length ≤ capacity

theorem bounded_fifo (w d : Nat) (hd : 0 < d) : Bounded (fifoCertified w d hd) d :=
  fun _ h => h

theorem bounded_elastic (m : Map wi wo) : Bounded (Elastic.certified m) 1 := by
  intro s _
  cases s <;> simp [Elastic.certified, elasticContract]

theorem bounded_serial (a : Certified wi wm) (b : Certified wm wo)
    (ha : Bounded a na) (hb : Bounded b nb) : Bounded (a.serial b) (na + nb) := by
  intro s h
  have h₁ := ha s.1 h.1
  have h₂ := hb s.2 h.2
  simp only [Certified.serial, Contract.serial, List.length_append, List.length_map]
  omega

theorem bounded_parallel (a : Certified wi wa) (b : Certified wi wb)
    (ha : Bounded a na) (hb : Bounded b nb) : Bounded (a.parallel b) (min na nb) := by
  intro s h
  have h₁ := ha s.1 h.1
  have h₂ := hb s.2 h.2.1
  simp only [Certified.parallel, Parallel.contract, List.length_zipWith]
  omega

theorem bounded_pipeline (m : Map wi wo) (extra : Nat) :
    Bounded (Design.pipeline m extra).flatten (extra + 1) := by
  induction extra generalizing wi with
  | zero => exact bounded_elastic m
  | succ n ih =>
    simpa only [Design.pipeline, Design.flatten, Nat.add_comm 1 (n + 1)] using
      bounded_serial _ _ (bounded_elastic m) (ih (Map.identity wo))

theorem bounded_design (m : Map wi wo) (depth extra : Nat) (hd : 0 < depth) :
    Bounded (Design.buffered m depth hd extra).flatten (depth + (extra + 1)) :=
  bounded_serial _ _ (bounded_fifo wi depth hd) (bounded_pipeline m extra)

def Stable (m : Machine α β S) : Prop := ∀ i s,
  i.reset = false → i.ready = false → (m.offer s).isSome = true → m.offer (m.step i s) = m.offer s

theorem stable_elastic (f : α → β) : Stable (elastic f) := elastic_stalled f

theorem stable_serial (a : Machine α β S) (b : Machine β γ T) (h : Stable b) : Stable (a.serial b) :=
  fun i s hr hd hv => h (a.rightInput i s.1) s.2 hr hd hv

theorem stable_parallel (a : Machine α β S) (b : Machine α γ T) (f : β → γ → δ)
    (ha : Stable a) (hb : Stable b) : Stable (Parallel.machine a b f) := by
  intro i s hr hd hv
  have hl : (a.offer s.1).isSome = true := by
    cases he : a.offer s.1 <;> simp_all [Parallel.machine, joinOffer]
  have hj : (b.offer s.2).isSome = true := by
    cases he : a.offer s.1 <;> cases hf : b.offer s.2 <;> simp_all [Parallel.machine, joinOffer]
  have ea := ha (Parallel.leftInput a b i s) s.1 hr
    (by simp [Parallel.leftInput, Parallel.leftReady, hd]) hl
  have eb := hb (Parallel.rightInput a b i s) s.2 hr
    (by simp [Parallel.rightInput, Parallel.leftReady, hd]) hj
  simp only [Parallel.machine, ea, eb]

theorem stable_pipeline (m : Map wi wo) (extra : Nat) : Stable (Design.pipeline m extra).flatten.machine := by
  induction extra generalizing wi with
  | zero => exact stable_elastic m.function
  | succ n ih => exact stable_serial _ _ (ih (Map.identity wo))

theorem stable_design (m : Map wi wo) (depth extra : Nat) (hd : 0 < depth) :
    Stable (Design.buffered m depth hd extra).flatten.machine :=
  stable_serial _ _ (stable_pipeline m extra)

end Pinwheel.Hardware.Stream
