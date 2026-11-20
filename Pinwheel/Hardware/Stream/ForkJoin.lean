import Pinwheel.Hardware.Stream.Machine

namespace Pinwheel.Hardware.Stream

set_option backward.isDefEq.respectTransparency false

def forkOffer (offer : Option α) (otherReady : Bool) : Option α := if otherReady then offer else none

def joinOffer (f : α → β → γ) : Option α → Option β → Option γ
  | some a, some b => some (f a b)
  | _, _ => none

/-- Atomic broadcast: each branch accepts precisely the same input occurrences.
Readiness must be independent of the offered input, as enforced by Machine. -/
theorem fork_accepted (i : Input α) (ar br : Bool) (ao : Option β) (bo : Option γ) :
    accepted { i with offered := forkOffer i.offered br } ⟨ar, ao⟩ =
      accepted i ⟨ar && br, bo⟩ := by
  cases i with
  | mk r o d => cases r <;> cases ar <;> cases br <;> rfl

theorem join_emitted (i : Input α) (av : Option β) (bv : Option γ) (f : β → γ → δ) :
    List.zipWith f
      (emitted { i with ready := i.ready && bv.isSome } ⟨false, av⟩)
      (emitted { i with ready := i.ready && av.isSome } ⟨false, bv⟩) =
    emitted i ⟨false, joinOffer f av bv⟩ := by
  cases i with
  | mk r o d => cases r <;> cases d <;> cases av <;> cases bv <;> rfl

theorem join_emitted_lengths (i : Input α) (av : Option β) (bv : Option γ) :
    (emitted { i with ready := i.ready && bv.isSome } ⟨false, av⟩).length =
      (emitted { i with ready := i.ready && av.isSome } ⟨false, bv⟩).length := by
  cases i with
  | mk r o d => cases r <;> cases d <;> cases av <;> cases bv <;> rfl

namespace Parallel

def leftReady (b : Machine β γ T) (r : Bool) (s : T) : Bool := r && (b.offer s).isSome

def leftInput (a : Machine α β S) (b : Machine α γ T) (i : Input α) (s : S × T) : Input α :=
  ⟨i.reset, forkOffer i.offered (b.ready (leftReady a i.ready s.1) s.2), leftReady b i.ready s.2⟩

def rightInput (a : Machine α β S) (b : Machine α γ T) (i : Input α) (s : S × T) : Input α :=
  ⟨i.reset, forkOffer i.offered (a.ready (leftReady b i.ready s.2) s.1), leftReady a i.ready s.1⟩

def machine (a : Machine α β S) (b : Machine α γ T) (f : β → γ → δ) : Machine α δ (S × T) where
  ready := fun r s => a.ready (leftReady b r s.2) s.1 && b.ready (leftReady a r s.1) s.2
  offer := fun s => joinOffer f (a.offer s.1) (b.offer s.2)
  step := fun i s => (a.step (leftInput a b i s) s.1, b.step (rightInput a b i s) s.2)

theorem accepted_left (a : Machine α β S) (b : Machine α γ T) (f : β → γ → δ)
    (i : Input α) (s : S × T) :
    accepted (leftInput a b i s) (a.component.observe (leftInput a b i s) s.1) =
      accepted i ((machine a b f).component.observe i s) := by
  cases hr : i.reset <;> simp [leftInput, Machine.component, machine, accepted, hr, forkOffer]
  cases a.ready (leftReady b i.ready s.2) s.1 <;> cases b.ready (leftReady a i.ready s.1) s.2 <;> rfl

theorem accepted_right (a : Machine α β S) (b : Machine α γ T) (f : β → γ → δ)
    (i : Input α) (s : S × T) :
    accepted (rightInput a b i s) (b.component.observe (rightInput a b i s) s.2) =
      accepted i ((machine a b f).component.observe i s) := by
  cases hr : i.reset <;> simp [rightInput, Machine.component, machine, accepted, hr, forkOffer]
  cases a.ready (leftReady b i.ready s.2) s.1 <;> cases b.ready (leftReady a i.ready s.1) s.2 <;> rfl

theorem emitted_lengths (a : Machine α β S) (b : Machine α γ T) (i : Input α) (s : S × T) :
    (emitted (leftInput a b i s) (a.component.observe (leftInput a b i s) s.1)).length =
      (emitted (rightInput a b i s) (b.component.observe (rightInput a b i s) s.2)).length := by
  cases hr : i.reset <;> cases hd : i.ready <;> cases ha : a.offer s.1 <;> cases hb : b.offer s.2 <;>
    simp [emitted, leftInput, rightInput, leftReady, Machine.component, hr, hd, ha, hb]

theorem emitted_join (a : Machine α β S) (b : Machine α γ T) (f : β → γ → δ)
    (i : Input α) (s : S × T) :
    List.zipWith f (emitted (leftInput a b i s) (a.component.observe (leftInput a b i s) s.1))
      (emitted (rightInput a b i s) (b.component.observe (rightInput a b i s) s.2)) =
      emitted i ((machine a b f).component.observe i s) := by
  cases hr : i.reset <;> cases hd : i.ready <;> cases ha : a.offer s.1 <;> cases hb : b.offer s.2 <;>
    simp [emitted, leftInput, rightInput, leftReady, Machine.component, machine, joinOffer, hr, hd, ha, hb]

theorem zipWith_maps (f : β → γ → δ) (g : α → β) (h : α → γ) (xs : List α) :
    List.zipWith f (xs.map g) (xs.map h) = xs.map (fun x => f (g x) (h x)) := by
  induction xs <;> simp_all

/-- Both branches have the same transaction frontier. The two pending lists
may occupy different physical stages, but are paired in acceptance order. -/
def contract {a : Machine α β S} {b : Machine α γ T} {g : α → β} {h : α → γ}
    (ka : Contract a.component g) (kb : Contract b.component h) (f : β → γ → δ) :
    Contract (machine a b f).component (fun x => f (g x) (h x)) where
  pending := fun s => List.zipWith f (ka.pending s.1) (kb.pending s.2)
  Valid := fun s => ka.Valid s.1 ∧ kb.Valid s.2 ∧ (ka.pending s.1).length = (kb.pending s.2).length
  preserved := by
    intro i s hs
    refine ⟨ka.preserved _ _ hs.1, kb.preserved _ _ hs.2.1, ?_⟩
    cases hr : i.reset with
    | true =>
      have ha := ka.reset_empty (leftInput a b i s) s.1 hr
      have hb := kb.reset_empty (rightInput a b i s) s.2 hr
      change (ka.pending (a.component.step _ _)).length = (kb.pending (b.component.step _ _)).length
      rw [ha, hb]
      rfl
    | false =>
      have ha := congrArg List.length (ka.balance (leftInput a b i s) s.1 hs.1 hr)
      have hb := congrArg List.length (kb.balance (rightInput a b i s) s.2 hs.2.1 hr)
      rw [accepted_left a b f] at ha
      rw [accepted_right a b f] at hb
      have he := emitted_lengths a b i s
      simp only [List.length_append, List.length_map] at ha hb
      change (ka.pending (a.component.step _ _)).length = (kb.pending (b.component.step _ _)).length
      omega
  reset_empty := by
    intro i s hr
    change List.zipWith f (ka.pending (a.component.step _ _)) (kb.pending (b.component.step _ _)) = []
    rw [ka.reset_empty (leftInput a b i s) s.1 hr, kb.reset_empty (rightInput a b i s) s.2 hr]
    rfl
  balance := by
    intro i s hs hr
    have ha := ka.balance (leftInput a b i s) s.1 hs.1 hr
    have hb := kb.balance (rightInput a b i s) s.2 hs.2.1 hr
    rw [accepted_left a b f] at ha
    rw [accepted_right a b f] at hb
    have hz : List.zipWith f
        (ka.pending s.1 ++ (accepted i ((machine a b f).component.observe i s)).map g)
        (kb.pending s.2 ++ (accepted i ((machine a b f).component.observe i s)).map h) =
        List.zipWith f
          (emitted (leftInput a b i s) (a.component.observe (leftInput a b i s) s.1) ++
            ka.pending (a.component.step (leftInput a b i s) s.1))
          (emitted (rightInput a b i s) (b.component.observe (rightInput a b i s) s.2) ++
            kb.pending (b.component.step (rightInput a b i s) s.2)) := by rw [ha, hb]
    simp only [List.zipWith_append hs.2.2, List.zipWith_append (emitted_lengths a b i s),
      zipWith_maps, emitted_join] at hz
    exact hz

end Parallel
end Pinwheel.Hardware.Stream
