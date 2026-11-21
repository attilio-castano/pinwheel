import Std

namespace Pinwheel.Hardware.Arbitration.RoundRobin

/-- Cyclic rank zero names the current cursor. This branch-based definition
avoids division in the executable selector and subsequent hardware lowering. -/
def atRank (cursor rank : Fin (n + 1)) : Fin (n + 1) :=
  if h : cursor.val + rank.val < n + 1 then ⟨cursor.val + rank.val, h⟩
  else ⟨cursor.val + rank.val - (n + 1), by omega⟩

def distance (cursor target : Fin (n + 1)) : Nat :=
  if cursor.val ≤ target.val then target.val - cursor.val else n + 1 - cursor.val + target.val

theorem distance_lt (cursor target : Fin (n + 1)) : distance cursor target < n + 1 := by
  simp only [distance]
  split <;> omega

theorem atRank_distance (cursor target : Fin (n + 1)) :
    atRank cursor ⟨distance cursor target, distance_lt cursor target⟩ = target := by
  apply Fin.ext
  simp only [atRank, distance]
  split <;> split <;> simp_all <;> omega

theorem distance_atRank (cursor rank : Fin (n + 1)) : distance cursor (atRank cursor rank) = rank.val := by
  simp only [atRank, distance]
  split <;> simp only <;> split <;> omega

def order (cursor : Fin (n + 1)) : List (Fin (n + 1)) := List.ofFn (atRank cursor)

def grant (cursor : Fin (n + 1)) (request : Fin (n + 1) → Bool) : Option (Fin (n + 1)) :=
  (order cursor).find? request

/-- Advance only after an actual transfer, never merely after an offer. -/
def next (winner : Fin (n + 1)) : Fin (n + 1) :=
  if h : winner.val + 1 < n + 1 then ⟨winner.val + 1, h⟩ else 0

theorem grant_requested {cursor winner : Fin (n + 1)} {request : Fin (n + 1) → Bool}
    (h : grant cursor request = some winner) : request winner = true := List.find?_some h

theorem mem_order (cursor target : Fin (n + 1)) : target ∈ order cursor :=
  List.mem_ofFn.mpr ⟨⟨distance cursor target, distance_lt cursor target⟩, atRank_distance cursor target⟩

theorem grant_none_iff (cursor : Fin (n + 1)) (request : Fin (n + 1) → Bool) :
    grant cursor request = none ↔ ∀ i, request i = false := by
  simp only [grant, List.find?_eq_none, Bool.not_eq_true]
  exact ⟨fun h i => h i (mem_order cursor i), fun h i _ => h i⟩

/-- No asserted requester is passed over in cyclic priority order. -/
theorem grant_priority {cursor winner target : Fin (n + 1)} {request : Fin (n + 1) → Bool}
    (hg : grant cursor request = some winner) (ht : request target = true) :
    distance cursor winner ≤ distance cursor target := by
  rw [grant, List.find?_eq_getElem?_findIdx] at hg
  rcases List.getElem?_eq_some_iff.mp hg with ⟨hi, he⟩
  have hdist : distance cursor winner = (order cursor).findIdx request := by
    rw [← he]
    simp only [order, List.getElem_ofFn, distance_atRank]
  rw [hdist]
  by_cases h : (order cursor).findIdx request ≤ distance cursor target
  · exact h
  have hn := List.not_of_lt_findIdx (p := request) (xs := order cursor) (by omega : distance cursor target < (order cursor).findIdx request)
  simp only [order, List.getElem_ofFn, atRank_distance, ht, Bool.true_eq_false] at hn

theorem distance_next_lt (cursor winner target : Fin (n + 1))
    (hp : distance cursor winner ≤ distance cursor target) (hn : winner ≠ target) :
    distance (next winner) target < distance cursor target := by
  have hv : winner.val ≠ target.val := fun h => hn (Fin.ext h)
  simp only [distance, next] at hp ⊢
  split at hp <;> split at hp <;> split <;> split <;> dsimp at * <;> omega

/-- Every successful service to another requester strictly decreases a waiting
requester's cyclic distance. No clock-cycle readiness assumption is hidden here. -/
theorem grant_progress {cursor winner target : Fin (n + 1)} {request : Fin (n + 1) → Bool}
    (hg : grant cursor request = some winner) (ht : request target = true) (hn : winner ≠ target) :
    distance (next winner) target < distance cursor target :=
  distance_next_lt cursor winner target (grant_priority hg ht) hn

/-- A trace indexed by eligible service opportunities. Call this only when an
output slot can accept a winner; clock cycles blocked downstream are omitted. -/
def services (cursor : Fin (n + 1)) : List (Fin (n + 1) → Bool) → List (Fin (n + 1))
  | [] => []
  | request :: rest => match grant cursor request with
    | none => services cursor rest
    | some winner => winner :: services (next winner) rest

theorem served_within_distance (cursor target : Fin (n + 1))
    (requests : List (Fin (n + 1) → Bool))
    (persistent : ∀ request ∈ requests, request target = true)
    (enough : distance cursor target < requests.length) : target ∈ services cursor requests := by
  induction requests generalizing cursor with
  | nil => simp at enough
  | cons request rest ih =>
    have ht := persistent request (by simp)
    cases hg : grant cursor request with
    | none =>
      have hn := (grant_none_iff cursor request).mp hg target
      simp [ht] at hn
    | some winner =>
      simp only [services, hg, List.mem_cons]
      by_cases hw : winner = target
      · exact Or.inl hw.symm
      · right
        apply ih
        · intro r hr
          exact persistent r (by simp [hr])
        · have hd := grant_progress hg ht hw
          simp only [List.length_cons] at enough
          omega

/-- A continuously requesting input is granted within N eligible service
opportunities for N inputs, even if all other request sets change each time. -/
theorem bounded_fairness (cursor target : Fin (n + 1))
    (requests : List (Fin (n + 1) → Bool))
    (persistent : ∀ request ∈ requests, request target = true)
    (length : requests.length = n + 1) : target ∈ services cursor requests :=
  served_within_distance cursor target requests persistent (by rw [length]; exact distance_lt cursor target)

end Pinwheel.Hardware.Arbitration.RoundRobin
