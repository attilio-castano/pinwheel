import Pinwheel.Hardware.Switch.Model

namespace Pinwheel.Hardware.Switch

def winners (depth : Nat) (o : Fin m) : State n m α → List (Input n m α) → List (Fin (n + 1))
  | _, [] => []
  | s, i :: rest => (grant i s o).toList ++ winners depth o (step depth i s) rest

def opportunities (depth : Nat) (o : Fin m) : State n m α → List (Input n m α) → Nat
  | _, [] => 0
  | s, i :: rest => (if canLoad i s o then 1 else 0) + opportunities depth o (step depth i s) rest

/-- The target remains an eligible FIFO head, and reset does not intervene.
Output backpressure is allowed; blocked cycles do not count as opportunities. -/
def persistent (depth : Nat) (o : Fin m) (target : Fin (n + 1)) : State n m α → List (Input n m α) → Prop
  | _, [] => True
  | s, i :: rest => i.reset = false ∧ request s o target = true ∧ persistent depth o target (step depth i s) rest

theorem cursor_after (depth : Nat) (i : Input n m α) (s : State n m α) (o : Fin m)
    (hr : i.reset = false) :
    (step depth i s).cursor o = ((grant i s o).map Arbitration.RoundRobin.next).getD (s.cursor o) := by
  simp [step, hr]

theorem served_within_distance (depth : Nat) (o : Fin m) (target : Fin (n + 1))
    (s : State n m α) (inputs : List (Input n m α))
    (h : persistent depth o target s inputs)
    (enough : Arbitration.RoundRobin.distance (s.cursor o) target < opportunities depth o s inputs) :
    target ∈ winners depth o s inputs := by
  induction inputs generalizing s with
  | nil => simp [opportunities] at enough
  | cons i rest ih =>
    rcases h with ⟨hr, ht, hp⟩
    cases hg : grant i s o with
    | none =>
      have blocked : canLoad i s o = false := by
        cases hc : canLoad i s o with
        | false => rfl
        | true =>
          have hn : Arbitration.RoundRobin.grant (s.cursor o) (request s o) = none := by
            simpa [grant, hr, hc] using hg
          have hf := (Arbitration.RoundRobin.grant_none_iff _ _).mp hn target
          simp [ht] at hf
      simp only [winners, hg, Option.toList_none, List.nil_append]
      apply ih _ hp
      simpa [opportunities, blocked, cursor_after depth i s o hr, hg] using enough
    | some winner =>
      simp only [winners, hg, Option.toList_some, List.singleton_append, List.mem_cons]
      by_cases he : winner = target
      · exact Or.inl he.symm
      · right
        apply ih _ hp
        have active : canLoad i s o = true := by
          cases hc : canLoad i s o <;> simp_all [grant]
        have hg' : Arbitration.RoundRobin.grant (s.cursor o) (request s o) = some winner := by
          simpa [grant, hr, active] using hg
        have decreases := Arbitration.RoundRobin.grant_progress hg' ht he
        simp only [opportunities, active, if_true] at enough
        rw [cursor_after depth i s o hr, hg]
        simp only [Option.map_some, Option.getD_some]
        omega

/-- A persistent head request is granted within N available output-slot refill
opportunities in the actual buffered switch model, for N inputs. -/
theorem bounded_fairness (depth : Nat) (o : Fin m) (target : Fin (n + 1))
    (s : State n m α) (inputs : List (Input n m α))
    (h : persistent depth o target s inputs)
    (enough : n + 1 ≤ opportunities depth o s inputs) : target ∈ winners depth o s inputs :=
  served_within_distance depth o target s inputs h
    (Nat.lt_of_lt_of_le (Arbitration.RoundRobin.distance_lt _ _) enough)

end Pinwheel.Hardware.Switch
