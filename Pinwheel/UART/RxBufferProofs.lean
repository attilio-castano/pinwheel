import Pinwheel.UART.RxBuffer

namespace Pinwheel.UART.Rx.Buffer

theorem accepted_cons (r : Receipt) (rs : List Receipt) :
    accepted (r :: rs) = r.accepted.toList ++ accepted rs := rfl

theorem retired_cons (r : Receipt) (rs : List Receipt) :
    retired (r :: rs) = (r.delivered.toList ++ r.flushed.toList) ++ retired rs := rfl

theorem step_order (s : State) (command : Command) :
    s.pending.toList ++ (step s command).receipt.accepted.toList =
      (step s command).receipt.delivered.toList ++ (step s command).receipt.flushed.toList ++
        (step s command).state.pending.toList := by
  cases command with
  | reset => simp [step]
  | cycle arrival take clear => cases take <;> cases hp : s.pending <;> simp [step, hp]

/-- Every accepted occurrence is retired in order or remains in the one slot. -/
theorem run_order (s : State) (commands : List Command) :
    s.pending.toList ++ accepted (run s commands).receipts =
      retired (run s commands).receipts ++ (run s commands).state.pending.toList := by
  induction commands generalizing s with
  | nil => simp [run, accepted, retired]
  | cons command rest ih =>
    simp only [run, accepted_cons, retired_cons, ← List.append_assoc]
    rw [step_order, List.append_assoc, List.append_assoc, ih]
    simp only [List.append_assoc]

theorem step_partition (s : State) (command : Command) :
    command.arrival.toList = (step s command).receipt.accepted.toList ++
      (step s command).receipt.dropped.toList := by
  cases command with
  | reset => rfl
  | cycle arrival take clear => cases take <;> cases hp : s.pending <;> simp [step, Command.arrival, hp]

/-- Count occurrences, including equal-valued bytes, across every consumer/reset history. -/
theorem run_accounting (s : State) (commands : List Command) :
    s.pending.toList.length + (arrivals commands).length =
      (delivered (run s commands).receipts).length +
      (dropped (run s commands).receipts).length +
      (flushed (run s commands).receipts).length +
      (run s commands).state.pending.toList.length := by
  induction commands generalizing s with
  | nil => simp [run, arrivals, delivered, dropped, flushed]
  | cons command rest ih =>
    have order := congrArg List.length (step_order s command)
    have partition := congrArg List.length (step_partition s command)
    have tail := ih (step s command).state
    simp only [run, arrivals, delivered, dropped, flushed, List.flatMap_cons,
      List.length_append] at order partition tail ⊢
    omega

theorem run_append_state (s : State) (a b : List Command) :
    (run s (a ++ b)).state = (run (run s a).state b).state := by
  induction a generalizing s with
  | nil => rfl
  | cons command rest ih => exact ih (step s command).state

/-- With no drops or reset flushes, every arrival is delivered in order or remains pending. -/
theorem run_lossless (s : State) (commands : List Command)
    (clean : ∀ r ∈ (run s commands).receipts, r.dropped = none ∧ r.flushed = none) :
    s.pending.toList ++ arrivals commands = delivered (run s commands).receipts ++
      (run s commands).state.pending.toList := by
  induction commands generalizing s with
  | nil => simp [run, arrivals, delivered]
  | cons command rest ih =>
    have head := clean (step s command).receipt (by simp [run])
    have tail := ih (step s command).state (fun r hr => clean r (by simp [run, hr]))
    have admitted : command.arrival.toList = (step s command).receipt.accepted.toList := by
      simpa [head.1] using step_partition s command
    change s.pending.toList ++ (command.arrival.toList ++ arrivals rest) =
      ((step s command).receipt.delivered.toList ++ delivered (run (step s command).state rest).receipts) ++ _
    rw [admitted, ← List.append_assoc, step_order, head.2]
    simpa only [Option.toList_none, List.append_nil, List.append_assoc, run] using
      congrArg ((step s command).receipt.delivered.toList ++ ·) tail

theorem take_and_arrive (old new : Outcome) (overrun clear : Bool) :
    step ⟨some old, overrun⟩ (.cycle (some new) true clear) =
      ⟨⟨some new, overrun && !clear⟩, {accepted := some new, delivered := some old}⟩ := rfl

theorem full_drops_newest (old new : Outcome) (overrun clear : Bool) :
    step ⟨some old, overrun⟩ (.cycle (some new) false clear) =
      ⟨⟨some old, true⟩, {dropped := some new}⟩ := by
  simp [step]

theorem empty_no_bypass (new : Outcome) (overrun clear : Bool) :
    step ⟨none, overrun⟩ (.cycle (some new) true clear) =
      ⟨⟨some new, overrun && !clear⟩, {accepted := some new}⟩ := rfl

theorem reset_flushes (s : State) : step s .reset = ⟨{}, {flushed := s.pending}⟩ := rfl

end Pinwheel.UART.Rx.Buffer
