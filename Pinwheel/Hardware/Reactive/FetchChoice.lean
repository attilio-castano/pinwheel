import Pinwheel.Hardware.Reactive.Fetch
import Pinwheel.Hardware.Reactive.SchedulerProofs

namespace Pinwheel.Hardware.Reactive.Fetch

/-- The terminal capture is visible to this edge's branch decision. -/
def branchBit (r : Request) : Bool :=
  (terminalValues r.context r.core)[(Execution.unpack r.context.current).sample.toNat]

/-- Prepare either address without depending on the current incoming pins.
Both candidates agree on sequential, unconditional-jump, and idle paths. -/
def candidateAddress (r : Request) (takeYes : Bool) : BitVec 8 :=
  let d := Execution.unpack r.context.current
  if runningValue r.core then
    if sequentialValue r.context r.core then r.core.pc - 255
    else if d.finish = 1 then d.yes
    else if takeYes then d.yes else d.no
  else 0

theorem address_choice (r : Request) :
    r.address = if branchBit r then candidateAddress r true else candidateAddress r false := by
  cases h : branchBit r <;> simp_all [Request.address, targetValue, candidateAddress, branchBit]
  done

theorem candidateAddress_input_independent (r : Request) (incoming : BitVec 2) (b : Bool) :
    candidateAddress ⟨{r.context with incoming}, r.core⟩ b = candidateAddress r b := by
  rfl

/-- Read both possibilities, then make the input-dependent selection. This
applies to either complete records or address-map indices; reads have no effects. -/
def readCandidates (r : Request) (read : BitVec 8 → α) : α :=
  if branchBit r then read (candidateAddress r true) else read (candidateAddress r false)

theorem readCandidates_eq (r : Request) (read : BitVec 8 → α) :
    readCandidates r read = read r.address := by
  cases h : branchBit r <;> simp [readCandidates, address_choice, h]
  done

def resolveCandidates (r : Request) (read : Reader) : Inputs :=
  {r.context with successor := readCandidates r read}

theorem resolveCandidates_eq (r : Request) (read : Reader) :
    resolveCandidates r read = resolve r.context r.core read := by
  simp [resolveCandidates, readCandidates_eq, resolve]
  done

def resolveIndexedCandidates (r : Request) (index : BitVec 8 → α)
    (dictionary : α → BitVec 64) : Inputs :=
  {r.context with successor := dictionary (readCandidates r index)}

theorem resolveIndexedCandidates_eq (r : Request) (index : BitVec 8 → α)
    (dictionary : α → BitVec 64) :
    resolveIndexedCandidates r index dictionary =
      resolve r.context r.core (fun address => dictionary (index address)) := by
  simp [resolveIndexedCandidates, readCandidates_eq, resolve]
  done

/-- Structural branch selection retains same-edge terminal capture forwarding. -/
def branchExpr : E 1 :=
  Execution.readTree 4 (fun k => terminalSlots k.toFin) (current .sample)

theorem branchExpr_correct (i : Inputs) (s : State) :
    branchExpr.eval i.values s.values = BitVec.ofBool (branchBit ⟨i, s⟩) := by
  simp [branchExpr, Execution.readTree_correct, terminal_correct, current_correct,
    Execution.value, Execution.fieldValue, branchBit]
  done

def candidateExpr (takeYes : Bool) : E 8 :=
  .mux running
    (.mux sequential (.sub (.reg .pc) (.lit 255))
      (.mux (.equal (current .finish) (.lit 1)) (current .yes)
        (if takeYes then current .yes else current .no)))
    (.lit 0)

theorem candidateExpr_correct (i : Inputs) (s : State) (b : Bool) :
    (candidateExpr b).eval i.values s.values = candidateAddress ⟨i, s⟩ b := by
  cases b <;> simp [candidateExpr, Expr.eval, running_correct, sequential_correct,
    current_correct, Execution.value, Execution.fieldValue, State.values, candidateAddress]
  done

/-- A combinational topology with the input-dependent mux after both reads. -/
def selectionExpr (branch : Expr I R 1) (candidate : Bool → Expr I R 8)
    (read : Expr I R 8 → Expr I R w) : Expr I R w :=
  .mux branch (read (candidate true)) (read (candidate false))

/-- General register/input namespaces let a parent bind the scheduler expressions
and supply actual writable-store reads, rather than only literal programs. -/
theorem selectionExpr_correct (r : Request) (i : Values I) (s : Values R)
    (branch : Expr I R 1) (candidate : Bool → Expr I R 8)
    (read : Expr I R 8 → Expr I R w) (reader : BitVec 8 → BitVec w)
    (hb : branch.eval i s = BitVec.ofBool (branchBit r))
    (ha : ∀ b, (candidate b).eval i s = candidateAddress r b)
    (hr : ∀ address, (read address).eval i s = reader (address.eval i s)) :
    (selectionExpr branch candidate read).eval i s = reader r.address := by
  simp only [selectionExpr, Expr.eval, hb, hr, ha]
  simpa [readCandidates] using readCandidates_eq r reader
  done

end Pinwheel.Hardware.Reactive.Fetch
