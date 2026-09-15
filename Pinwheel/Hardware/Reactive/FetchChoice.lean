import Pinwheel.Hardware.Reactive.Fetch

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

end Pinwheel.Hardware.Reactive.Fetch
