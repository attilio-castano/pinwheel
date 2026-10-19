import Pinwheel.Program.StreamingUART

open Pinwheel.Program.StreamingUART
open Pinwheel.Program.StreamingReady

def q4 : Profile := ⟨0,0⟩
def q12 : Profile := ⟨8,0⟩
def q128 : Profile := ⟨124,0⟩

example : (image q4).words =
    [0x14000000000004,0x4000000000004,0x808,0x44000000000004,0x1008,
     0x800003831,0x808,0x54000000000004,2] := by decide +kernel
example : (image q12).words =
    [0x14000000000004,0x4000000000004,0x4848,0x44000000000004,0x5048,
     0x80000b8b1,0x4848,0x54000000000004,2] := by decide +kernel
example : (image q128).words =
    [0x14000000000004,0x4000000000004,0x3ebe8,0x44000000000004,0x3f3e8,
     0x80007fff1,0x3ebe8,0x54000000000004,2] := by decide +kernel

example (p : Profile) : (image p).program.WellFormed := (image p).wellFormed
example (p : Profile) : (image p).words.length = 9 := image_rows p
example (p : Profile) : 4 ≤ p.Q ∧ p.Q ≤ 128 := ⟨p.Q_ge4,p.Q_le128⟩
example (p : Profile) : 8 ≤ 2*p.Q ∧ 2*p.Q ≤ 256 := by
  have := p.Q_ge4
  have := p.Q_le128
  omega

/-- The one-cycle checks remain bounded. The idle/start waits are unbounded. -/
example (p : Profile) : (checkStart p).limit.budget = 1 ∧ (checkStop p).limit.budget = 1 ∧
    (markGuard p).limit.budget = 0 ∧ (startGuard p).limit.budget = 0 := by exact ⟨rfl,rfl,rfl,rfl⟩

example : wordCanonical (0x800003831 ||| (1 <<< 63)) = false := by decide +kernel
example : ¬ Supported [.stream (cell q4) none,.stream (cell q4) none,.halt] := by decide +kernel

#print axioms supported
#print axioms source_fetch
#print axioms image
