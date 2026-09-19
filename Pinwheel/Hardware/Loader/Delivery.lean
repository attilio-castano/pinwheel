import Pinwheel.Hardware.Loader.Contract

/-! What a consumed input history tells the loader machine: a list of commands,
each on one edge with its word, among edges that tell it nothing. This is the
interface between a transport (the serial loader delivers such histories) and
the loader's own theorems (what such a history does). -/
namespace Pinwheel.Hardware.Loader.Machine

/-- An edge on which the machine is told nothing. -/
def Quiet (m : Inputs) : Prop := m.init = false ∧ m.reset = false ∧ m.command = 0

/-- An edge that carries one command and its word. Command 7 is the `reset` input. -/
def Carries (m : Inputs) (c : BitVec 3) (d : BitVec 64) : Prop :=
  m.init = false ∧ m.reset = (c == 7) ∧ m.command = (if c != 7 then c else 0) ∧ m.data = d

/-- The history is the given commands, in order, among quiet edges. -/
inductive Delivers : List Inputs → List (BitVec 3 × BitVec 64) → Prop where
  | nil : Delivers [] []
  | quiet {m h cs} : Quiet m → Delivers h cs → Delivers (m :: h) cs
  | command {m h c d cs} : Carries m c d → Delivers h cs → Delivers (m :: h) ((c, d) :: cs)

theorem Delivers.append {h₁ h₂ : List Inputs} {c₁ c₂ : List (BitVec 3 × BitVec 64)}
    (a : Delivers h₁ c₁) (b : Delivers h₂ c₂) : Delivers (h₁ ++ h₂) (c₁ ++ c₂) := by
  induction a with
  | nil => exact b
  | quiet hq _ ih => exact .quiet hq ih
  | command hc _ ih => exact .command hc ih

end Pinwheel.Hardware.Loader.Machine
