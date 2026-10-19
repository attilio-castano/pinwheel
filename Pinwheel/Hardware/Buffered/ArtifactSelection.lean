import Pinwheel.Hardware.Execution.Memory

/-! Value-level balanced selection laws for artifact graph reconstruction.
These are independent of a particular controller, image or initialized state. -/
namespace Pinwheel.Hardware.Buffered.ArtifactSelection

/-- The emitter's balanced mux order, consuming the least-significant bit first. -/
def select (bits : Nat) (words : BitVec bits → α) (address : BitVec bits) : α :=
  match bits with
  | 0 => words 0
  | n + 1 => if address.extractLsb' 0 1 = 1 then
      select n (fun k => words (k ++ (1#1))) (address.extractLsb' 1 n)
    else select n (fun k => words (k ++ (0#1))) (address.extractLsb' 1 n)

private theorem bit_cases (b : BitVec 1) : b = 0 ∨ b = 1 := by
  bv_omega

theorem select_correct (bits : Nat) (words : BitVec bits → α) (address : BitVec bits) :
    select bits words address = words address := by
  induction bits with
  | zero => simp only [select, show address = 0 from Subsingleton.elim _ _]
  | succ n ih =>
    simp only [select, ih]
    have h := BitVec.extractLsb'_append_extractLsb' (x := address) (w := n) (len := 1)
    rcases bit_cases (address.extractLsb' 0 1) with hb | hb <;> simp_all
    done

/-- Any pure value transformation commutes with the entire selection tree. -/
theorem select_map (f : α → β) (bits : Nat) (words : BitVec bits → α)
    (address : BitVec bits) :
    select bits (fun k => f (words k)) address = f (select bits words address) := by
  rw [select_correct, select_correct]
  done

/-- Digital dictionary expansion of one compact row. -/
def expand (dictionary : BitVec 4 → BitVec 56) (row : BitVec 92) : BitVec 144 :=
  dictionary (row.extractLsb' 88 4) ++ row.extractLsb' 0 88

/-- Selecting compact rows before dictionary expansion preserves the value. -/
theorem expand_select (dictionary : BitVec 4 → BitVec 56)
    (bits : Nat) (rows : BitVec bits → BitVec 92) (address : BitVec bits) :
    select bits (fun k => expand dictionary (rows k)) address =
      expand dictionary (select bits rows address) := by
  exact select_map (expand dictionary) bits rows address
  done

end Pinwheel.Hardware.Buffered.ArtifactSelection
