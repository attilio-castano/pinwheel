import Pinwheel.Hardware.Execution.Images

/-! A checkable connection between a canonical E64 program and the actual paired
upload image. This is an execution-image/successor certificate, not a proof of
the paired loader, complete controller, emitted RTL, or physical SRAM timing.
HALT and fault tokens stop dispatch; their row bits are not executable addresses.
Resident SHIFT/KEEP extensions remain outside this canonical E64 certificate. -/
namespace Pinwheel.Hardware.Storage.PairedImage
open Engine.Reactive

abbrev Word := BitVec 32
abbrev PC := BitVec 8
abbrev Node := Option PC

structure Image where
  parameters : Vector (BitVec 20) 32
  rows : Vector (BitVec 64) 256
  boot : Word
  idle : BitVec 6
  deriving DecidableEq, Repr

def upload (image : Image) : List (BitVec 64) :=
  image.parameters.toList.map (·.zeroExtend 64) ++ image.rows.toList ++
    [image.boot.zeroExtend 64, image.idle.zeroExtend 64]

def select (pair : BitVec 64) (choice : Bool) : Word :=
  if choice then pair.extractLsb' 32 32 else pair.extractLsb' 0 32

def row (word : Word) : PC := word.extractLsb' 22 8
def index (word : Word) : BitVec 5 := word.extractLsb' 17 5
def terminal (word : Word) : Bool :=
  word.extractLsb' 0 3 == 4 || word.extractLsb' 0 3 == 7

def fields (p : Execution.Image) (pc : PC) : Execution.Fields :=
  Execution.fields (p.fetch pc.toFin)

def parameter (f : Execution.Fields) : BitVec 20 :=
  if f.kind = 3 then (0#4) ++ f.check ++ (0#4) ++ f.budget
  else f.sample ++ f.check ++ f.terminal ++ f.entry

def successor (p : Execution.Image) (pc : PC) (choice : Bool) : Node :=
  let f := fields p pc
  let target := if f.kind = 2 ∧ f.finish = 2 then
      (if choice then f.yes else f.no).toNat
    else if f.kind = 2 ∧ f.finish = 1 then f.yes.toNat
    else pc.toNat + 1
  if target ≤ p.last.val then some (BitVec.ofNat 8 target) else none

/-- Every bit of the entering token is checked, including its parameter value.
The parameter slot is chosen by the producer; its contents are independently
compared with the canonical E64 projection. -/
abbrev Matches (p : Execution.Image) (image : Image) (node : Node) (word : Word) : Prop :=
  match node with
  | none => word = 7
  | some pc => pc.toNat ≤ p.last.val ∧
      if (fields p pc).kind = 4 then word = 4 else
        terminal word = false ∧ row word = pc ∧
        word.extractLsb' 30 2 = 0 ∧
        word.extractLsb' 0 17 =
          ((fields p pc).duration ++ (fields p pc).enabled ++
            (fields p pc).levels ++ (fields p pc).kind) ∧
        image.parameters[(index word).toNat] = parameter (fields p pc)

instance (p : Execution.Image) (image : Image) (node : Node) (word : Word) :
    Decidable (Matches p image node word) :=
  match node with
  | none => inferInstance
  | some _ => inferInstance

/-- A finite check against the program, not against compiler-supplied successors. -/
abbrev Corresponds (p : Execution.Image) (image : Image) : Prop :=
  Matches p image (some 0) image.boot ∧
  image.idle = p.idle.enabled ++ p.idle.levels ∧
  ∀ pc : PC, ∀ choice : Bool,
    if pc.toNat ≤ p.last.val then
      Matches p image (successor p pc choice) (select image.rows[pc.toNat] choice)
    else select image.rows[pc.toNat] choice = 4

def check (p : Execution.Image) (image : Image) (words : List (BitVec 64)) : Bool :=
  decide (words = upload image ∧ Corresponds p image)

def referenceStep (p : Execution.Image) (node : Node) (choice : Bool) : Node :=
  match node with
  | none => none
  | some pc => if (fields p pc).kind = 4 then some pc else successor p pc choice

def step (image : Image) (word : Word) (choice : Bool) : Word :=
  if terminal word then word else select image.rows[(row word).toNat] choice

theorem step_matches (p : Execution.Image) (image : Image) (node : Node)
    (word : Word) (choice : Bool) (certificate : Corresponds p image)
    (h : Matches p image node word) :
    Matches p image (referenceStep p node choice) (step image word choice) := by
  cases node with
  | none => simp_all [Matches, referenceStep, step, terminal]
  | some pc =>
    by_cases halt : (fields p pc).kind = 4
    · simp_all [Matches, referenceStep, step, terminal]
    · simp only [Matches, halt, if_false] at h
      simpa only [referenceStep, halt, if_false, step, h.2.1, Bool.false_eq_true,
        h.2.2.1, if_pos h.1] using certificate.2.2 pc choice
      done

def run (image : Image) (word : Word) : List Bool → Word
  | [] => word
  | choice :: rest => run image (step image word choice) rest

def referenceRun (p : Execution.Image) (node : Node) : List Bool → Node
  | [] => node
  | choice :: rest => referenceRun p (referenceStep p node choice) rest

theorem run_matches (p : Execution.Image) (image : Image) (node : Node)
    (word : Word) (choices : List Bool) (certificate : Corresponds p image)
    (h : Matches p image node word) :
    Matches p image (referenceRun p node choices) (run image word choices) := by
  induction choices generalizing node word with
  | nil => exact h
  | cons choice rest ih =>
    exact ih _ _ (step_matches p image node word choice certificate h)
    done

theorem check_sound (p : Execution.Image) (image : Image) (words : List (BitVec 64))
    (h : check p image words = true) : words = upload image ∧ Corresponds p image := by
  exact of_decide_eq_true h
  done

/-- Accepted concrete upload words preserve every finite successor-choice history.
This is a dispatch-image theorem; deriving choices and dispatch edges from the
complete timed controller remains a separate refinement obligation. -/
theorem checked_trace (p : Execution.Image) (image : Image) (words : List (BitVec 64))
    (h : check p image words = true) (choices : List Bool) :
    Matches p image (referenceRun p (some 0) choices) (run image image.boot choices) := by
  exact run_matches p image (some 0) image.boot choices (check_sound p image words h).2
    (check_sound p image words h).2.1
  done

theorem upload_length (image : Image) : (upload image).length = 290 := by
  simp [upload]
  done

end Pinwheel.Hardware.Storage.PairedImage
