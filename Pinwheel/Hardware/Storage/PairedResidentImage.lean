import Pinwheel.Hardware.Storage.PairedImage

/-! A separately named resident source language for the existing paired ABI.
Canonical E64 remains unchanged. SHIFT consumes a START-owned byte; KEEP can
capture while preserving selected output levels. The certificate binds source
operands, successors and exact upload bytes. Controller timing and package
delivery are separate obligations. -/
namespace Pinwheel.Hardware.Storage.PairedResidentImage
open Pinwheel.Hardware
open PairedImage (Word PC Node Image select row index terminal upload)

structure Source where
  words : Execution.Words
  idle : Engine.Reactive.Pins
  last : Fin 256
  deriving DecidableEq, Repr

def canonical (word : BitVec 64) : Bool :=
  let f := Execution.unpack word
  if f.kind = 5 then
    decide (word = Execution.pack {kind := 5, levels := f.levels, enabled := f.enabled, duration := f.duration, entry := f.entry} ∧
      f.entry.toNat < 8 ∧ (f.entry.extractLsb' 0 2).toNat < 3)
  else if f.kind = 6 then
    decide (word = Execution.pack {kind := 6, levels := f.levels, enabled := f.enabled, duration := f.duration, entry := f.entry, terminal := f.terminal} ∧ (f.entry[0] = true ∨ f.entry = 0) ∧
      f.terminal.toNat < 8)
  else (Execution.decode word).isSome

abbrev Valid (p : Source) : Prop := ∀ pc : Fin 256, canonical p.words[pc.val] = true

def fields (p : Source) (pc : PC) : Execution.Fields := Execution.unpack p.words[pc.toNat]

def successor (p : Source) (pc : PC) (choice : Bool) : Node :=
  let f := fields p pc
  let target := if f.kind = 2 ∧ f.finish = 2 then
      (if choice then f.yes else f.no).toNat
    else if f.kind = 2 ∧ f.finish = 1 then f.yes.toNat
    else pc.toNat + 1
  if target ≤ p.last.val then some (BitVec.ofNat 8 target) else none

abbrev Matches (p : Source) (image : Image) (node : Node) (word : Word) : Prop :=
  match node with
  | none => word = 7
  | some pc => pc.toNat ≤ p.last.val ∧
      if (fields p pc).kind = 4 then word = 4 else
        terminal word = false ∧ row word = pc ∧
        word.extractLsb' 30 2 = 0 ∧
        word.extractLsb' 0 17 =
          ((fields p pc).duration ++ (fields p pc).enabled ++
            (fields p pc).levels ++ (fields p pc).kind) ∧
        image.parameters[(index word).toNat] = PairedImage.parameter (fields p pc)

instance (p : Source) (image : Image) (node : Node) (word : Word) :
    Decidable (Matches p image node word) :=
  match node with
  | none => inferInstance
  | some _ => inferInstance

abbrev Corresponds (p : Source) (image : Image) : Prop :=
  Matches p image (some 0) image.boot ∧
  image.idle = p.idle.enabled ++ p.idle.levels ∧
  ∀ pc : PC, ∀ choice : Bool,
    if pc.toNat ≤ p.last.val then
      Matches p image (successor p pc choice) (select image.rows[pc.toNat] choice)
    else select image.rows[pc.toNat] choice = 4

def check (p : Source) (image : Image) (words : List (BitVec 64)) : Bool :=
  decide (Valid p ∧ words = upload image ∧ Corresponds p image)

def referenceStep (p : Source) (node : Node) (choice : Bool) : Node :=
  match node with
  | none => none
  | some pc => if (fields p pc).kind = 4 then some pc else successor p pc choice

def run (image : Image) (word : Word) : List Bool → Word
  | [] => word
  | choice :: rest => run image (PairedImage.step image word choice) rest

def referenceRun (p : Source) (node : Node) : List Bool → Node
  | [] => node
  | choice :: rest => referenceRun p (referenceStep p node choice) rest

theorem check_sound (p : Source) (image : Image) (words : List (BitVec 64))
    (h : check p image words = true) : Valid p ∧ words = upload image ∧ Corresponds p image := by
  exact of_decide_eq_true h
  done

theorem step_matches (p : Source) (image : Image) (node : Node)
    (word : Word) (choice : Bool) (certificate : Corresponds p image)
    (h : Matches p image node word) :
    Matches p image (referenceStep p node choice) (PairedImage.step image word choice) := by
  cases node with
  | none => simp_all [Matches, referenceStep, PairedImage.step, terminal]
  | some pc =>
    by_cases halt : (fields p pc).kind = 4
    · simp_all [Matches, referenceStep, PairedImage.step, terminal]
      done
    · simp only [Matches, halt, if_false] at h
      simpa only [referenceStep, halt, if_false, PairedImage.step, h.2.1,
        Bool.false_eq_true, h.2.2.1, if_pos h.1] using certificate.2.2 pc choice
      done

theorem run_matches (p : Source) (image : Image) (node : Node)
    (word : Word) (choices : List Bool) (certificate : Corresponds p image)
    (h : Matches p image node word) :
    Matches p image (referenceRun p node choices) (run image word choices) := by
  induction choices generalizing node word with
  | nil => exact h
  | cons choice rest ih =>
    exact ih _ _ (step_matches p image node word choice certificate h)
    done

theorem checked_trace (p : Source) (image : Image) (words : List (BitVec 64))
    (h : check p image words = true) (choices : List Bool) :
    Matches p image (referenceRun p (some 0) choices) (run image image.boot choices) := by
  exact run_matches p image (some 0) image.boot choices (check_sound p image words h).2.2
    (check_sound p image words h).2.2.1
  done


end Pinwheel.Hardware.Storage.PairedResidentImage
