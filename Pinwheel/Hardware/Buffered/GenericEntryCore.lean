import Pinwheel.Hardware.Buffered.GenericEntryImage
import Pinwheel.Hardware.Buffered.GenericNormalize
import Pinwheel.Hardware.Buffered.GenericPins
import Pinwheel.Hardware.Buffered.GenericPhaseEntry

/-! Instruction entry in the existing source interpreter, separated from its
buffer effects. These equations retain arbitrary source scratch contents. -/
namespace Pinwheel.Hardware.Buffered.GenericEntry
open Pinwheel.Hardware Pinwheel.Program Pinwheel.Engine.Reactive

def capture (instruction : Program.Buffered.Instruction) : Option (Capture 15) :=
  match instruction.operation with
  | .drive a | .shift _ _ _ a | .keep _ _ a | .checked a _ _ _ => a.capture
  | _ => none

theorem capture_field (instruction : Program.Buffered.Instruction) :
    (GenericEncoding.instruction instruction).capture = GenericEncoding.capture (capture instruction) := by
  cases operation : instruction.operation
  all_goals simp [GenericEncoding.instruction, GenericEncoding.action,
    GenericEncoding.empty, capture, operation, GenericEncoding.capture]

def control (instruction : Program.Buffered.Instruction) (pc : Program.Buffered.PC) :
    Engine.Reactive.Control 1023 :=
  match instruction.operation with
  | .drive a | .shift _ _ _ a | .keep _ _ a => .active pc a.durationMinusOne
  | .wait w => .waiting pc w.budgetMinusOne
  | .checked a _ _ _ => .checked pc a.durationMinusOne
  | .qualify q => .qualifying pc q.durationMinusOne q.budgetMinusOne
  | .halt | .fault _ => .stopped .completed

def core (instruction : Program.Buffered.Instruction) (idle old : Pins)
    (pc : Program.Buffered.PC) (txBit : Bool) (slots : Vector Bool 16) (sampled : Inputs) :
    Engine.Reactive.State 1023 15 :=
  ⟨control instruction pc,
   match instruction.operation with
   | .halt | .fault _ => idle
   | _ => GenericPins.pins instruction old txBit,
   Engine.Reactive.capture slots (capture instruction) sampled⟩

theorem core_not_fault (instruction : Program.Buffered.Instruction) (idle old : Pins)
    (pc : Program.Buffered.PC) (txBit : Bool) (slots : Vector Bool 16) (sampled : Inputs) :
    (core instruction idle old pc txBit slots sampled).control ≠ .stopped .fault := by
  cases operation : instruction.operation
  all_goals simp [core, control, operation]

theorem core_busy (instruction : Program.Buffered.Instruction) (idle old : Pins)
    (pc : Program.Buffered.PC) (txBit : Bool) (slots : Vector Bool 16) (sampled : Inputs)
    (nonterminal : (GenericEncoding.instruction instruction).kind ≠ 3 ∧
      (GenericEncoding.instruction instruction).kind ≠ 4) :
    busy (core instruction idle old pc txBit slots sampled) = true := by
  cases operation : instruction.operation
  all_goals simp [core, control, busy, GenericEncoding.instruction,
    GenericEncoding.action, GenericEncoding.empty, operation] at nonterminal ⊢

theorem core_pins (instruction : Program.Buffered.Instruction) (idle old : Pins)
    (pc : Program.Buffered.PC) (txBit : Bool) (slots : Vector Bool 16) (sampled : Inputs)
    (nonterminal : (GenericEncoding.instruction instruction).kind ≠ 3 ∧
      (GenericEncoding.instruction instruction).kind ≠ 4) :
    (core instruction idle old pc txBit slots sampled).pins =
      GenericPins.pins instruction old txBit := by
  cases operation : instruction.operation
  all_goals simp [core, GenericEncoding.instruction,
    GenericEncoding.action, GenericEncoding.empty, operation] at nonterminal ⊢

theorem source_enter (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (s : Program.Buffered.State) (pc : Program.Buffered.PC)
    (within : pc.val < p.code.span) (instruction : Program.Buffered.Instruction)
    (fetch : p.fetch pc = some instruction) (slots : Vector Bool 16) (sampled : Inputs) :
    Fetch.enter (Program.Buffered.lower p s) pc slots sampled =
      core instruction p.idle s.core.pins pc (Program.Buffered.txBit s) slots sampled := by
  have normal := GenericNormalize.normalize_isSome s pc layout.map instruction
    (Refinement.sourceNormalizes layout pc within instruction fetch)
  cases operation : instruction.operation
  all_goals simp [Fetch.enter, Program.Buffered.lower, fetch, Program.Buffered.normalize,
    operation, core, control, capture, GenericPins.pins, Fetch.stop,
    Engine.Reactive.capture] at normal ⊢
  case checked action guard terminal finish =>
    cases equality : finish.eval pc
    all_goals simp_all
  all_goals done

end Pinwheel.Hardware.Buffered.GenericEntry

namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

theorem Caches.runEntryTick (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (instruction : Program.Buffered.Instruction)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction)
    (branch : Reactive.entryBranch.eval i r = GenericLayout.instructionFinish layout.map instruction) :
    Caches p layout (GenericPhase.runEntryTick i r) instruction := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [GenericPhase.runEntryTick, word] using GenericWord.duration_field instruction
  · simpa only [GenericPhase.runEntryTick, word] using GenericWord.budget_field instruction
  · simpa only [GenericPhase.runEntryTick, word] using GenericWord.check_field instruction
  · simpa only [GenericPhase.runEntryTick, word] using GenericWord.wait_field instruction
  · simpa only [GenericPhase.runEntryTick, Reactive.terminalCapture, Expr.eval, word]
      using GenericWord.terminal_field instruction
  · simp only [GenericPhase.runEntryTick, branch]

theorem entry_control (i : Values Reactive.Input) (r : Values Reactive.Register)
    (instruction : Program.Buffered.Instruction) (pc : Program.Buffered.PC)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction)
    (nonterminal : (GenericEncoding.instruction instruction).kind ≠ 3 ∧
      (GenericEncoding.instruction instruction).kind ≠ 4) :
    Control (GenericPhase.runEntryTick i r) instruction pc (GenericEntry.control instruction pc) := by
  cases operation : instruction.operation
  all_goals simp [Control, GenericEntry.control, GenericPhase.runEntryTick,
    Reactive.entryPhase, Reactive.isKind, Reactive.kind, Expr.eval, word,
    GenericWord.kind_field, GenericWord.duration_field, GenericWord.budget_field,
    GenericEncoding.instruction, GenericEncoding.action, GenericEncoding.empty, operation]
    at nonterminal ⊢
  all_goals done

theorem entry_scratch (i : Values Reactive.Input) (r : Values Reactive.Register)
    (instruction : Program.Buffered.Instruction) (slots : Vector Bool 16)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction)
    (running : Reactive.runEntry.eval i r = 1)
    (notStarting : Reactive.starting.eval i r = 0)
    (scratch : GenericPhase.Scratch (Reactive.exitScratch.eval i r) slots) :
    GenericPhase.Scratch ((GenericPhase.runEntryTick i r) .scratch)
      (Engine.Reactive.capture slots (GenericEntry.capture instruction) (r .stage2)) := by
  have fields : GenericPhase.CaptureFields (Reactive.entryCapture.eval i r)
      (GenericEntry.capture instruction) := by
    simpa only [Reactive.entryCapture, Expr.eval, word, GenericWord.capture_field,
      GenericEntry.capture_field] using GenericPhase.capture_fields (GenericEntry.capture instruction)
  have old : GenericPhase.Scratch
      ((Expr.mux Reactive.starting (.lit 0) Reactive.exitScratch).eval i r) slots := by
    simpa only [Expr.eval, notStarting, show (0 : BitVec 1) ≠ 1 from by decide, ↓reduceIte] using scratch
  simpa only [GenericPhase.runEntryTick, Reactive.entryScratch, Expr.eval, running, ↓reduceIte]
    using GenericPhase.capture_matches Reactive.entryCapture
      (.mux Reactive.starting (.lit 0) Reactive.exitScratch) i r slots
      (GenericEntry.capture instruction) fields old

theorem Common.txBit {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} (h : Common p layout payload r s e)
    (slot : s.buffers.slot = .running e) (available : e.txConsumed < e.request.tx.length)
    (i : Values Reactive.Input) (notStarting : Reactive.starting.eval i r = 0) :
    (Reactive.entryTx.eval i r).getLsbD 0 = Program.Buffered.txBit s := by
  simp only [Reactive.entryTx, Expr.eval, notStarting,
    show (0 : BitVec 1) ≠ 1 from by decide, ↓reduceIte, h.data.shifted,
    Program.Buffered.txBit, slot]
  rw [h.data.tx]
  simp only [SpiPacking.txBits_getElem?, available]
  simp only [BitVec.getLsbD_ushiftRight, Nat.add_zero, ↓reduceIte, Option.getD_some]

theorem entry_pins_source {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} (h : Common p layout payload r s e)
    (slot : s.buffers.slot = .running e) (i : Values Reactive.Input)
    (instruction : Program.Buffered.Instruction)
    (word : Reactive.entryWord.eval i r = GenericEncoding.encode instruction)
    (notStarting : Reactive.starting.eval i r = 0)
    (available : ∀ pin enable invert action,
      instruction.operation = .shift pin enable invert action → e.txConsumed < e.request.tx.length) :
    (⟨Reactive.entryLevels.eval i r, Reactive.entryEnabled.eval i r⟩ : Engine.Reactive.Pins) =
      GenericPins.pins instruction s.core.pins (Program.Buffered.txBit s) := by
  rw [GenericPins.entry_pins instruction i r word, h.pins]
  cases operation : instruction.operation
  all_goals simp only [GenericPins.pins, operation]
  case shift pin enable invert action =>
    rw [h.txBit slot (available pin enable invert action operation) i notStarting]
  all_goals done

end Pinwheel.Hardware.Buffered.Refinement
