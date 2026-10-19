import Pinwheel.Hardware.Buffered.GenericDispatchAt
import Pinwheel.Hardware.Buffered.GenericEntryStep
import Pinwheel.Hardware.Buffered.GenericInvalidEntry
import Pinwheel.Hardware.Buffered.GenericHeldStop
import Pinwheel.Hardware.Buffered.GenericStopped
import Pinwheel.Hardware.Buffered.GenericNormalize
import Pinwheel.Hardware.Buffered.GenericDispatchSource
import Pinwheel.Hardware.Buffered.SpiStart

/-! Universal clock-prefix preservation for the buffered source interpreter
and every instruction in the packed Reactive circuit. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

private theorem Running.entry_related {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (target : Program.Buffered.PC) (slots : Vector Bool 16)
    (atEntry : EntryAt layout.map i r target) (within : target.val < p.code.span)
    (scratch : GenericPhase.Scratch (Reactive.exitScratch.eval i r) slots) :
    Related p layout payload (Reactive.circuit.step i r)
      (GenericEntry.entered p {s with samplerFirst := (i .rawInputs), samplerSecond := s.samplerFirst}
        target slots s.samplerSecond) := by
  rcases layout.sourceRecord target within with ⟨next, fetch, _⟩
  simpa only [h.second] using valid_entry
    (h.common.samplers (i .rawInputs) s.samplerFirst) i quiet target next slots
    atEntry within fetch h.slot h.retained rfl h.first scratch

private theorem Running.invalid_related {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (slots : Vector Bool 16) {capture : Bool}
    (flags : GenericPhase.Dispatching i r capture)
    (illegal : Reactive.legalEntry.eval i r = 0)
    (scratch : GenericPhase.Scratch (Reactive.exitScratch.eval i r) slots) :
    Related p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.terminal p capacity
        {{s with samplerFirst := (i .rawInputs), samplerSecond := s.samplerFirst}
          with core := {s.core with samples := slots}} .fault) := by
  exact Or.inr ⟨e, .fault, invalid_entry
    (h.common.samplers (i .rawInputs) s.samplerFirst) i quiet h.slot slots scratch
    flags.entering illegal flags.timeout⟩

private theorem Running.next_dispatch {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (slots : Vector Bool 16) {capture : Bool}
    (flags : GenericPhase.Dispatching i r capture)
    (notAbsolute : Reactive.absoluteDispatch.eval i r = 0)
    (scratch : GenericPhase.Scratch (Reactive.exitScratch.eval i r) slots)
    (source : Program.Buffered.advance p capacity s (i .rawInputs) =
      GenericInterpreter.dispatchState p
        {s with samplerFirst := (i .rawInputs), samplerSecond := s.samplerFirst}
        (Program.Buffered.sequentialTarget p pc) slots s.samplerSecond) :
    Related p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) := by
  rw [source]
  by_cases within : pc.val + 1 < p.code.span
  case pos =>
    have next : pc.val < p.last.val := by change pc.val < p.code.span - 1; omega
    have coordinates := h.sequential_coordinates i quiet notAbsolute within
    simpa only [Program.Buffered.sequentialTarget, next, ↓reduceDIte,
      GenericInterpreter.dispatchState] using
      h.entry_related i quiet ⟨pc.val + 1, by have := p.fits; omega⟩ slots
        ⟨flags.entering, coordinates.1, coordinates.2⟩ within scratch
  case neg =>
    have notNext : ¬ pc.val < p.last.val := by change ¬ pc.val < p.code.span - 1; omega
    have virtual := sequential_virtual i r pc (SpiCircuit.quiet_controls i r quiet).2.2.1
      notAbsolute h.virtualPC
    have outside : (r .virtualSpan).toNat ≤ (Reactive.entryVirtual.eval i r).toNat := by
      rw [h.common.span, virtual]
      simp only [BitVec.toNat_ofNat]
      have := p.fits
      have := pc.isLt
      omega
    simpa only [Program.Buffered.sequentialTarget, notNext, ↓reduceDIte,
      GenericInterpreter.dispatchState] using h.invalid_related i quiet slots flags
        (illegal_virtual i r outside) scratch

private theorem Running.absolute_dispatch {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (slots : Vector Bool 16) {capture : Bool}
    (flags : GenericPhase.Dispatching i r capture) (target : Program.Buffered.PC)
    (atEntry : EntryAt layout.map i r target)
    (scratch : GenericPhase.Scratch (Reactive.exitScratch.eval i r) slots)
    (source : Program.Buffered.advance p capacity s (i .rawInputs) =
      GenericInterpreter.dispatchState p
        {s with samplerFirst := (i .rawInputs), samplerSecond := s.samplerFirst}
        ((some target).filter (fun pc => decide (pc.val ≤ p.last.val))) slots s.samplerSecond) :
    Related p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) := by
  rw [source]
  by_cases within : target.val < p.code.span
  case pos =>
    have accepted : target.val ≤ p.last.val := by change target.val ≤ p.code.span - 1; omega
    simpa only [Option.filter, accepted, decide_true, ↓reduceIte,
      GenericInterpreter.dispatchState] using h.entry_related i quiet target slots atEntry within scratch
  case neg =>
    have rejected : ¬ target.val ≤ p.last.val := by
      change ¬ target.val ≤ p.code.span - 1
      have := h.within
      omega
    have outside : (r .virtualSpan).toNat ≤ (Reactive.entryVirtual.eval i r).toNat := by
      rw [h.common.span, atEntry.virtualPC]
      simp only [BitVec.toNat_ofNat]
      have := p.fits
      have := target.isLt
      omega
    simpa only [Option.filter, rejected, decide_false, Bool.false_eq_true, ↓reduceIte,
      GenericInterpreter.dispatchState] using h.invalid_related i quiet slots flags
        (illegal_virtual i r outside) scratch

private theorem Running.active_sequential {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (remaining : Fin 256)
    (control : s.core.control = .active pc remaining) :
    GenericLayout.instructionFinish layout.map instruction = 0 := by
  have state : Control r instruction pc (.active pc remaining) := control ▸ h.control
  have kind := state.2.2.2
  cases operation : instruction.operation
  all_goals simp [GenericEncoding.instruction, GenericEncoding.action, operation] at kind
  all_goals simp [GenericLayout.instructionFinish, operation]

private theorem Running.active_step {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (remaining : Fin 256)
    (control : s.core.control = .active pc remaining) :
    Related p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) := by
  by_cases positive : 0 < remaining.val
  case pos => exact Or.inl ⟨e, instruction, pc, h.active_countdown remaining control positive i quiet⟩
  case neg =>
    have zero : remaining = 0 := Fin.ext (by omega)
    subst remaining
    have flags := h.active_dispatching i quiet control
    exact h.next_dispatch i quiet s.core.samples flags
      (h.sequential_notAbsolute i (h.active_sequential 0 control))
      (h.common.exitScratch i (by simpa only [BitVec.ofBool_false] using flags.terminal))
      (GenericInterpreter.active_dispatch p s pc h.owned control (i .rawInputs))

private theorem Running.wait_step {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (remaining : Fin 256) (wait : Engine.Reactive.Wait)
    (control : s.core.control = .waiting pc remaining)
    (operation : instruction.operation = .wait wait) :
    Related p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) := by
  cases ready : wait.condition.ready s.samplerSecond
  case true =>
    have flags := h.wait_dispatching i quiet remaining wait control operation ready
    exact h.next_dispatch i quiet s.core.samples flags
      (h.sequential_notAbsolute i (by simp [GenericLayout.instructionFinish, operation]))
      (h.common.exitScratch i (by simpa only [BitVec.ofBool_false] using flags.terminal))
      (GenericInterpreter.wait_dispatch p s pc remaining instruction wait
        h.owned control h.fetch operation ready (i .rawInputs))
  case false =>
    by_cases positive : 0 < remaining.val
    case pos => exact Or.inl ⟨e, instruction, pc,
      h.wait_countdown remaining wait control operation ready positive i quiet⟩
    case neg =>
      have zero : remaining = 0 := Fin.ext (by omega)
      subst remaining
      exact Or.inr ⟨e, .timeout, h.wait_timeout wait control operation ready i quiet⟩

private theorem Running.qualify_step {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (remaining waitLeft : Fin 256) (qualify : Engine.Reactive.Qualify)
    (control : s.core.control = .qualifying pc remaining waitLeft)
    (operation : instruction.operation = .qualify qualify) :
    Related p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) := by
  cases ready : qualify.condition.ready s.samplerSecond
  case true =>
    by_cases positive : 0 < remaining.val
    case pos => exact Or.inl ⟨e, instruction, pc,
      h.qualify_progress remaining waitLeft qualify control operation ready positive i quiet⟩
    case neg =>
      have zero : remaining = 0 := Fin.ext (by omega)
      subst remaining
      have flags := h.qualify_dispatching i quiet waitLeft qualify control operation ready
      exact h.next_dispatch i quiet s.core.samples flags
        (h.sequential_notAbsolute i (by simp [GenericLayout.instructionFinish, operation]))
        (h.common.exitScratch i (by simpa only [BitVec.ofBool_false] using flags.terminal))
        (GenericInterpreter.qualify_dispatch p s pc waitLeft instruction qualify
          h.owned control h.fetch operation ready (i .rawInputs))
  case false =>
    by_cases positive : 0 < waitLeft.val
    case pos => exact Or.inl ⟨e, instruction, pc,
      h.qualify_blocked remaining waitLeft qualify control operation ready positive i quiet⟩
    case neg =>
      have zero : waitLeft = 0 := Fin.ext (by omega)
      subst waitLeft
      exact Or.inr ⟨e, .timeout, h.qualify_timeout remaining qualify control operation ready i quiet⟩

private theorem next_target (p : Program.Buffered.Program) (pc : Program.Buffered.PC) :
    (Program.Buffered.Target.next.eval pc).filter (fun target => decide (target.val ≤ p.last.val)) =
      Program.Buffered.sequentialTarget p pc := by
  by_cases next : pc.val < p.last.val
  case pos =>
    have bound : pc.val + 1 < 1024 := by have := p.last.isLt; omega
    have accepted : pc.val + 1 ≤ p.last.val := by omega
    simp [Program.Buffered.Target.eval, Program.Buffered.sequentialTarget, next,
      bound, Option.filter, accepted]
  case neg =>
    have rejected : ¬ pc.val + 1 ≤ p.last.val := by omega
    by_cases bound : pc.val + 1 < 1024
    all_goals simp [Program.Buffered.Target.eval, Program.Buffered.sequentialTarget,
      next, bound, Option.filter, rejected]

private theorem finish_sequential (p : Program.Buffered.Program) (pc : Program.Buffered.PC)
    (slots : Vector Bool 16) :
    Program.Buffered.finishTarget p pc .sequential slots = Program.Buffered.sequentialTarget p pc := by
  by_cases next : pc.val < p.last.val
  case pos =>
    have accepted : pc.val + 1 ≤ p.last.val := by omega
    simp [Program.Buffered.finishTarget, Program.Buffered.sequentialTarget, next,
      Option.filter, accepted]
  case neg => simp [Program.Buffered.finishTarget, Program.Buffered.sequentialTarget, next]

private theorem Running.checked_dispatch_step {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminal : Option (Engine.Reactive.Capture 15)) (finish : Program.Buffered.Finish)
    (normalized : Engine.Reactive.Finish 1023 15)
    (control : s.core.control = .checked pc 0)
    (operation : instruction.operation = .checked action guard terminal finish)
    (normalization : finish.eval pc = some normalized)
    (ready : guard.ready s.samplerSecond = true) :
    Related p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) := by
  have flags := h.checked_dispatching i quiet action guard terminal finish control operation ready
  have terminalEdge : Reactive.terminalEdge.eval i r = 1 := by
    simpa only [BitVec.ofBool_true] using flags.terminal
  have scratch := h.checked_exitScratch i action guard terminal finish operation terminalEdge
  have source := GenericInterpreter.checked_dispatch p s pc instruction action guard terminal finish
    normalized h.owned control h.fetch operation normalization ready (i .rawInputs)
  cases finish
  case sequential =>
    exact h.next_dispatch i quiet _ flags
      (h.sequential_notAbsolute i (by simp [GenericLayout.instructionFinish, operation, GenericLayout.finish]))
      scratch (by simpa only [finish_sequential] using source)
  case jump target =>
    have location := h.jump_entryAt i quiet action guard terminal target control operation ready
    exact h.absolute_dispatch i quiet _ flags target location.2 scratch
      (by simpa only [Program.Buffered.finishTarget] using source)
  case branch sample yes no =>
    cases selected : (if (Engine.Reactive.capture s.core.samples terminal s.samplerSecond)[sample.val]
      then yes else no)
    case absolute target =>
      have location := h.branch_absolute_entryAt i quiet action guard terminal sample yes no target
        control operation ready selected
      exact h.absolute_dispatch i quiet _ flags target location.2 scratch
        (by simpa only [Program.Buffered.finishTarget, selected, Program.Buffered.Target.eval] using source)
    case next =>
      have location := h.branch_next_virtual i quiet action guard terminal sample yes no operation
        terminalEdge selected
      exact h.next_dispatch i quiet _ flags location.1 scratch
        (by simpa only [Program.Buffered.finishTarget, selected, next_target] using source)

private theorem Running.checked_step {p : Program.Buffered.Program}
    {layout : GenericCertificate.Layout p} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) (remaining : Fin 256)
    (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminal : Option (Engine.Reactive.Capture 15)) (finish : Program.Buffered.Finish)
    (control : s.core.control = .checked pc remaining)
    (operation : instruction.operation = .checked action guard terminal finish) :
    Related p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) := by
  cases ready : guard.ready s.samplerSecond
  case false => exact Or.inr ⟨e, .fault,
    h.checked_fault remaining action guard terminal finish control operation ready i quiet⟩
  case true =>
    have defined := GenericNormalize.checked_finish_isSome pc layout.map instruction action guard terminal finish
      operation (sourceNormalizes layout pc h.within instruction h.fetch)
    cases normalization : finish.eval pc
    case none => simp [normalization] at defined
    case some normalized =>
      by_cases positive : 0 < remaining.val
      case pos => exact Or.inl ⟨e, instruction, pc,
        h.checked_countdown remaining action guard terminal finish normalized control operation
          normalization ready positive i quiet⟩
      case neg =>
        have zero : remaining = 0 := Fin.ext (by omega)
        subst remaining
        exact h.checked_dispatch_step i quiet action guard terminal finish normalized control operation
          normalization ready

theorem Running.step {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (quiet : SpiCircuit.Quiet i) :
    Related p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) := by
  cases sourceControl : s.core.control
  case active current remaining =>
    have state : Control r instruction pc (.active current remaining) := sourceControl ▸ h.control
    have same : current = pc := state.1
    subst current
    exact h.active_step i quiet remaining sourceControl
  case waiting current remaining =>
    have state : Control r instruction pc (.waiting current remaining) := sourceControl ▸ h.control
    have same : current = pc := state.1
    subst current
    have kind := state.2.2.2
    cases operation : instruction.operation
    all_goals simp [GenericEncoding.instruction, GenericEncoding.action, GenericEncoding.empty, operation] at kind
    case wait wait => exact h.wait_step i quiet remaining wait sourceControl operation
  case checked current remaining =>
    have state : Control r instruction pc (.checked current remaining) := sourceControl ▸ h.control
    have same : current = pc := state.1
    subst current
    have kind := state.2.2.2
    cases operation : instruction.operation
    all_goals simp [GenericEncoding.instruction, GenericEncoding.action, GenericEncoding.empty, operation] at kind
    case checked action guard terminal finish =>
      exact h.checked_step i quiet remaining action guard terminal finish sourceControl operation
  case qualifying current remaining waitLeft =>
    have state : Control r instruction pc (.qualifying current remaining waitLeft) := sourceControl ▸ h.control
    have same : current = pc := state.1
    subst current
    have kind := state.2.2.2.2
    cases operation : instruction.operation
    all_goals simp [GenericEncoding.instruction, GenericEncoding.action, GenericEncoding.empty, operation] at kind
    case qualify qualify => exact h.qualify_step i quiet remaining waitLeft qualify sourceControl operation
  case stopped reason =>
    have state : Control r instruction pc (.stopped reason) := sourceControl ▸ h.control
    exact False.elim state

theorem related_step {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    (h : Related p layout payload r s) (i : Values Reactive.Input) (quiet : SpiCircuit.Quiet i) :
    Related p layout payload (Reactive.circuit.step i r)
      (Program.Buffered.advance p capacity s (i .rawInputs)) := by
  rcases h with ⟨e, instruction, pc, running⟩ | ⟨e, outcome, stopped⟩
  case inl => exact running.step i quiet
  case inr => exact Or.inr ⟨e, outcome, stopped.step i quiet⟩

theorem related_run {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    (initial : Related p layout payload r s) (incoming : Nat → BitVec 2) (edges : Nat) :
    Related p layout payload (SpiStart.packedRun r incoming edges)
      (Program.Buffered.run p capacity s incoming edges) := by
  induction edges
  case zero => exact initial
  case succ n ih =>
    rw [SpiStart.packedRun_succ, Program.Buffered.run]
    exact related_step ih (SpiStart.quietInput (incoming n)) ⟨rfl, rfl⟩

end Pinwheel.Hardware.Buffered.Refinement
