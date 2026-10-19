import Pinwheel.Hardware.Buffered.GenericCertificate
import Pinwheel.Hardware.Buffered.GenericPhaseScratch
import Pinwheel.Hardware.Buffered.SpiRelation

/-! A reusable state representation for every buffered instruction kind.
The independent static layout certificate does not contain this relation. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

abbrev capacity := SpiRefinement.capacity
abbrev Datapath := SpiRefinement.Datapath

structure Common (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (payload : BitVec 32) (r : Values Reactive.Register) (s : Program.Buffered.State)
    (e : Transfer.Execution) : Prop where
  count : r .count = BitVec.ofNat 7 layout.count.val
  span : r .virtualSpan = BitVec.ofNat 11 p.code.span
  idleLevels : r .idleLevels = p.idle.levels
  idleEnabled : r .idleEnabled = p.idle.enabled
  image : ∀ k, r (.word k) = layout.words k
  valid : r .valid = 1
  data : Datapath payload r e
  owner : e.request.identity = s.owner
  pins : s.core.pins = ⟨r .levels, r .enabled⟩
  scratch : GenericPhase.Scratch (r .scratch) s.core.samples

structure Caches (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (r : Values Reactive.Register) (instruction : Program.Buffered.Instruction) : Prop where
  duration : r .cachedDuration = (GenericEncoding.instruction instruction).duration
  budget : r .cachedBudget = (GenericEncoding.instruction instruction).budget
  check : r .cachedCheck = (GenericEncoding.instruction instruction).checkValue ++
    (GenericEncoding.instruction instruction).checkMask
  wait : r .cachedWait = (GenericEncoding.instruction instruction).waitLevel ++
    (GenericEncoding.instruction instruction).waitInput
  terminal : r .cachedTerminal = (GenericEncoding.instruction instruction).terminal
  branch : r .cachedBranch =
    (GenericLayout.instructionFinish layout.map instruction).extractLsb' 0 54

def Control (r : Values Reactive.Register) (instruction : Program.Buffered.Instruction)
    (pc : Program.Buffered.PC) : Engine.Reactive.Control 1023 → Prop
  | .active current remaining => current = pc ∧ r .phase = 1 ∧
    r .remaining = BitVec.ofNat 8 remaining.val ∧
    ((GenericEncoding.instruction instruction).kind = 0 ∨
      (GenericEncoding.instruction instruction).kind = 1 ∨
      (GenericEncoding.instruction instruction).kind = 2)
  | .waiting current remaining => current = pc ∧ r .phase = 2 ∧
    r .remaining = BitVec.ofNat 8 remaining.val ∧
    (GenericEncoding.instruction instruction).kind = 5
  | .checked current remaining => current = pc ∧ r .phase = 3 ∧
    r .remaining = BitVec.ofNat 8 remaining.val ∧
    (GenericEncoding.instruction instruction).kind = 6
  | .qualifying current remaining waitLeft => current = pc ∧ r .phase = 4 ∧
    r .remaining = BitVec.ofNat 8 remaining.val ∧
    r .waitLeft = BitVec.ofNat 8 waitLeft.val ∧
    (GenericEncoding.instruction instruction).kind = 7
  | .stopped _ => False

structure Running (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (payload : BitVec 32) (r : Values Reactive.Register) (s : Program.Buffered.State)
    (e : Transfer.Execution) (instruction : Program.Buffered.Instruction)
    (pc : Program.Buffered.PC) : Prop where
  common : Common p layout payload r s e
  slot : s.buffers.slot = .running e
  within : pc.val < p.code.span
  fetch : p.fetch pc = some instruction
  coordinates : GenericLayout.coordinates r = layout.map pc
  virtualPC : r .virtualPC = BitVec.ofNat 10 pc.val
  currentControl : r .currentControl =
    (layout.words ((layout.map pc).row.setWidth 6)).extractLsb' 64 22
  caches : Caches p layout r instruction
  control : Control r instruction pc s.core.control
  retained : r .retained = 0
  first : s.samplerFirst = r .stage1
  second : s.samplerSecond = r .stage2

def stopReason : Transfer.Outcome → Engine.Reactive.Stop
  | .complete => .completed | .timeout => .timeout | .fault => .fault

def stopPhase : Transfer.Outcome → BitVec 3
  | .complete => 5 | .timeout => 6 | .fault => 7

structure Stopped (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (payload : BitVec 32) (r : Values Reactive.Register) (s : Program.Buffered.State)
    (e : Transfer.Execution) (outcome : Transfer.Outcome) : Prop where
  common : Common p layout payload r s e
  slot : s.buffers.slot = .completed ⟨e, outcome⟩
  control : s.core.control = .stopped (stopReason outcome)
  phase : r .phase = stopPhase outcome
  retained : r .retained = 1
  pc : r .pc = 0
  virtualPC : r .virtualPC = 0
  outer : r .outer = 0
  inner : r .inner = 0
  currentControl : r .currentControl = 0
  remaining : r .remaining = 0
  waitLeft : r .waitLeft = 0
  cachedDuration : r .cachedDuration = 0
  cachedBudget : r .cachedBudget = 0
  cachedCheck : r .cachedCheck = 0
  cachedWait : r .cachedWait = 0
  cachedTerminal : r .cachedTerminal = 0
  cachedBranch : r .cachedBranch = 0

def Related (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p)
    (payload : BitVec 32) (r : Values Reactive.Register) (s : Program.Buffered.State) : Prop :=
  (∃ e instruction pc, Running p layout payload r s e instruction pc) ∨
  (∃ e outcome, Stopped p layout payload r s e outcome)

end Pinwheel.Hardware.Buffered.Refinement
