import Pinwheel.Hardware.Buffered.GenericDispatch

/-! Cached checked successors and same-edge terminal capture select the actual
branch endpoint. Endpoint coordinates are encoded source layout facts. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program
set_option maxRecDepth 4096

private theorem packed_branch_fields (sample : BitVec 4) (yes no : BitVec 24) :
    let full : BitVec 56 := (0 : BitVec 2) ++ no ++ yes ++ sample ++ (2 : BitVec 2)
    let cached := full.extractLsb' 0 54
    cached.extractLsb' 0 2 = 2 ∧ cached.extractLsb' 2 4 = sample ∧
      cached.extractLsb' 6 24 = yes ∧ cached.extractLsb' 30 24 = no := by
  simp (disch := decide) only [BitVec.extractLsb'_extractLsb'_of_le,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le,
    BitVec.extractLsb'_eq_self, Nat.reduceSub, and_self]

theorem Running.branch_fields {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminal : Option (Engine.Reactive.Capture 15)) (sample : Fin 16)
    (yes no : Program.Buffered.Target)
    (operation : instruction.operation = .checked action guard terminal (.branch sample yes no)) :
    Reactive.finish.eval i r = 2 ∧ Reactive.branchSample.eval i r = BitVec.ofNat 4 sample.val ∧
      (r .cachedBranch).extractLsb' 6 24 = GenericLayout.target layout.map yes ∧
      (r .cachedBranch).extractLsb' 30 24 = GenericLayout.target layout.map no := by
  have cached : r .cachedBranch =
      (GenericLayout.finish layout.map (.branch sample yes no)).extractLsb' 0 54 := by
    simpa only [GenericLayout.instructionFinish, operation] using h.caches.branch
  simpa only [Reactive.finish, Reactive.branchSample, Expr.eval, cached, GenericLayout.finish]
    using packed_branch_fields (BitVec.ofNat 4 sample.val)
      (GenericLayout.target layout.map yes) (GenericLayout.target layout.map no)
  done

theorem Running.branch_endpoint {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminal : Option (Engine.Reactive.Capture 15)) (sample : Fin 16)
    (yes no : Program.Buffered.Target)
    (operation : instruction.operation = .checked action guard terminal (.branch sample yes no))
    (terminalEdge : Reactive.terminalEdge.eval i r = 1) :
    Reactive.endpoint.eval i r = GenericLayout.target layout.map
      (if (Engine.Reactive.capture s.core.samples terminal s.samplerSecond)[sample.val] then yes else no) := by
  have fields := h.branch_fields i action guard terminal sample yes no operation
  have cache : r .cachedTerminal = GenericEncoding.capture terminal := by
    simpa only [GenericEncoding.instruction, operation] using h.caches.terminal
  have bit : Reactive.branchBit.eval i r =
      BitVec.ofBool (Engine.Reactive.capture s.core.samples terminal s.samplerSecond)[sample.val] := by
    simpa only [← h.second] using GenericPhase.terminal_branch_matches i r s.core.samples
      terminal sample cache fields.2.1 h.common.scratch terminalEdge
  cases observed : (Engine.Reactive.capture s.core.samples terminal s.samplerSecond)[sample.val]
  all_goals simp [Reactive.endpoint, Expr.eval, fields.1, fields.2.2.1, fields.2.2.2, bit, observed]
  all_goals done

end Pinwheel.Hardware.Buffered.Refinement
