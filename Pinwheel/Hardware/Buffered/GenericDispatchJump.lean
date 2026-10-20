import Pinwheel.Hardware.Buffered.GenericDispatchBranch

namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program
set_option maxRecDepth 4096

private theorem packed_jump_fields (endpoint : BitVec 24) :
    let full : BitVec 56 := (0 : BitVec 2) ++ (0 : BitVec 24) ++ endpoint ++
      (0 : BitVec 4) ++ (1 : BitVec 2)
    let cached := full.extractLsb' 0 54
    cached.extractLsb' 0 2 = 1 ∧ cached.extractLsb' 6 24 = endpoint := by
  simp (disch := decide) only [BitVec.extractLsb'_extractLsb'_of_le,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le,
    BitVec.extractLsb'_eq_self, Nat.reduceSub, and_self]

theorem Running.jump_fields {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminal : Option (Engine.Reactive.Capture 15)) (target : Program.Buffered.PC)
    (operation : instruction.operation = .checked action guard terminal (.jump target)) :
    Reactive.finish.eval i r = 1 ∧ (r .cachedBranch).extractLsb' 6 24 =
      GenericLayout.endpoint target (layout.map target) := by
  have cached : r .cachedBranch =
      (GenericLayout.finish layout.map (.jump target)).extractLsb' 0 54 := by
    simpa only [GenericLayout.instructionFinish, operation] using h.caches.branch
  simpa only [Reactive.finish, Expr.eval, cached, GenericLayout.finish]
    using packed_jump_fields (GenericLayout.endpoint target (layout.map target))
  done

theorem Running.jump_endpoint {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminal : Option (Engine.Reactive.Capture 15)) (target : Program.Buffered.PC)
    (operation : instruction.operation = .checked action guard terminal (.jump target)) :
    Reactive.endpoint.eval i r = GenericLayout.endpoint target (layout.map target) := by
  have fields := h.jump_fields i action guard terminal target operation
  simp [Reactive.endpoint, Expr.eval, fields.1, fields.2]
  done

end Pinwheel.Hardware.Buffered.Refinement
