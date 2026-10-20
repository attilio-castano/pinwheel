import Pinwheel.Hardware.Buffered.GenericDispatchJump

namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

private theorem extend_pc (pc : Program.Buffered.PC) :
    (0 : BitVec 1) ++ BitVec.ofNat 10 pc.val = BitVec.ofNat 11 pc.val := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append]
  simp
  exact (Nat.mod_eq_of_lt (by have := pc.isLt; omega)).symm
  done

theorem absolute_from_endpoint (i : Values Reactive.Input) (r : Values Reactive.Register)
    (pc : Program.Buffered.PC) (q : GenericLayout.Coordinates)
    (terminal : Reactive.terminalEdge.eval i r = 1)
    (finish : Reactive.finish.eval i r ≠ 0#2)
    (endpoint : Reactive.endpoint.eval i r = GenericLayout.endpoint pc q) :
    Reactive.absoluteDispatch.eval i r = 1 := by
  have low : (Reactive.endpoint.eval i r).extractLsb' 0 1 = 0 := by
    simpa only [endpoint] using (GenericLayout.endpoint_fields pc q).2.2.2.2
  simp [Reactive.absoluteDispatch, Reactive.both, Expr.eval, terminal, finish, low]
  done

theorem absolute_coordinates (i : Values Reactive.Input) (r : Values Reactive.Register)
    (pc : Program.Buffered.PC) (q : GenericLayout.Coordinates)
    (notStarting : Reactive.starting.eval i r = 0)
    (absolute : Reactive.absoluteDispatch.eval i r = 1)
    (endpoint : Reactive.endpoint.eval i r = GenericLayout.endpoint pc q) :
    Reactive.entryPC.eval i r = q.row ∧
    Reactive.entryVirtual.eval i r = BitVec.ofNat 11 pc.val ∧
    Reactive.entryOuter.eval i r = q.outer ∧ Reactive.entryInner.eval i r = q.inner := by
  have restore := Reactive.absolute_endpoint_restores_location i r absolute
  have fields := GenericLayout.endpoint_fields pc q
  refine ⟨?_, ?_, ?_, ?_⟩
  case refine_1 => simpa only [endpoint, fields.2.1] using restore.1
  case refine_3 => simpa only [endpoint, fields.2.2.1] using restore.2.1
  case refine_4 => simpa only [endpoint, fields.2.2.2.1] using restore.2.2
  case refine_2 =>
    simpa only [Reactive.entryVirtual, Expr.eval, notStarting, absolute, endpoint,
      fields.1, show (0 : BitVec 1) ≠ 1 from by decide, ↓reduceIte] using extend_pc pc

theorem next_notAbsolute (i : Values Reactive.Input) (r : Values Reactive.Register)
    (endpoint : Reactive.endpoint.eval i r = 1) : Reactive.absoluteDispatch.eval i r = 0 := by
  simp [Reactive.absoluteDispatch, Reactive.both, Expr.eval, endpoint]

theorem Running.sequential_notAbsolute {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc) (i : Values Reactive.Input)
    (sequential : GenericLayout.instructionFinish layout.map instruction = 0) :
    Reactive.absoluteDispatch.eval i r = 0 := by
  have cached : r .cachedBranch = 0 := by simpa [sequential] using h.caches.branch
  simp [Reactive.absoluteDispatch, Reactive.finish, Reactive.both, Expr.eval, cached]
  done

end Pinwheel.Hardware.Buffered.Refinement
