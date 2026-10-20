import Pinwheel.Hardware.Buffered.GenericRelation

/-! Cached circuit observations interpreted as the current source instruction's
pre-edge guard or wait condition. -/
namespace Pinwheel.Hardware.Buffered.Refinement
open Pinwheel.Hardware Pinwheel.Program

theorem Running.waitReady {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc)
    (i : Values Reactive.Input) (wait : Engine.Reactive.Wait)
    (operation : instruction.operation = .wait wait) :
    Reactive.waitReady.eval i r = BitVec.ofBool (wait.condition.ready s.samplerSecond) := by
  have cache : r .cachedWait = BitVec.ofBool wait.condition.level ++
      BitVec.ofNat 1 wait.condition.input.val := by
    simpa only [GenericEncoding.instruction, operation] using h.caches.wait
  simpa only [h.second] using GenericPhase.waitReady_matches i r wait.condition cache
  done

theorem Running.checkedReady {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc)
    (i : Values Reactive.Input) (action : Engine.Reactive.Action 15) (guard : Engine.Reactive.Check)
    (terminal : Option (Engine.Reactive.Capture 15)) (finish : Program.Buffered.Finish)
    (operation : instruction.operation = .checked action guard terminal finish) :
    Reactive.checkedReady.eval i r = BitVec.ofBool (guard.ready s.samplerSecond) := by
  have cache : r .cachedCheck = guard.value ++ guard.mask := by
    simpa only [GenericEncoding.instruction, operation] using h.caches.check
  simpa only [h.second] using GenericPhase.checkedReady_matches i r guard cache
  done

theorem Running.qualifyReady {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
    {payload : BitVec 32} {r : Values Reactive.Register} {s : Program.Buffered.State}
    {e : Transfer.Execution} {instruction : Program.Buffered.Instruction} {pc : Program.Buffered.PC}
    (h : Running p layout payload r s e instruction pc)
    (i : Values Reactive.Input) (qualify : Engine.Reactive.Qualify)
    (operation : instruction.operation = .qualify qualify) :
    Reactive.checkedReady.eval i r = BitVec.ofBool (qualify.condition.ready s.samplerSecond) := by
  have cache : r .cachedCheck = qualify.condition.value ++ qualify.condition.mask := by
    simpa only [GenericEncoding.instruction, operation] using h.caches.check
  simpa only [h.second] using GenericPhase.checkedReady_matches i r qualify.condition cache
  done

end Pinwheel.Hardware.Buffered.Refinement
