import Pinwheel.Hardware.Processor.Examples.ReadySPIProofs
import Pinwheel.Hardware.Processor.ReadyHost

/-! Fetch, issue and retire the ROM's actual GPIO sample at PC 100. The four
clock edges can see four unrelated public pad values. Only the value at
accepted MMIO service contributes to the architectural result. -/
namespace Pinwheel.Hardware.Processor.ReadySPI

open RV32I.Semantics
open Pinwheel.Hardware.StreamingReady

private def sampleContext (s : State) : Context :=
  ⟨s, 0x0000a603, .load .word 12 1 0, by decide +kernel⟩

private def sampleRequest (s : State) : CoreModel.DataRequest :=
  .load (sampleContext s) .word 12 (effectiveAddress s 1 0)

private theorem sample_fetch (requests : Array (BitVec 8)) (frames collect : Nat) :
    SystemModel.fetchReply layout (rom requests frames collect) 100 = .instruction 0x0000a603 := by
  rfl

theorem sample_retirement (requests : Array (BitVec 8)) (frames collect : Nat)
    (arch : State) (ram : Memory.ByteAdapterModel.State 2) (mmio : MmioModel.State)
    (prior : Option CoreModel.FetchReply) (p0 p1 p2 p3 : TinyWiring.Pad → BitVec 8)
    (pc : arch.pc = 100) (base : read arch.registers 1 = 0x40000000) :
    let s : SystemModel.State 2 := ⟨⟨arch,.fetchRequest⟩,ram,mmio,prior⟩
    let image := rom requests frames collect
    let clock := fun pads => SystemModel.step layout image (ReadyHost.cpuInput false pads)
    (clock p3 (clock p2 (clock p1 (clock p0 s)))).core =
      ⟨writeNext arch 12 (ReadyHost.reply p3), .fetchRequest⟩ := by
  dsimp only
  let s : SystemModel.State 2 := ⟨⟨arch,.fetchRequest⟩,ram,mmio,prior⟩
  let image := rom requests frames collect
  let clk := fun pads => SystemModel.step layout image (ReadyHost.cpuInput false pads)
  let a := clk p0 s
  let b := clk p1 a
  let c := clk p2 b
  have aligned : CoreModel.aligned arch := by simp [CoreModel.aligned, pc]
  have fetched : a.fetch = some (.instruction 0x0000a603) := by
    change (if CoreModel.aligned arch then some (SystemModel.fetchReply layout image arch.pc) else none) = _
    rw [if_pos aligned, pc, sample_fetch]
  have first : a.core = ⟨arch,.fetchResponse⟩ := by
    change CoreModel.step (SystemModel.coreInput layout image (ReadyHost.cpuInput false p0) s) ⟨arch,.fetchRequest⟩ = _
    simp [CoreModel.step, CoreModel.tick, ReadyHost.cpuInput, SystemModel.coreInput, aligned]
  have second : b.core = ⟨arch,.execute 0x0000a603⟩ := by
    change CoreModel.step _ a.core = _
    rw [first]
    simp [CoreModel.step, CoreModel.tick, ReadyHost.cpuInput, SystemModel.coreInput, fetched]
  have issued : c.core = ⟨arch,.dataRequest (sampleRequest arch)⟩ := by
    change CoreModel.step _ b.core = _
    rw [second]
    rfl
  have pending : SystemModel.pendingPlan layout image c = some (.mmio ⟨.gpio,0,false,0⟩) := by
    simp only [SystemModel.pendingPlan, issued]
    change some (SystemModel.plan layout image (.load (effectiveAddress arch 1 0) .word false)) = _
    have address : effectiveAddress arch 1 0 = 0x40000000 := by
      change read arch.registers 1 + 0 = _
      exact (BitVec.add_zero _).trans base
    rw [address]
    rfl
  have served := ReadyHost.read_reply layout image c p3 pending
  change CoreModel.step (SystemModel.coreInput layout image (ReadyHost.cpuInput false p3) c) c.core = _
  rw [issued]
  have active : (SystemModel.coreInput layout image (ReadyHost.cpuInput false p3) c).reset = false := rfl
  simp only [CoreModel.step, CoreModel.tick, active, Bool.false_eq_true, ↓reduceIte, served]
  rfl

end Pinwheel.Hardware.Processor.ReadySPI
