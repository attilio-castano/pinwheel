import Lean
import Pinwheel.Hardware.Processor.Examples.ByteProgram
import Pinwheel.Hardware.Processor.SystemExportProofs
import Pinwheel.Hardware.Processor.SystemModel

open Lean Elab Command Pinwheel.Hardware Pinwheel.Hardware.Processor

namespace ProcessorSystemCircuitTests

def capture (d : Interface P) (v : Values P) : Array Nat := d.ports.map fun ⟨_,p⟩ => (v p).toNat

open ProcessorSystemFirmware

def circuit := SystemExport.staged layout rom (by decide) (by decide)

def row (i : SystemModel.Input) : Values SystemCircuit.Input := fun p => match p with
  | .at ⟨0,_⟩ => BitVec.ofBool i.reset
  | .at ⟨1,_⟩ => i.gpio
  | .at ⟨2,_⟩ => BitVec.ofBool i.txComplete
  | .at ⟨3,_⟩ => BitVec.ofBool i.rxArrival.isSome
  | .at ⟨4,_⟩ => i.rxArrival.getD 0
  | .at ⟨5,_⟩ => BitVec.ofBool i.framingError
  | .at ⟨k+6,h⟩ => False.elim (by change k+6 < 6 at h; omega)

def faultCode : CoreModel.DataReply → Nat
  | .success _ => 0 | .fault .misaligned => 1 | .fault .accessFault => 2
def payload : CoreModel.DataReply → Nat | .success data => data.toNat | _ => 0
def corePins (i : CoreModel.Input) : Values CoreInterface.Input := fun {b} p =>
  BitVec.ofNat b (match (CoreInterface.inputs.position p).val with
    | 0 => i.reset.toNat | 1 => i.fetchReady.toNat | 2 => i.fetchResponse.isSome.toNat
    | 3 => (i.fetchResponse matches some .accessFault).toNat
    | 4 => match i.fetchResponse with | some (.instruction w) => w.toNat | _ => 0
    | 5 => i.dataService.isSome.toNat
    | 6 => (i.dataService matches some (.atomic _)).toNat
    | 7 => match i.dataService with | some (.atomic r) => faultCode r | _ => 0
    | 8 => match i.dataService with | some (.atomic r) => payload r | _ => 0
    | 9 => i.dataResponse.isSome.toNat
    | 10 => (i.dataResponse.map faultCode).getD 0
    | 11 => (i.dataResponse.map payload).getD 0
    | _ => 0)

def mmioPins (i : MmioModel.Input) : Values MmioInterface.Input := fun {b} p =>
  BitVec.ofNat b (match (MmioInterface.inputs.position p).val with
    | 0 => i.reset.toNat | 1 => i.operation.isSome.toNat
    | 2 => match i.operation with
        | some r => match r.device with | .gpio => 0 | .timer => 1 | .uart => 2
        | _ => 0
    | 3 => ((i.operation.map MmioModel.Request.write).getD false).toNat
    | 4 => ((i.operation.map MmioModel.Request.word).getD 0).toNat
    | 5 => ((i.operation.map MmioModel.Request.data).getD 0).toNat
    | 6 => i.gpioInput.toNat | 7 => i.txComplete.toNat | 8 => i.rxArrival.isSome.toNat
    | 9 => (i.rxArrival.getD 0).toNat | 10 => i.framingError.toNat | _ => 0)

def initial : SystemModel.State 2 := SystemModel.initial (fun a => BitVec.ofNat 32 (0x11223344+a.toNat)) 0x87654321
def rawInitial : Values (SystemCircuit.Register 2) := fun {b} r =>
  let k := ((SystemCircuit.registers 2).position r).val
  BitVec.ofNat b (if 37 ≤ k ∧ k < 41 then 0x11223344+k-37 else if k = 41 then 0x87654321 else 0)

def require (name : String) (actual expected : Nat) : IO Unit := do
  unless actual == expected do throw (IO.userError s!"{name}: expected {expected}, got {actual}")

def checkOutputs (cycle : Nat) (input : SystemModel.Input) (model : SystemModel.State 2)
    (raw : Values (SystemCircuit.Register 2)) : IO Unit := do
  let i : Values SystemCircuit.Input := row input
  let observed := SystemExport.outputSnapshot layout rom (by decide) (by decide) i raw
  let ci : Values CoreInterface.Input := corePins (SystemModel.coreInput layout rom input model)
  let mi : Values MmioInterface.Input := mmioPins (SystemModel.mmioInput layout rom input model)
  for ⟨_,p⟩ in CoreInterface.outputs.ports do
    require s!"edge{cycle}/core/{CoreInterface.outputs.label p}"
      (observed.values (.left p)).toNat (CoreInterface.outputValues ci model.core p).toNat
  for ⟨_,p⟩ in MmioInterface.outputs.ports do
    require s!"edge{cycle}/mmio/{MmioInterface.outputs.label p}"
      (observed.values (.right p)).toNat (MmioInterface.outputValues mi model.mmio p).toNat

def checkState (cycle : Nat) (model : SystemModel.State 2) (raw : Values (SystemCircuit.Register 2)) : IO Unit := do
  require s!"edge{cycle}/pc" (raw (SystemCircuit.core CoreCircuit.pc)).toNat model.core.arch.pc.toNat
  for k in List.finRange 31 do
    require s!"edge{cycle}/x{k+1}" (raw (SystemCircuit.core (CoreCircuit.word k))).toNat
      (model.core.arch.registers k).toNat
  for a in [:4] do
    require s!"edge{cycle}/ram{a}" (raw (SystemCircuit.ram (.left (Memory.CommandFlops.word (BitVec.ofNat 2 a))))).toNat
      (model.ram.memory.contents (BitVec.ofNat 2 a)).toNat
  require "RAM Q" (raw (SystemCircuit.ram (.left Memory.CommandFlops.q))).toNat model.ram.memory.q.toNat
  let mmioState := MmioCircuit.view (fun r => raw (SystemCircuit.mmio r))
  unless mmioState == model.mmio do throw (IO.userError s!"edge{cycle}: device state mismatch")

def boot (directory : Option String := none) : IO Nat := do
  let mut model := initial
  let mut raw : Values (SystemCircuit.Register 2) := rawInitial
  let mut retires : List Nat := []
  let mut writes := 0
  let mut timerRead : Option Nat := none
  let mut frames : Array Json := #[]
  for cycle in [:100] do
    let input : SystemModel.Input := ⟨cycle == 0,0xdecafbad,false,none,false⟩
    checkOutputs cycle input model raw
    let pre := SystemExport.outputSnapshot layout rom (by decide) (by decide) (row input) raw
    let preValues := capture SystemCircuit.outputs pre.values
    let event := (SystemModel.observe layout rom input model).core.event
    match event with
    | some (.retired word _ _) =>
        retires := retires ++ [word.toNat]
        if model.core.arch.pc == 40 then timerRead := some model.mmio.timer.toNat
    | _ => pure ()
    let before := model.ram.memory.contents 0
    let next := SystemModel.step layout rom input model
    if next.ram.memory.contents 0 != before then
      writes := writes+1
      unless event matches some (.retired _ (.data .deferred (.store _ _ _) _) _) do
        throw (IO.userError "RAM write lacks matching deferred store retirement")
    let nextBank := SystemExport.nextSnapshot layout rom (by decide) (by decide) (row input) raw
    raw := nextBank.values
    model := next
    checkState cycle model raw
    checkOutputs cycle input model raw
    let post := SystemExport.outputSnapshot layout rom (by decide) (by decide) (row input) raw
    frames := frames.push (Json.mkObj [("cycle",toJson cycle),
      ("input",toJson (capture SystemCircuit.inputs (row input))),
      ("pre",toJson preValues),("post",toJson (capture SystemCircuit.outputs post.values)),
      ("registers",toJson (capture (SystemCircuit.registers 2) raw))])
    if (CoreModel.terminal model.core).isSome then
      require "single byte-store commit" writes 1
      require "signed byte" (RV32I.Semantics.read model.core.arch.registers 3).toNat 0xffffff80
      require "unsigned byte" (RV32I.Semantics.read model.core.arch.registers 4).toNat 128
      require "GPIO readback" (RV32I.Semantics.read model.core.arch.registers 6).toNat 0xffffff80
      require "untouched RAM lanes" (model.ram.memory.contents 0).toNat 0x11228044
      require "GPIO output" model.mmio.gpioOut.toNat 0xffffff80
      require "pre-edge timer read" (RV32I.Semantics.read model.core.arch.registers 8).toNat (timerRead.getD (2^32))
      unless retires == (program.toList.take (program.size-1)).map BitVec.toNat do
        throw (IO.userError "Firmware retirement sequence mismatch")
      let some fault := CoreModel.terminal model.core | throw (IO.userError "Missing terminal trap")
      unless fault.cause == .instruction .breakpoint && fault.pc == 48 && fault.word == some 0x00100073 do
        throw (IO.userError "Firmware terminal trap mismatch")
      let reset : SystemModel.Input := {reset := true}
      let next := SystemModel.step layout rom reset model
      require "warm reset preserves RAM" (next.ram.memory.contents 0).toNat 0x11228044
      if let some out := directory then
        IO.FS.createDirAll out
        IO.FS.writeFile (out++"/expected.json") ((toJson frames).pretty++"\n")
        IO.FS.writeFile (out++"/startup.json") ((toJson (capture (SystemCircuit.registers 2) rawInitial)).pretty++"\n")
        IO.FS.writeFile (out++"/ledger.json") ((Json.mkObj [("edges",toJson (cycle+1)),
          ("retired_words",toJson retires),("ram_commits",toJson writes),
          ("timer_read",toJson timerRead),("terminal_pc",toJson fault.pc.toNat),
          ("ram_word0",toJson (model.ram.memory.contents 0).toNat),
          ("gpio_output",toJson model.mmio.gpioOut.toNat)]).pretty++"\n")
      return cycle+1
  throw (IO.userError "Firmware did not reach its completion trap")

end ProcessorSystemCircuitTests

def main (args : List String) : IO Unit := do
  unless args.length ≤ 1 do throw (IO.userError "Usage: processor_system_replay [output-directory]")
  let cycles ← ProcessorSystemCircuitTests.boot args.head?
  IO.println s!"System circuit: firmware reached breakpoint after {cycles} edges with exact retirement, byte RAM and GPIO/timer effects."
