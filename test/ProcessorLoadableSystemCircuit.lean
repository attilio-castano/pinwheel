import Lean
import Pinwheel.Hardware.Processor.Examples.ByteProgram
import Pinwheel.Hardware.Processor.LoadableSystemStagedProofs
import Pinwheel.Hardware.Processor.SystemModelEncoding

open Lean Pinwheel.Hardware Pinwheel.Hardware.Processor

namespace ProcessorLoadableSystemTests

open ProcessorSystemFirmware

def capture (d : Interface P) (v : Values P) : Array Nat :=
  d.ports.map fun ⟨_,p⟩ => (v p).toNat

def pins (row : Array Nat) : Values (LoadableSystem.Input 2) := fun {b} p =>
  BitVec.ofNat b row[((LoadableSystem.inputs 2).position p).val]!

def startup : Array Nat := (SystemCircuit.registers 2).ports.mapIdx fun k ⟨b,_⟩ =>
  (0x9abcdef0+k*0x10203)%2^b

def rawStartup : Values (SystemCircuit.Register 2) := fun {b} p =>
  BitVec.ofNat b startup[((SystemCircuit.registers 2).position p).val]!

def initial : SystemModel.State 2 := SystemModel.initial
  (fun a => BitVec.ofNat 32 startup[37+a.toNat]!) (BitVec.ofNat 32 startup[41]!)

def stimulus (cycle : Nat) : Array Nat :=
  let base := #[0,0xdecafbad,0,0,0,0,1,0,0,0]
  if cycle == 0 || cycle == 7 then ((base.set! 0 1).set! 7 1).set! 9 0xdeadbeef
  else if 2 ≤ cycle && cycle ≤ 5 then
    ((base.set! 7 1).set! 8 (cycle-2)).set! 9 (0x11223344+cycle-2)
  else if cycle ≥ 8 then base.set! 6 0
  else base

def systemInput (row : Array Nat) : SystemModel.Input :=
  ⟨row[0]! == 1 || row[6]! == 1,BitVec.ofNat 32 row[1]!,false,none,false⟩

def modelStep (row : Array Nat) (state : SystemModel.State 2) : SystemModel.State 2 :=
  let next := SystemModel.step layout rom (systemInput row) state
  if row[6]! == 1 && row[0]! == 0 && row[7]! == 1 then
    let contents := fun (a : BitVec 2) =>
      if a.toNat == row[8]! then BitVec.ofNat 32 row[9]! else next.ram.memory.contents a
    {next with ram := {next.ram with memory := {next.ram.memory with contents := contents}}}
  else next

def require (name : String) (actual expected : Nat) : IO Unit := do
  unless actual == expected do throw (IO.userError s!"{name}: expected {expected}, got {actual}")

def checkOutputs (cycle : Nat) (row : Array Nat) (model : SystemModel.State 2)
    (observed : Values LoadableSystem.Output) : IO Unit := do
  let input := systemInput row
  let ci : Values CoreInterface.Input := SystemModelEncoding.corePins (SystemModel.coreInput layout rom input model)
  let mi : Values MmioInterface.Input := SystemModelEncoding.mmioPins (SystemModel.mmioInput layout rom input model)
  for ⟨_,p⟩ in CoreInterface.outputs.ports do
    require s!"edge{cycle}/core/{CoreInterface.outputs.label p}"
      (observed (.left (.left p))).toNat (CoreInterface.outputValues ci model.core p).toNat
  for ⟨_,p⟩ in MmioInterface.outputs.ports do
    require s!"edge{cycle}/mmio/{MmioInterface.outputs.label p}"
      (observed (.left (.right p))).toNat (MmioInterface.outputValues mi model.mmio p).toNat
  require "loader ready" (observed (.right (.at ⟨0,by decide⟩))).toNat
    (row[6]! == 1 && row[0]! == 0).toNat
  require "running" (observed (.right (.at ⟨1,by decide⟩))).toNat
    (row[6]! == 0 && row[0]! == 0).toNat

def checkState (cycle : Nat) (model : SystemModel.State 2)
    (raw : Values (SystemCircuit.Register 2)) : IO Unit := do
  require s!"edge{cycle}/pc" (raw (SystemCircuit.core CoreCircuit.pc)).toNat model.core.arch.pc.toNat
  for k in List.finRange 31 do
    require s!"edge{cycle}/x{k+1}" (raw (SystemCircuit.core (CoreCircuit.word k))).toNat
      (model.core.arch.registers k).toNat
  for a in [:4] do
    require s!"edge{cycle}/ram{a}" (raw (SystemCircuit.ram (.left (Memory.CommandFlops.word (BitVec.ofNat 2 a))))).toNat
      (model.ram.memory.contents (BitVec.ofNat 2 a)).toNat
  require s!"edge{cycle}/ramQ" (raw (SystemCircuit.ram (.left Memory.CommandFlops.q))).toNat model.ram.memory.q.toNat
  unless MmioCircuit.view (fun r => raw (SystemCircuit.mmio r)) == model.mmio do
    throw (IO.userError s!"edge{cycle}: device state mismatch")

def boot (directory : Option String) : IO Nat := do
  let mut model := initial
  let mut raw : Values (SystemCircuit.Register 2) := rawStartup
  let mut frames : Array Json := #[]
  let mut retired : List Nat := []
  let mut stores := 0
  let mut loads := 0
  let mut timerRead : Option Nat := none
  for cycle in [:100] do
    let row := stimulus cycle
    let i : Values (LoadableSystem.Input 2) := pins row
    let pre := LoadableSystem.outputSnapshot layout rom (by decide) (by decide) i raw
    checkOutputs cycle row model pre.values
    let event := (SystemModel.observe layout rom (systemInput row) model).core.event
    match event with
    | some (.retired word _ _) =>
        retired := retired ++ [word.toNat]
        if model.core.arch.pc == 40 then timerRead := some model.mmio.timer.toNat
    | _ => pure ()
    let next := modelStep row model
    if row[6]! == 1 && row[0]! == 0 && row[7]! == 1 then loads := loads+1
    if row[6]! == 0 && next.ram.memory.contents 0 != model.ram.memory.contents 0 then
      stores := stores+1
      unless event matches some (.retired _ (.data .deferred (.store _ _ _) _) _) do
        throw (IO.userError "RAM store lacks same-edge retirement")
    let nextRaw := LoadableSystem.nextSnapshot layout rom (by decide) (by decide) i raw
    raw := nextRaw.values
    model := next
    checkState cycle model raw
    let post := LoadableSystem.outputSnapshot layout rom (by decide) (by decide) i raw
    checkOutputs cycle row model post.values
    frames := frames.push (Json.mkObj [("cycle",toJson cycle),("input",toJson row),
      ("pre",toJson (capture LoadableSystem.outputs pre.values)),
      ("post",toJson (capture LoadableSystem.outputs post.values)),
      ("registers",toJson (capture (LoadableSystem.registers 2) raw))])
    if cycle == 7 then
      require "complete loaded image" loads 4
      for a in [:4] do require "loaded word after reset" (model.ram.memory.contents (BitVec.ofNat 2 a)).toNat (0x11223344+a)
      unless (model.core.phase matches .fetchRequest) && model.core.arch.pc == 0 &&
          model.fetch.isNone && model.ram.pending.isNone do
        throw (IO.userError "Loader failed to hold processor and providers quiescent")
      for k in List.finRange 31 do require "loader clears registers" (model.core.arch.registers k).toNat 0
    if let some fault := CoreModel.terminal model.core then
      require "CPU store count" stores 1
      require "signed byte" (RV32I.Semantics.read model.core.arch.registers 3).toNat 0xffffff80
      require "unsigned byte" (RV32I.Semantics.read model.core.arch.registers 4).toNat 128
      require "GPIO readback" (RV32I.Semantics.read model.core.arch.registers 6).toNat 0xffffff80
      require "RAM byte preservation" (model.ram.memory.contents 0).toNat 0x11228044
      require "GPIO output" model.mmio.gpioOut.toNat 0xffffff80
      require "pre-edge timer read" (RV32I.Semantics.read model.core.arch.registers 8).toNat (timerRead.getD (2^32))
      unless retired == (program.toList.take (program.size-1)).map BitVec.toNat &&
          fault.cause == .instruction .breakpoint && fault.pc == 48 && fault.word == some 0x00100073 do
        throw (IO.userError "Loaded firmware retirement/trap mismatch")
      if let some out := directory then
        IO.FS.createDirAll out
        IO.FS.writeFile (out++"/expected.json") ((toJson frames).pretty++"\n")
        IO.FS.writeFile (out++"/startup.json") ((toJson startup).pretty++"\n")
        IO.FS.writeFile (out++"/ledger.json") ((Json.mkObj [("edges",toJson (cycle+1)),
          ("loader_writes",toJson loads),("external_resets",toJson (2 : Nat)),
          ("retired_words",toJson retired),("ram_commits",toJson stores),
          ("timer_read",toJson timerRead),("terminal_pc",toJson fault.pc.toNat),
          ("ram_word0",toJson (model.ram.memory.contents 0).toNat),
          ("gpio_output",toJson model.mmio.gpioOut.toNat)]).pretty++"\n")
      return cycle+1
  throw (IO.userError "Loaded firmware did not reach its breakpoint")

end ProcessorLoadableSystemTests

def main (args : List String) : IO Unit := do
  unless args.length ≤ 1 do throw (IO.userError "Usage: loadable_system_replay [output-directory]")
  let cycles ← ProcessorLoadableSystemTests.boot args.head?
  IO.println s!"Loadable system: {cycles} edges, 4 full-word loader writes, 2 external resets, exact firmware retirement and RAM/GPIO/timer effects."
