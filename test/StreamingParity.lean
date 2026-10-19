import Pinwheel.Hardware.Streaming.CoreEmit
import Pinwheel.Program.StreamingCompile
import Pinwheel.Program.StreamingExecution
import Lean

open Pinwheel.Hardware
namespace StreamingParity

def sourceValues (p : Pinwheel.Program.Streaming.Program) (s : Pinwheel.Program.Streaming.State a) : Values (Pinwheel.Hardware.Streaming.Core.Register a) := fun r =>
  match r with
  | .word k => Pinwheel.Program.Streaming.encode (p.memory[k.toNat]'(by have := k.isLt; omega))
  | .txWord k => (s.tx.memory[k.toNat]'(by have := k.isLt; exact this)).data
  | .txBits k => BitVec.ofNat 6 (s.tx.memory[k.toNat]'(by have := k.isLt; exact this)).validBits
  | .rxWord k => (s.rx.memory[k.toNat]'(by have := k.isLt; exact this)).data
  | .rxBits k => BitVec.ofNat 6 (s.rx.memory[k.toNat]'(by have := k.isLt; exact this)).validBits
  | .written => BitVec.ofNat 64 (2^p.length-1)
  | .pending => 0 | .valid => 1
  | .count => BitVec.ofNat 7 p.length
  | .idleLevels => p.idle.levels | .idleEnabled => p.idle.enabled
  | .generation => s.generation | .transfer => s.transfer
  | .phase => s.phase.code | .pc => s.pc
  | .currentWord => Pinwheel.Program.Streaming.encode s.current | .total => s.total
  | .remaining => s.remaining | .countdown => s.countdown
  | .cellBit => BitVec.ofBool s.cellBit | .levels => s.pins.levels | .enabled => s.pins.enabled
  | .txHead => BitVec.ofNat a s.tx.head.val | .txTail => BitVec.ofNat a s.tx.tail.val
  | .txCount => BitVec.ofNat 4 s.tx.count.val
  | .rxHead => BitVec.ofNat a s.rx.head.val | .rxTail => BitVec.ofNat a s.rx.tail.val
  | .rxCount => BitVec.ofNat 4 s.rx.count.val
  | .txShift => s.txShift | .txValid => s.txValid
  | .rxPartial => s.rxPartial | .rxUsed => s.rxUsed
  | .txAccepted => s.txAccepted | .txConsumed => s.txConsumed
  | .rxProduced => s.rxProduced | .rxPopped => s.rxPopped
  | .stage1 => s.samplerFirst | .stage2 => s.samplerSecond

def inputValues (i : Pinwheel.Program.Streaming.Input) : Values Pinwheel.Hardware.Streaming.Core.Input := fun r => match r with
  | .initialize => BitVec.ofBool i.initialize | .command => i.command
  | .address => 0 | .word => 0 | .count => 0 | .idleLevels => 0 | .idleEnabled => 0
  | .startCount => i.startCount
  | .expectedGeneration => i.expectedGeneration | .expectedTransfer => i.expectedTransfer
  | .txPush => BitVec.ofBool i.txPush | .rxPop => BitVec.ofBool i.rxPop
  | .txData => i.txData | .txBits => i.txBits | .rawInputs => i.rawInputs

def isRuntime : Pinwheel.Hardware.Streaming.Core.Register a w → Bool
  | .word _ | .written | .pending | .valid | .count | .idleLevels | .idleEnabled => false
  | _ => true

def fromBank (bank : Array Nat) : Values (Pinwheel.Hardware.Streaming.Core.Register a) := fun {w} r =>
  BitVec.ofNat w (bank[Pinwheel.Hardware.Streaming.Core.registerIndex r]?.getD 0)

def snapshot (s : Values (Pinwheel.Hardware.Streaming.Core.Register a)) : Array Nat :=
  (Pinwheel.Hardware.Streaming.Core.registers a).map fun ⟨_,r⟩ => (s r).toNat

def checkStep (p : Pinwheel.Program.Streaming.Program) (i : Pinwheel.Program.Streaming.Input) (s : Pinwheel.Program.Streaming.State a) (bank : Array Nat)
    (name : String) (edge : Nat) : IO (Pinwheel.Program.Streaming.State a × Array Nat) := do
  let expected := Pinwheel.Program.Streaming.step p i s
  let actual := snapshot ((Pinwheel.Hardware.Streaming.Core.circuit a).step (inputValues i) (fromBank bank))
  let ev : Values (Pinwheel.Hardware.Streaming.Core.Register a) := sourceValues p expected
  for ⟨_,r⟩ in Pinwheel.Hardware.Streaming.Core.registers a do
    if isRuntime r && (fromBank actual r).toNat != (ev r).toNat then
      throw (IO.userError s!"{name} edge{edge} {Pinwheel.Hardware.Streaming.Core.registerLabel r}: hardware={(fromBank actual r).toNat}, source={(ev r).toNat}; phase={s.phase.code.toNat}, command={i.command.toNat}")
  return (expected,actual)

def exercise (a n : Nat) (jtag : Bool) : IO Nat := do
  let p := if jtag then (Pinwheel.Program.Streaming.jtagImage 0).program else (Pinwheel.Program.Streaming.spiImage 0).program
  let mut s : Pinwheel.Program.Streaming.State a := { generation := 1, pins := p.idle }
  let mut bank := snapshot (sourceValues p s)
  let name := s!"d{2^a}-n{n}-jtag{jtag}"
  let pair ← checkStep p {command:=3,startCount:=BitVec.ofNat 16 n,expectedGeneration:=1} s bank name 0
  s := pair.1; bank := pair.2
  let mut released := false
  let mut edges := 1
  let mut txStall := false
  let mut rxStall := false
  for edge in [1:2500] do
    let left := n-s.txAccepted.toNat
    let bits := min 32 left
    let push := s.phase.busy && left>0 && edge>40 && edge%13==3
    let pop := edge>700 && edge%19==7
    let release := s.phase.retained && s.drained
    let i : Pinwheel.Program.Streaming.Input := {
      command := if release then 4 else if edge%47==2 then 4 else 0
      expectedGeneration := s.generation
      expectedTransfer := if edge%31==0 then s.transfer+1 else s.transfer
      txPush := push, txBits:=BitVec.ofNat 6 bits
      txData := BitVec.ofNat 32 (edge*16777619+2166136261)
      rxPop := pop
      rawInputs := BitVec.ofNat 2 (edge/3) }
    txStall := txStall || (s.phase == .boundary && !s.txReady)
    rxStall := rxStall || (s.phase == .boundary && !s.rxReady)
    let pair ← checkStep p i s bank name edge
    s := pair.1; bank := pair.2; edges := edge+1
    if release && s.phase == .free then
      released := true
      break
  unless released do throw (IO.userError s!"{name} failed to release; {s.phase.code.toNat}")
  IO.println s!"{name}: {edges} edges; TXstall={txStall}; RXstall={rxStall}"
  return edges

def main : IO Unit := do
  let mut total := 0
  for a in [1,2] do
    for n in [0,1,31,32,33,65,129] do
      for jtag in [false,true] do total := total + (← exercise a n jtag)
  IO.println s!"PASS: 28 all-runtime-field source/circuit cases, {total} edges."

end StreamingParity

def main : IO Unit := StreamingParity.main

