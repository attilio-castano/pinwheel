import Pinwheel.UART.RxProofs
import Pinwheel.Engine.Reactive

namespace Pinwheel.Compile.UARTRx
open Engine.Reactive
open UART.Rx (Config)

abbrev RxProgram := Program 255 15
abbrev RxState := State 255 15
abbrev RxInstruction := Instruction 255 15

def chunks (duration : Nat) : Nat := (duration - 1) / 256 + 1
def halfChunks (cfg : Config) : Nat := chunks cfg.half
def bitChunks (cfg : Config) : Nat := chunks cfg.bitCycles
def haltPC (cfg : Config) : Nat := 2 + halfChunks cfg + 9 * bitChunks cfg

def base (cfg : Config) (symbol : Fin 10) : Nat :=
  if symbol.val = 0 then 2 else 2 + halfChunks cfg + (symbol.val - 1) * bitChunks cfg

def address (n : Nat) : Fin 256 := Fin.ofNat 256 n

def captureAt (cfg : Config) (slot : Fin 16) : Capture 15 := ⟨cfg.input, slot⟩

def poll (cfg : Config) (yes no : Nat) : RxInstruction :=
  .checked ⟨⟨{}, 0, none⟩, ⟨0, 0⟩, some (captureAt cfg 8),
    .branch 8 (address yes) (address no)⟩

/-- A short first chunk followed by full chunks. The final chunk captures once.
All chunks together occupy exactly the protocol's whole-symbol duration. -/
def timedInstruction (cfg : Config) (symbol : Fin 10) (offset : Nat) : RxInstruction :=
  let d := UART.Rx.duration cfg symbol
  let timer := if offset = 0 then Fin.ofNat 256 (d - 1) else 255
  let action : Action 15 := ⟨{}, timer, none⟩
  if offset + 1 < chunks d then .action action
  else .checked ⟨action, ⟨0, 0⟩, some (captureAt cfg (UART.Rx.sampleSlot symbol)),
    if symbol.val = 0 then .branch 8 0 (address (base cfg 1)) else .sequential⟩

def instruction (cfg : Config) (pc : Fin 256) : RxInstruction :=
  if pc.val = 0 then poll cfg 1 0
  else if pc.val = 1 then poll cfg 1 2
  else if pc.val < 2 + halfChunks cfg then timedInstruction cfg 0 (pc.val - 2)
  else if pc.val < haltPC cfg then
    let offset := pc.val - (2 + halfChunks cfg)
    timedInstruction cfg (Fin.ofNat 10 (offset / bitChunks cfg + 1)) (offset % bitChunks cfg)
  else .halt

def program (cfg : Config) : RxProgram :=
  ⟨Vector.ofFn (instruction cfg), {}, address (haltPC cfg)⟩

/-- Engine completion includes protocol errors; the retained stop sample distinguishes them. -/
def result (s : RxState) : Option UART.Rx.Outcome :=
  match s.control with
  | .stopped .completed => some (UART.Rx.outcome s.samples)
  | _ => none

def execute (cfg : Config) (incoming : Nat → Inputs) (cycles : Nat) : RxState :=
  run (program cfg) (start (program cfg) (incoming 0)) incoming cycles

end Pinwheel.Compile.UARTRx
