import Pinwheel.Program.StreamingReadySegments
import Pinwheel.UART.Spec

/-! Author an 8N1 transmitter from ordinary Ready PULSE rows. The byte is
    a program parameter and TX uses one configured output pad. -/
namespace Pinwheel.Program.StreamingReadyUARTTx

open StreamingReady (Cell Pins)
open StreamingReadySegments

def config (hold : Fin 253) : Pinwheel.UART.Config :=
  ⟨⟨hold.val + 3, by omega⟩⟩

theorem cycles (hold : Fin 253) : (config hold).cycles = hold.val + 4 := rfl

def pins (level : Bool) : Pins := ⟨BitVec.ofNat 3 level.toNat, 1⟩

def cell (hold : Fin 253) (level : Bool) : Cell :=
  {lowDuration := ⟨hold.val, by omega⟩, highDuration := 0,
   lowPins := pins level, highPins := pins level}

def symbols (byte : BitVec 8) : List Bool :=
  false :: ((List.range 8).map byte.getLsbD ++ [true])

theorem symbols_eq_frame (byte : BitVec 8) : symbols byte = (Pinwheel.UART.frame byte).toList := rfl

def rows (hold : Fin 253) (byte : BitVec 8) : List Row :=
  (symbols byte).map (fun level => .cell (.pulse (cell hold level))) ++ [.cell .halt]

def image (hold : Fin 253) (byte : BitVec 8) : Except String (Image (rows hold byte) 0) :=
  compile (rows hold byte) 0

theorem checked (hold : Fin 253) (byte : BitVec 8) : (check (rows hold byte) 0).isSome = true := rfl

end Pinwheel.Program.StreamingReadyUARTTx
