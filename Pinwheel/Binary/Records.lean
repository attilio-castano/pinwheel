import Pinwheel.Binary.Basic
import Pinwheel.Engine.Counted

namespace Pinwheel.Binary
open Engine.Reactive
open Engine.Reactive.Counted

def putPins (p : Pins) : List Byte := putBits (by decide) p.levels ++ putBits (by decide) p.enabled

def getPins : Reader Pins := do return ⟨← getBits 3, ← getBits 3⟩

def putIndex : Index → List Byte
  | .literal v => putFin (by decide) (0 : Fin 2) ++ putFin (by decide) v
  | .loop d => putFin (by decide) (1 : Fin 2) ++ putFin (by decide) d

def getIndex : Reader Index := do
  let tag ← getFin 2
  if tag.val == 0 then return .literal (← getFin 8) else return .loop (← getFin 2)

def putSerial (s : Serial) : List Byte :=
  putIndex s.byte ++ putIndex s.bit ++ putBool s.msbFirst ++ putBool s.invert

def getSerial : Reader Serial := do return ⟨← getIndex, ← getIndex, ← getBool, ← getBool⟩

def putPinExpr : PinExpr → List Byte
  | .literal p => putFin (by decide) (0 : Fin 2) ++ putPins p
  | .serial p pin enable s => putFin (by decide) (1 : Fin 2) ++ putPins p ++
      putFin (by decide) pin ++ putBool enable ++ putSerial s

def getPinExpr : Reader PinExpr := do
  let tag ← getFin 2
  if tag.val == 0 then return .literal (← getPins)
  else return .serial (← getPins) (← getFin 3) (← getBool) (← getSerial)

def putSample (s : Sample) : List Byte := putFin (by decide) s.input ++ putIndex s.destination

def getSample : Reader Sample := do return ⟨← getFin 2, ← getIndex⟩

def putCondition (c : Condition) : List Byte := putFin (by decide) c.input ++ putBool c.level

def getCondition : Reader Condition := do return ⟨← getFin 2, ← getBool⟩

def putCheck (c : Check) : List Byte := putBits (by decide) c.mask ++ putBits (by decide) c.value

def getCheck : Reader Check := do return ⟨← getBits 2, ← getBits 2⟩

def putTarget : Target → List Byte
  | .absolute pc => putFin (by decide) (0 : Fin 2) ++ putFin (by decide) pc
  | .next => putFin (by decide) (1 : Fin 2)

def getTarget : Reader Target := do
  let tag ← getFin 2
  if tag.val == 0 then return .absolute (← getFin 128) else return .next

def putTransfer : Transfer → List Byte
  | .sequential => putFin (by decide) (0 : Fin 3)
  | .jump pc => putFin (by decide) (1 : Fin 3) ++ putTarget pc
  | .branch sample yes no => putFin (by decide) (2 : Fin 3) ++ putIndex sample ++ putTarget yes ++ putTarget no

def getTransfer : Reader Transfer := do
  let tag ← getFin 3
  match tag.val with
  | 0 => return .sequential
  | 1 => return .jump (← getTarget)
  | _ => return .branch (← getIndex) (← getTarget) (← getTarget)

def putSuccessor : Successor → List Byte
  | .sequential => putFin (by decide) (0 : Fin 4)
  | .jump pc => putFin (by decide) (1 : Fin 4) ++ putTarget pc
  | .branch sample yes no => putFin (by decide) (2 : Fin 4) ++ putIndex sample ++ putTarget yes ++ putTarget no
  | .select index value yes no => putFin (by decide) (3 : Fin 4) ++ putIndex index ++
      putFin (by decide) value ++ putTransfer yes ++ putTransfer no

def getSuccessor : Reader Successor := do
  let tag ← getFin 4
  match tag.val with
  | 0 => return .sequential
  | 1 => return .jump (← getTarget)
  | 2 => return .branch (← getIndex) (← getTarget) (← getTarget)
  | _ => return .select (← getIndex) (← getFin 8) (← getTransfer) (← getTransfer)

def putTemplate : Template → List Byte
  | .action pins d c => putFin (by decide) (0 : Fin 5) ++ putPinExpr pins ++
      putFin (by decide) d ++ putOption putSample c
  | .wait pins c w => putFin (by decide) (1 : Fin 5) ++ putPinExpr pins ++
      putCondition c ++ putFin (by decide) w
  | .checked pins d guard entry terminal finish => putFin (by decide) (2 : Fin 5) ++
      putPinExpr pins ++ putFin (by decide) d ++ putCheck guard ++ putOption putSample entry ++
      putOption putSample terminal ++ putSuccessor finish
  | .qualify pins c d w => putFin (by decide) (3 : Fin 5) ++ putPinExpr pins ++
      putCheck c ++ putFin (by decide) d ++ putFin (by decide) w
  | .halt => putFin (by decide) (4 : Fin 5)

def getTemplate : Reader Template := do
  let tag ← getFin 5
  match tag.val with
  | 0 => return .action (← getPinExpr) (← getFin 256) (← getOption getSample)
  | 1 => return .wait (← getPinExpr) (← getCondition) (← getFin 256)
  | 2 => return .checked (← getPinExpr) (← getFin 256) (← getCheck) (← getOption getSample) (← getOption getSample) (← getSuccessor)
  | 3 => return .qualify (← getPinExpr) (← getCheck) (← getFin 256) (← getFin 256)
  | _ => return .halt

end Pinwheel.Binary
