import Pinwheel.Hardware.Bank
import Pinwheel.Hardware.Switch.PacketEncoding
import Pinwheel.Hardware.Stream.ElasticCircuit
import Pinwheel.Hardware.Arbitration.RoundRobinMasked

/-! Structural buffered packet switch. Input FIFOs store destination ++ payload;
output registers store only payload. Source provenance is erased from physical
state. The cursor of each output is one-hot and advances only on slot refill.
Invalid asserted destination codes neither enter a FIFO nor receive ready.
-/
namespace Pinwheel.Hardware.Switch.Structural

open Physical

set_option backward.isDefEq.respectTransparency false

abbrev Register (n m dw w depth : Nat) :=
  Stream.Joint (Bank (n+1) (Stream.CellReg (dw+w) depth))
    (Stream.Joint (Bank (m+1) (Stream.CellReg w 1)) (Bank (m+1) (Lane 1 (n+1))))

def registers (n m dw w depth : Nat) : Interface (Register n m dw w depth) :=
  indexedInterface (Stream.Joint.interface
    (Bank.interface (n+1) (Stream.CellReg.interface (dw+w) depth))
    (Stream.Joint.interface (Bank.interface (m+1) (Stream.CellReg.interface w 1))
      (Bank.interface (m+1) (lanePorts 1 (n+1)).interface))) "reg_"

def fifoReg (k : Fin (n+1)) (r : Stream.CellReg (dw+w) depth b) : Register n m dw w depth b :=
  .left (.at k r)
def slotReg (o : Fin (m+1)) (r : Stream.CellReg w 1 b) : Register n m dw w depth b :=
  .right (.left (.at o r))
def cursorReg (o : Fin (m+1)) (k : Fin (n+1)) : Register n m dw w depth 1 :=
  .right (.right (.at o (.at k)))

def slotValue (s : Switch.State n (m+1) (BitVec w)) (o : Fin (m+1)) : Option (BitVec w) :=
  (s.slots o).map (fun d => d.packet.payload)

def encode (e : DestinationEncoding (m+1)) (s : Switch.State n (m+1) (BitVec w)) :
    Values (Register n m e.width w depth)
  | _, .left (.at k r) => PacketEncoding.cells e (s.queues k) r
  | _, .right (.left (.at o r)) => Stream.cells (slotValue s o).toList r
  | _, .right (.right (.at o (.at k))) => BitVec.ofBool (k == s.cursor o)

abbrev Wire (n m dw w depth b : Nat) := Expr (In n m dw w) (Register n m dw w depth) b

def headValid (dw w depth : Nat) (k : Fin (n+1)) : Wire n m dw w depth 1 :=
  (Stream.cellValid (dw+w) depth 0).bind (fun p => .input p) (fun r => .reg (fifoReg k r))
def headData (dw w depth : Nat) (k : Fin (n+1)) : Wire n m dw w depth (dw+w) :=
  (Stream.cellData (dw+w) depth 0).bind (fun p => .input p) (fun r => .reg (fifoReg k r))
def headPayload (dw w depth : Nat) (k : Fin (n+1)) : Wire n m dw w depth w :=
  .slice 0 w (by omega) (headData dw w depth k)

def request (e : DestinationEncoding (m+1)) (w depth : Nat) (o : Fin (m+1)) (k : Fin (n+1)) :
    Wire n m e.width w depth 1 :=
  .band (headValid e.width w depth k)
    (.equal (.slice w e.width (by omega) (headData e.width w depth k))
      (.lit (encodeDestination e o)))

def canLoad (dw w depth : Nat) (o : Fin (m+1)) : Wire n m dw w depth 1 :=
  (Expr.inv (.reg (slotReg o (.valid 0)))).bor (.input (outReady o))

/-- The proved masked selector is shared by grant, payload and cursor updates. -/
def selection (e : DestinationEncoding (m+1)) (w depth : Nat) (o : Fin (m+1))
    (value : Fin (n+1) → Wire n m e.width w depth b) (fallback : Wire n m e.width w depth b) :
    Wire n m e.width w depth b :=
  Arbitration.RoundRobinMasked.selection (fun c => .reg (cursorReg o c))
    (request e w depth o) value fallback

def gated (dw w depth : Nat) (o : Fin (m+1)) (value : Wire n m dw w depth b) : Wire n m dw w depth b :=
  .mux (.input reset) (.lit 0) (.mux (canLoad dw w depth o) value (.lit 0))

def grantBit (e : DestinationEncoding (m+1)) (w depth : Nat) (o : Fin (m+1)) (k : Fin (n+1)) :
    Wire n m e.width w depth 1 :=
  gated e.width w depth o (selection e w depth o (fun winner => .lit (BitVec.ofBool (winner == k))) (.lit 0))
def grantAny (e : DestinationEncoding (m+1)) (w depth : Nat) (o : Fin (m+1)) :
    Wire n m e.width w depth 1 :=
  gated e.width w depth o (selection e w depth o (fun _ : Fin (n+1) => .lit 1) (.lit 0))
def selectedPayload (e : DestinationEncoding (m+1)) (w depth : Nat) (o : Fin (m+1)) :
    Wire n m e.width w depth w :=
  gated e.width w depth o (selection e w depth o (headPayload e.width w depth) (.lit 0))

def anyWire (bits : α → Expr I R 1) (xs : List α) : Expr I R 1 :=
  xs.foldr (fun x rest => (bits x).bor rest) (.lit 0)
def pulled (e : DestinationEncoding (m+1)) (w depth : Nat) (k : Fin (n+1)) :
    Wire n m e.width w depth 1 :=
  anyWire (fun o => grantBit e w depth o k) (List.finRange (m+1))

/-- Comparing against the largest legal code also works when every code is legal. -/
def legal (e : DestinationEncoding (m+1)) (w depth : Nat) (k : Fin (n+1)) :
    Wire n m e.width w depth 1 :=
  .inv (.ult (.lit (encodeDestination e ⟨m, by omega⟩)) (.input (inDestination k)))
def admitted (e : DestinationEncoding (m+1)) (w depth : Nat) (k : Fin (n+1)) :
    Wire n m e.width w depth 1 := .band (.input (inValid k)) (legal e w depth k)
def admissible (e : DestinationEncoding (m+1)) (w depth : Nat) (k : Fin (n+1)) :
    Wire n m e.width w depth 1 := (Expr.inv (.input (inValid k))).bor (legal e w depth k)

def fifoInput (e : DestinationEncoding (m+1)) (w depth : Nat) (k : Fin (n+1)) :
    {b : Nat} → Stream.In (e.width+w) b → Wire n m e.width w depth b :=
  Stream.inputExpr (.input reset) (admitted e w depth k) (pulled e w depth k)
    (.mux (admitted e w depth k) (.concat (.input (inDestination k)) (.input (inPayload k))) (.lit 0))
def slotInput (e : DestinationEncoding (m+1)) (w depth : Nat) (o : Fin (m+1)) :
    {b : Nat} → Stream.In w b → Wire n m e.width w depth b :=
  Stream.inputExpr (.input reset) (grantAny e w depth o) (.input (outReady o)) (selectedPayload e w depth o)

def cursorNext (e : DestinationEncoding (m+1)) (w depth : Nat) (o : Fin (m+1)) (k : Fin (n+1)) :
    Wire n m e.width w depth 1 :=
  .mux (.input reset) (.lit (BitVec.ofBool (k == 0)))
    (.mux (canLoad e.width w depth o)
      (selection e w depth o (fun winner => .lit (BitVec.ofBool (k == Arbitration.RoundRobin.next winner))) (.reg (cursorReg o k)))
      (.reg (cursorReg o k)))

def circuit (e : DestinationEncoding (m+1)) (n w depth : Nat) :
    Circuit (In n m e.width w) (Register n m e.width w depth) (Out n m w) where
  next := fun {b} r => match b, r with
    | _, .left (.at k r) => ((Stream.Fifo.circuit (e.width+w) depth).next r).bind
        (fifoInput e w depth k) (fun r => .reg (fifoReg k r))
    | _, .right (.left (.at o r)) => ((Stream.Elastic.circuit (Stream.Map.identity w)).next r).bind
        (slotInput e w depth o) (fun r => .reg (slotReg o r))
    | _, .right (.right (.at o (.at k))) => cursorNext e w depth o k
  output := fun {b} p => match b, p with
    | _, .left (.at k) => .band (admissible e w depth k)
        (((Stream.Fifo.circuit (e.width+w) depth).output Stream.inReady).bind
          (fifoInput e w depth k) (fun r => .reg (fifoReg k r)))
    | _, .right (.left (.at o)) => ((Stream.Elastic.circuit (Stream.Map.identity w)).output Stream.outValid).bind
        (slotInput e w depth o) (fun r => .reg (slotReg o r))
    | _, .right (.right (.at o)) => ((Stream.Elastic.circuit (Stream.Map.identity w)).output Stream.outData).bind
        (slotInput e w depth o) (fun r => .reg (slotReg o r))

end Pinwheel.Hardware.Switch.Structural
