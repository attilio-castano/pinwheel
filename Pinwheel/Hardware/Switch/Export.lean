import Pinwheel.Hardware.Switch.Circuit
import Pinwheel.Hardware.TypedHierarchy

/-! Hierarchical export with the same state bits and same-edge behavior as the
structural switch. FIFO and elastic-slot leaves expose raw register taps. A
typed control module consumes those taps and reuses the structural expressions
for every leaf input, visible output, and cursor update. In particular it does
not assume that cursor bits or FIFO cells encode a reachable logical state.

The top-level Verilog contains only typed-descriptor-derived wiring. Fresh
artifact readback checks the unproved HDL emitter and hierarchy assembly.
-/

namespace Pinwheel.Hardware.Switch.Export

open Physical Lean

set_option backward.isDefEq.respectTransparency false

abbrev CursorRegister (n m : Nat) := Bank (m+1) (Lane 1 (n+1))
abbrev LeafState (n m dw w depth : Nat) :=
  Stream.Joint (Bank (n+1) (Stream.CellReg (dw+w) depth)) (Bank (m+1) (Stream.CellReg w 1))
abbrev ControlIn (n m dw w depth : Nat) := Stream.Joint (In n m dw w) (LeafState n m dw w depth)
abbrev ControlOut (n m dw w : Nat) := Stream.Joint (Out n m w)
  (Stream.Joint (Bank (n+1) (Stream.In (dw+w))) (Bank (m+1) (Stream.In w)))

def cursorInterface (n m : Nat) : Interface (CursorRegister n m) :=
  indexedInterface (Bank.interface (m+1) (lanePorts 1 (n+1)).interface) "cursor_"

def controlInputInterface (n m dw w depth : Nat) : Interface (ControlIn n m dw w depth) :=
  indexedInterface (Stream.Joint.interface (Physical.inputInterface n m dw w)
    (Stream.Joint.interface
      (Bank.interface (n+1) (Stream.CellReg.interface (dw+w) depth))
      (Bank.interface (m+1) (Stream.CellReg.interface w 1)))) "control_in_"

def controlOutputInterface (n m dw w : Nat) : Interface (ControlOut n m dw w) :=
  indexedInterface (Stream.Joint.interface (Physical.outputInterface n m w)
    (Stream.Joint.interface
      (Bank.interface (n+1) (Stream.inputPorts (dw+w)).interface)
      (Bank.interface (m+1) (Stream.inputPorts w).interface))) "control_out_"

def registerWire : Structural.Register n m dw w depth b →
    Expr (ControlIn n m dw w depth) (CursorRegister n m) b
  | .left (.at k r) => .input (.right (.left (.at k r)))
  | .right (.left (.at o r)) => .input (.right (.right (.at o r)))
  | .right (.right r) => .reg r

def controlWire (e : Structural.Wire n m dw w depth b) :
    Expr (ControlIn n m dw w depth) (CursorRegister n m) b :=
  e.bind (fun p => .input (.left p)) registerWire

def control (e : DestinationEncoding (m+1)) (n w depth : Nat) :
    Circuit (ControlIn n m e.width w depth) (CursorRegister n m) (ControlOut n m e.width w) where
  next := fun {b} r => match b, r with
    | _, .at o (.at k) => controlWire (Structural.cursorNext e w depth o k)
  output := fun {b} p => match b, p with
    | _, .left p => controlWire ((Structural.circuit e n w depth).output p)
    | _, .right (.left (.at k p)) => controlWire (Structural.fifoInput e w depth k p)
    | _, .right (.right (.at o p)) => controlWire (Structural.slotInput e w depth o p)

def controlValues (i : Values (In n m dw w)) (s : Values (Structural.Register n m dw w depth)) :
    Values (ControlIn n m dw w depth)
  | _, .left p => i p
  | _, .right (.left (.at k r)) => s (Structural.fifoReg k r)
  | _, .right (.right (.at o r)) => s (Structural.slotReg o r)

def cursorValues (s : Values (Structural.Register n m dw w depth)) : Values (CursorRegister n m)
  | _, .at o (.at k) => s (Structural.cursorReg o k)

theorem controlWire_eval (e : Structural.Wire n m dw w depth b)
    (i : Values (In n m dw w)) (s : Values (Structural.Register n m dw w depth)) :
    (controlWire e).eval (controlValues i s) (cursorValues s) = e.eval i s := by
  rw [controlWire, Expr.eval_bind]
  congr 1
  funext b r
  cases r with
  | left r => cases r; rfl
  | right r => cases r with
    | left r => cases r; rfl
    | right r => cases r with | «at» o r => cases r; rfl

/-- Expose every raw register bit without changing any next-state expression. -/
def tapped (c : Circuit I R O) : Circuit I R R :=
  ⟨c.next, fun r => .reg r⟩

theorem tapped_step (c : Circuit I R O) (i : Values I) (s : Values R) (r : R b) :
    (tapped c).step i s r = c.step i s r := rfl

theorem tapped_output (c : Circuit I R O) (i : Values I) (s : Values R) (r : R b) :
    (tapped c).observe i s r = s r := rfl

def fifoInstance (k : Fin (n+1)) : String := "fifo_" ++ Nat.repr k.val
def slotInstance (o : Fin (m+1)) : String := "slot_" ++ Nat.repr o.val
def stateLabel (d : Interface R) (r : R b) : String := "state_" ++ d.label r
def tapInterface (d : Interface R) : Interface R :=
  d.rename (stateLabel d) (by
    intro a b h
    apply d.unique
    simpa only [stateLabel, String.append_right_inj] using h)

abbrev Net (n m dw w depth : Nat) :=
  Stream.Joint
    (Bank (n+1) (Stream.Joint (Stream.In (dw+w)) (Stream.CellReg (dw+w) depth)))
    (Bank (m+1) (Stream.Joint (Stream.In w) (Stream.CellReg w 1)))

private def nets (n m dw w depth : Nat) : Interface (Net n m dw w depth) :=
  Stream.Joint.interface
    (Bank.interface (n+1) (Stream.Joint.interface (Stream.inputPorts (dw+w)).interface
      (Stream.CellReg.interface (dw+w) depth)))
    (Bank.interface (m+1) (Stream.Joint.interface (Stream.inputPorts w).interface
      (Stream.CellReg.interface w 1)))

/-- The controller sees raw taps, so the assembly covers malformed encodings too. -/
def hierarchy (e : DestinationEncoding (m+1)) (n w depth : Nat) (name : String) :
    TypedHierarchy (In n m e.width w) (Structural.Register n m e.width w depth)
      (Out n m w) (Net n m e.width w depth) := Id.run do
  let ii := Physical.inputInterface n m e.width w
  let oi := Physical.outputInterface n m w
  let ri := Structural.registers n m e.width w depth
  let fr := Stream.CellReg.interface (e.width+w) depth
  let sr := Stream.CellReg.interface w 1
  let fifo : TypedModule _ _ _ := ⟨name ++ "_fifo",
    tapped (Stream.Fifo.circuit (e.width+w) depth), (Stream.inputPorts (e.width+w)).interface,
    fr, tapInterface fr⟩
  let slot : TypedModule _ _ _ := ⟨name ++ "_slot",
    tapped (Stream.Elastic.circuit (Stream.Map.identity w)), (Stream.inputPorts w).interface,
    sr, tapInterface sr⟩
  let ctl : TypedModule _ _ _ := ⟨name ++ "_control", control e n w depth,
    controlInputInterface n m e.width w depth, cursorInterface n m,
    controlOutputInterface n m e.width w⟩
  let mut instances := #[]
  for k in List.finRange (n+1) do
    instances := instances.push (TypedHierarchy.Instance.connect (fifoInstance k) fifo
      (fun p => .net (.left (.at k (.left p)))) (fun p => .net (.left (.at k (.right p))))
      (Structural.fifoReg k))
  for k in List.finRange (m+1) do
    instances := instances.push (TypedHierarchy.Instance.connect (slotInstance k) slot
      (fun p => .net (.right (.at k (.left p)))) (fun p => .net (.right (.at k (.right p))))
      (Structural.slotReg k))
  let controller := TypedHierarchy.Instance.connect "control" ctl
    (fun p => match p with
      | .left p => .input p
      | .right (.left (.at k r)) => .net (.left (.at k (.right r)))
      | .right (.right (.at k r)) => .net (.right (.at k (.right r))))
    (fun p => match p with
      | .left p => .output p
      | .right (.left (.at k p)) => .net (.left (.at k (.left p)))
      | .right (.right (.at k p)) => .net (.right (.at k (.left p))))
    (fun r => .right (.right r))
  return ⟨name, ⟨name ++ "_flat", Structural.circuit e n w depth, ii, ri, oi⟩,
    nets n m e.width w depth, instances.push controller⟩

def rolesJson (n m dw w : Nat) : Json :=
  let ii := Physical.inputInterface n m dw w
  let oi := Physical.outputInterface n m w
  Json.mkObj
    [("reset", toJson (ii.label Physical.reset)),
     ("in_valid", toJson (Array.ofFn (fun k : Fin (n+1) => ii.label (Physical.inValid k)))),
     ("in_destination", toJson (Array.ofFn (fun k : Fin (n+1) => ii.label (Physical.inDestination k)))),
     ("in_payload", toJson (Array.ofFn (fun k : Fin (n+1) => ii.label (Physical.inPayload k)))),
     ("out_ready", toJson (Array.ofFn (fun o : Fin (m+1) => ii.label (Physical.outReady o)))),
     ("in_ready", toJson (Array.ofFn (fun k : Fin (n+1) => oi.label (Physical.inReady k)))),
     ("out_valid", toJson (Array.ofFn (fun o : Fin (m+1) => oi.label (Physical.outValid o)))),
     ("out_payload", toJson (Array.ofFn (fun o : Fin (m+1) => oi.label (Physical.outPayload o))))]

def registerRolesJson (n m dw w depth : Nat) : Json :=
  let ri := Structural.registers n m dw w depth
  let flatName := fun {b : Nat} (r : Structural.Register n m dw w depth b) => "r_" ++ ri.label r
  Json.mkObj
    [("fifo_valid", toJson (Array.ofFn (fun k : Fin (n+1) =>
        Array.ofFn (fun cell : Fin depth => flatName (Structural.fifoReg k (.valid cell)))))),
     ("fifo_data", toJson (Array.ofFn (fun k : Fin (n+1) =>
        Array.ofFn (fun cell : Fin depth => flatName (Structural.fifoReg k (.data cell)))))),
     ("slot_valid", toJson (Array.ofFn (fun o : Fin (m+1) => flatName (Structural.slotReg o (.valid 0))))),
     ("slot_payload", toJson (Array.ofFn (fun o : Fin (m+1) => flatName (Structural.slotReg o (.data 0))))),
     ("cursor", toJson (Array.ofFn (fun o : Fin (m+1) =>
        Array.ofFn (fun k : Fin (n+1) => flatName (Structural.cursorReg o k)))))]

def exportHierarchy (e : DestinationEncoding (m+1)) (n w depth : Nat)
    (dir : System.FilePath) (name : String) : IO Unit := do
  unless w > 0 && depth > 0 do throw (IO.userError "Hierarchy payload width and FIFO depth must be positive")
  let design := hierarchy e n w depth name
  let emitted ← IO.ofExcept design.emit
  let initial : Values (Structural.Register n m e.width w depth) := Structural.encode e Switch.initial
  let rows ← IO.ofExcept (emitted.descriptor.getObjVal? "registers" >>= Json.getArr?)
  let annotated := (rows.zip design.flat.registers.ports).map fun (row, ⟨_, r⟩) =>
    row.mergeObj (Json.mkObj [("initial", toJson (initial r).toNat), ("reset", toJson (initial r).toNat)])
  let emitted := { emitted with descriptor := emitted.descriptor.setObjVal! "registers" (toJson annotated) }
  emitted.write dir
    [("schema", toJson (1 : Nat)), ("input_count", toJson (n+1)), ("output_count", toJson (m+1)),
     ("depth", toJson depth), ("payload_width", toJson w), ("destination_width", toJson e.width),
     ("reset_synchronous", toJson true), ("roles", rolesJson n m e.width w),
     ("register_roles", registerRolesJson n m e.width w depth),
     ("startup", toJson "encoded_initial; hardware requires a reset edge before use"),
     ("state_contract", toJson "one-to-one with flat structural registers, including malformed raw encodings"),
     ("latency_added", toJson (0 : Nat))]

end Pinwheel.Hardware.Switch.Export
