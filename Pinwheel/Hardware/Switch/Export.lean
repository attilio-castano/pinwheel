import Pinwheel.Hardware.Switch.Circuit
import Pinwheel.Hardware.Emit
import Lean.Data.Json

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
def fifoWire (k : Fin (n+1)) (r : Stream.CellReg (dw+w) depth b) : String :=
  fifoInstance k ++ "_" ++ stateLabel (Stream.CellReg.interface (dw+w) depth) r
def slotWire (o : Fin (m+1)) (r : Stream.CellReg w 1 b) : String :=
  slotInstance o ++ "_" ++ stateLabel (Stream.CellReg.interface w 1) r
def fifoInputWire (k : Fin (n+1)) (p : Stream.In (dw+w) b) : String :=
  fifoInstance k ++ "_" ++ (Stream.inputPorts (dw+w)).interface.label p
def slotInputWire (o : Fin (m+1)) (p : Stream.In w b) : String :=
  slotInstance o ++ "_" ++ (Stream.inputPorts w).interface.label p

def hierarchyReference : Structural.Register n m dw w depth b → String
  | .left (.at k r) => fifoInstance k ++ ".r_" ++ (Stream.CellReg.interface (dw+w) depth).label r
  | .right (.left (.at o r)) => slotInstance o ++ ".r_" ++ (Stream.CellReg.interface w 1).label r
  | .right (.right r) => "control.r_" ++ (cursorInterface n m).label r

def tapInterface (d : Interface R) : Interface R :=
  d.rename (stateLabel d) (by
    intro a b h
    apply d.unique
    simpa only [stateLabel, String.append_right_inj] using h)

def controlInputConnection : ControlIn n m dw w depth b → String
  | .left p => (Physical.inputInterface n m dw w).label p
  | .right (.left (.at k r)) => fifoWire k r
  | .right (.right (.at o r)) => slotWire o r

def controlOutputConnection : ControlOut n m dw w b → String
  | .left p => (Physical.outputInterface n m w).label p
  | .right (.left (.at k p)) => fifoInputWire k p
  | .right (.right (.at o p)) => slotInputWire o p

def connections (d : Interface P) (wire : {b : Nat} → P b → String) : Array String :=
  d.ports.map (fun ⟨_, p⟩ => s!".{d.label p}({wire p})")

def vectorDeclaration (direction name : String) (width : Nat) : String :=
  s!"{direction} [{width-1}:0] {name}"

def instanceText (moduleName instanceName : String) (ports : Array String) : String :=
  s!"{moduleName} {instanceName}(" ++ String.intercalate ", " (#[".clk(clk)"] ++ ports).toList ++ ");"

/-- Wiring only: every gate and state transition is emitted from typed Exprs. -/
def hierarchyVerilog (e : DestinationEncoding (m+1)) (n w depth : Nat) (name : String) : String := Id.run do
  let ii := Physical.inputInterface n m e.width w
  let oi := Physical.outputInterface n m w
  let fi := (Stream.inputPorts (e.width+w)).interface
  let fr := Stream.CellReg.interface (e.width+w) depth
  let si := (Stream.inputPorts w).interface
  let sr := Stream.CellReg.interface w 1
  let ci := controlInputInterface n m e.width w depth
  let co := controlOutputInterface n m e.width w
  let ports := #["input wire clk"] ++
    ii.ports.map (fun ⟨b, p⟩ => vectorDeclaration "input wire" (ii.label p) b) ++
    oi.ports.map (fun ⟨b, p⟩ => vectorDeclaration "output wire" (oi.label p) b)
  let mut lines := #[s!"module {name}(" ++ String.intercalate ", " ports.toList ++ ");"]
  for k in List.finRange (n+1) do
    lines := lines ++ fi.ports.map (fun ⟨b, p⟩ => vectorDeclaration "wire" (fifoInputWire k p) b ++ ";")
    lines := lines ++ fr.ports.map (fun ⟨b, r⟩ => vectorDeclaration "wire" (fifoWire (dw := e.width) (w := w) k r) b ++ ";")
    lines := lines.push (instanceText (name ++ "_fifo") (fifoInstance k)
      (connections fi (fifoInputWire k) ++ connections (tapInterface fr) (fifoWire (dw := e.width) (w := w) k)))
  for o in List.finRange (m+1) do
    lines := lines ++ si.ports.map (fun ⟨b, p⟩ => vectorDeclaration "wire" (slotInputWire o p) b ++ ";")
    lines := lines ++ sr.ports.map (fun ⟨b, r⟩ => vectorDeclaration "wire" (slotWire o r) b ++ ";")
    lines := lines.push (instanceText (name ++ "_slot") (slotInstance o)
      (connections si (slotInputWire o) ++ connections (tapInterface sr) (slotWire o)))
  lines := lines.push (instanceText (name ++ "_control") "control"
    (connections ci controlInputConnection ++ connections co controlOutputConnection))
  return String.intercalate "\n" (lines.push "endmodule").toList ++ "\n"

def interfaceJson (d : Interface P) : Json := toJson (d.ports.mapIdx (fun index p =>
  Json.mkObj [("name", toJson (d.label p.2)), ("width", toJson p.1), ("index", toJson index)]))

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

def leafJson (name : String) (inputs : Interface I) (registers : Interface R) (outputs : Interface O) : Json :=
  Json.mkObj [("module", toJson name), ("mlir", toJson (name ++ ".mlir")),
    ("inputs", interfaceJson inputs), ("outputs", interfaceJson outputs),
    ("registers", toJson (registers.ports.map (fun ⟨b, r⟩ => Json.mkObj
      [("name", toJson ("r_" ++ registers.label r)),
       ("reference", toJson ("r_" ++ registers.label r)), ("width", toJson b)])))]

def exportHierarchy (e : DestinationEncoding (m+1)) (n w depth : Nat)
    (dir : System.FilePath) (name : String) : IO Unit := do
  unless w > 0 && depth > 0 do throw (IO.userError "Hierarchy payload width and FIFO depth must be positive")
  IO.FS.createDirAll dir
  let ii := Physical.inputInterface n m e.width w
  let oi := Physical.outputInterface n m w
  let ri := Structural.registers n m e.width w depth
  let fi := (Stream.inputPorts (e.width+w)).interface
  let fr := Stream.CellReg.interface (e.width+w) depth
  let si := (Stream.inputPorts w).interface
  let sr := Stream.CellReg.interface w 1
  let ci := controlInputInterface n m e.width w depth
  let cr := cursorInterface n m
  let co := controlOutputInterface n m e.width w
  let fifoName := name ++ "_fifo"
  let slotName := name ++ "_slot"
  let controlName := name ++ "_control"
  IO.FS.writeFile (dir / (fifoName ++ ".mlir")) (← IO.ofExcept
    (Emit.moduleText fifoName (tapped (Stream.Fifo.circuit (e.width+w) depth))
      fi.ports fr.ports fr.ports fi.label fr.label (stateLabel fr)))
  IO.FS.writeFile (dir / (slotName ++ ".mlir")) (← IO.ofExcept
    (Emit.moduleText slotName (tapped (Stream.Elastic.circuit (Stream.Map.identity w)))
      si.ports sr.ports sr.ports si.label sr.label (stateLabel sr)))
  IO.FS.writeFile (dir / (controlName ++ ".mlir")) (← IO.ofExcept
    (Emit.moduleText controlName (control e n w depth) ci.ports cr.ports co.ports ci.label cr.label co.label))
  IO.FS.writeFile (dir / "hierarchy_top.sv") (hierarchyVerilog e n w depth name)
  IO.FS.writeFile (dir / "flat.mlir") (← IO.ofExcept
    (Emit.moduleText (name ++ "_flat") (Structural.circuit e n w depth)
      ii.ports ri.ports oi.ports ii.label ri.label oi.label))
  let initial : Values (Structural.Register n m e.width w depth) := Structural.encode e Switch.initial
  let registerMap := ri.ports.map (fun ⟨_, r⟩ => ("r_" ++ ri.label r, toJson (hierarchyReference r)))
  let leaves := #[leafJson fifoName fi fr (tapInterface fr), leafJson slotName si sr (tapInterface sr),
    leafJson controlName ci cr co]
  let descriptor := Json.mkObj
    [("schema", toJson (1 : Nat)), ("module", toJson name), ("flat_module", toJson (name ++ "_flat")),
     ("input_count", toJson (n+1)), ("output_count", toJson (m+1)), ("depth", toJson depth),
     ("payload_width", toJson w), ("destination_width", toJson e.width), ("clock", toJson "clk"),
     ("reset_synchronous", toJson true), ("inputs", interfaceJson ii), ("outputs", interfaceJson oi),
     ("registers", toJson (ri.ports.map (fun ⟨b, r⟩ => Json.mkObj
       [("name", toJson ("r_" ++ ri.label r)), ("flat_reference", toJson ("r_" ++ ri.label r)),
        ("reference", toJson (hierarchyReference r)), ("width", toJson b),
        ("initial", toJson ((initial r).toNat)), ("reset", toJson ((initial r).toNat))]))),
     ("roles", rolesJson n m e.width w), ("register_roles", registerRolesJson n m e.width w depth),
     ("register_map", Json.mkObj registerMap.toList),
     ("hierarchical_registers", toJson (ri.ports.map (fun p => hierarchyReference p.2))),
     ("leaves", toJson #[fifoName, slotName, controlName]), ("leaf_interfaces", toJson leaves),
     ("top_verilog", toJson "hierarchy_top.sv"),
     ("startup", toJson "encoded_initial; hardware requires a reset edge before use"),
     ("state_contract", toJson "one-to-one with flat structural registers, including malformed raw encodings"),
     ("latency_added", toJson (0 : Nat))]
  IO.FS.writeFile (dir / "interface.json") (descriptor.pretty ++ "\n")

end Pinwheel.Hardware.Switch.Export
