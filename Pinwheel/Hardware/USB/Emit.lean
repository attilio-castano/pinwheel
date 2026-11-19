import Pinwheel.Hardware.USB.Core
import Pinwheel.Hardware.Streaming.FrontendEmit

namespace Pinwheel.Hardware.USB
open Pinwheel.Hardware

private def widthPrefix (width : Nat) : String :=
  if width = 1 then "" else s!"[{width - 1}:0] "

private structure Wires where
  lines : Array String := #[]
  names : Std.HashMap (Nat × String) String := {}

private abbrev Render := StateT Wires (Except String)

private def wireFor (width : Nat) (rhs : String) : Render String := do
  let wires ← get
  if let some name := wires.names[(width, rhs)]? then return name
  let name := s!"n{wires.lines.size}"
  set {wires with
    lines := wires.lines.push s!"  wire {widthPrefix width}{name} = {rhs};"
    names := wires.names.insert (width, rhs) name}
  return name

private def expression (inputName : {w : Nat} → I w → String)
    (registerName : {w : Nat} → R w → String) (e : Expr I R w) : Render String := do
  match w, e with
  | 0, _ => throw "SystemVerilog requires positive widths"
  | _, .input p => return inputName p
  | _, .reg r => return registerName r
  | w, .lit k => return s!"{w}'d{k.toNat}"
  | _, .concat (a := a) (b := b) x y =>
    let high ← expression inputName registerName x
    let low ← expression inputName registerName y
    wireFor (a+b) ("{" ++ high ++ ", " ++ low ++ "}")
  | w, .inv x => wireFor w s!"~{← expression inputName registerName x}"
  | w, .band x y => wireFor w s!"{← expression inputName registerName x} & {← expression inputName registerName y}"
  | w, .sub x y => wireFor w s!"{← expression inputName registerName x} - {← expression inputName registerName y}"
  | _, .slice (w := width) first len _ x =>
    let source ← expression inputName registerName x
    if width == len then return source
    let source ← wireFor width source
    wireFor len s!"{source}[{first + len - 1}:{first}]"
  | _, .equal x y => wireFor 1 s!"{← expression inputName registerName x} == {← expression inputName registerName y}"
  | _, .ult x y => wireFor 1 s!"{← expression inputName registerName x} < {← expression inputName registerName y}"
  | _, .zero (w := width) x => wireFor 1 s!"{← expression inputName registerName x} == {width}'d0"
  | w, .mux c t f =>
    wireFor w s!"{← expression inputName registerName c} ? {← expression inputName registerName t} : {← expression inputName registerName f}"

private def moduleText (name : String) (c : Circuit I R O)
    (inputs : Array (Sigma I)) (registers : Array (Sigma R)) (outputs : Array (Sigma O))
    (inputLabel : {w : Nat} → I w → String) (registerLabel : {w : Nat} → R w → String)
    (outputLabel : {w : Nat} → O w → String) : Except String String := do
  let regName := fun {w : Nat} (r : R w) => "r_" ++ registerLabel r
  let (actions, wires) ← (do
    let mut actions := #[]
    for ⟨_, r⟩ in registers do
      let rhs ← expression inputLabel regName (c.next r)
      actions := actions.push s!"  always @(posedge clk) {regName r} <= {rhs};"
    for ⟨_, o⟩ in outputs do
      let rhs ← expression inputLabel regName (c.output o)
      actions := actions.push s!"  assign {outputLabel o} = {rhs};"
    return actions : Render _).run {}
  let ports := #["input wire clk"] ++
    inputs.map (fun ⟨w,i⟩ => s!"input wire {widthPrefix w}{inputLabel i}") ++
    outputs.map (fun ⟨w,o⟩ => s!"output wire {widthPrefix w}{outputLabel o}")
  let regs := registers.map fun ⟨w,r⟩ => s!"  reg {widthPrefix w}{regName r};"
  return "`default_nettype none\n" ++ s!"module {name}(" ++
    String.intercalate ",\n  " ports.toList ++ ");\n" ++
    String.intercalate "\n" (regs ++ wires.lines ++ actions).toList ++
    "\nendmodule\n`default_nettype wire\n"

def registers : Array (Sigma Register) :=
  (Streaming.Core.registers 1).map (fun ⟨w,r⟩ => ⟨w,.base r⟩) ++
  #[⟨3,.mode⟩,⟨12,.age⟩,⟨9,.timer⟩,⟨1,.level⟩,⟨4,.sample⟩,
    ⟨1,.previous⟩,⟨3,.ones⟩,⟨7,.consumed⟩,⟨16,.header⟩,⟨16,.crc⟩]

def registerLabel : {w : Nat} → Register w → String
  | _, .base r => Streaming.Core.registerLabel r
  | _, .mode => "usb_mode"
  | _, .age => "usb_age"
  | _, .timer => "usb_timer"
  | _, .level => "usb_level"
  | _, .sample => "usb_sample"
  | _, .previous => "usb_previous"
  | _, .ones => "usb_ones"
  | _, .consumed => "usb_consumed"
  | _, .header => "usb_header"
  | _, .crc => "usb_crc"

def coreText : Except String String := moduleText "pinwheel_usb_low_speed_core_d2"
  circuit Streaming.Core.inputs registers Streaming.Core.outputs
  Streaming.Core.inputLabel registerLabel Streaming.Core.outputLabel

def frontendText : Except String String := moduleText "pinwheel_streaming_quad_frontend"
  Streaming.Frontend.circuit Streaming.Frontend.inputs Streaming.Frontend.registers
  Streaming.Frontend.outputs Streaming.Frontend.inputLabel Streaming.Frontend.registerLabel
  Streaming.Frontend.outputLabel

end Pinwheel.Hardware.USB
