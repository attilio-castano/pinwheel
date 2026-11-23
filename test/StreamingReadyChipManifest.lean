import Pinwheel.Hardware.StreamingReady.ChipManifest
import Lean

/-! Write the chip manifest for the sampled-ready Tiny Tapeout top.

Every field except `targets` is computed from Lean definitions. Theorem names
are written with double backticks, so this file stops compiling if one is
renamed or removed.

    lake env lean -DwarningAsError=true --run test/StreamingReadyChipManifest.lean [OUT] [ADDR_BITS]
-/

open Lean Pinwheel.Hardware Pinwheel.Hardware.StreamingReady ChipManifest

private def port (p : Wiring.Port) : Json :=
  Json.mkObj [("name", toJson p.name), ("width", toJson p.width),
    ("direction", toJson (if p.input then "input" else "output"))]

private def wire (inputSide : Bool) (x : Wire) : Json :=
  let pad := Json.mkObj [("port", toJson x.pad), ("bit", toJson x.padBit)]
  let signal := Json.mkObj [("port", toJson x.signal), ("bit", toJson x.signalBit)]
  if inputSide then Json.mkObj [("pad", pad), ("drives", signal)]
  else Json.mkObj [("signal", signal), ("drives", pad)]

private def theorems : List Name :=
  [``labels_match_interface, ``inputWires_canonical, ``outputWires_canonical, ``zeroBits_canonical,
   ``initialize_canonical, ``input_bit, ``pad_bit, ``release_state_bits,
   ``TinyWiring.Certificate.step_eq, ``TinyWiring.Certificate.observe_eq,
   ``programClocks_over_target, ``Pinwheel.Program.StreamingCANClock.captured,
   ``Pinwheel.Program.StreamingEthernetClock.phyClock]

def manifest (a : Nat) : Json :=
  let top := TinyWiring.canonical a
  let package := Wiring.canonical a
  let rows := census a
  Json.mkObj [
    ("schema", toJson "pinwheel.chip-manifest.v1"),
    ("generator", toJson "test/StreamingReadyChipManifest.lean"),
    ("top", toJson top.name),
    ("addr_bits", toJson a),
    ("depth", toJson (2 ^ a)),
    ("clock", toJson top.engineClock),
    ("hierarchy", Json.mkObj [
      ("top", toJson top.name),
      ("instances", Json.arr #[Json.mkObj [("name", toJson top.engineName),
        ("module", toJson top.engineKind),
        ("instances", Json.arr (package.instances.map fun (n, m) =>
          Json.mkObj [("name", toJson n), ("module", toJson m)]).toArray)]])]),
    ("top_ports", Json.arr (TinyWiring.interface.map port).toArray),
    ("engine_ports", Json.arr (Wiring.interface.map port).toArray),
    ("pins", Json.mkObj [
      ("inputs", Json.arr ((inputWires top).map (wire true)).toArray),
      ("outputs", Json.arr ((outputWires top).map (wire false)).toArray),
      ("zero_outputs", Json.mkObj (pads.map fun pad =>
        (padLabel pad, toJson (zeroBits top pad)))),
      ("enable", Json.mkObj [
        ("inputs", toJson ["ena", "rst_n"]),
        ("initialize", toJson "high unless ena and rst_n are both high"),
        ("outputs", toJson "all pads zero unless ena and rst_n are both high")])]),
    ("state", Json.mkObj [
      ("modules", Json.arr (rows.map fun r => Json.mkObj [("module", toJson r.module),
        ("registers", toJson r.registers), ("bits", toJson r.bits)]).toArray),
      ("bits", toJson (stateBits a))]),
    ("targets", Json.mkObj [
      ("declared_not_proved", toJson true),
      ("tiles", toJson targets.tiles),
      ("clock_period_ns", toJson targets.clockPeriodNs),
      ("max_core_hz", toJson targetMaxHz)]),
    ("program_clocks", Json.arr (programClocks.map fun p => Json.mkObj [
      ("program", toJson p.program), ("core_hz", toJson p.coreHz), ("bit_rate", toJson p.bitRate),
      ("cycles_per_bit", toJson p.cyclesPerBit), ("skew_samples", toJson p.skewSamples),
      ("within_target", toJson p.withinTarget)]).toArray),
    ("lean_theorems", toJson (theorems.map toString))]

def main (args : List String) : IO Unit := do
  let out := args.headD "build/chip-manifest/streaming-ready-d2.json"
  let a := (args[1]?.getD (toString releaseAddrBits)).toNat?.getD releaseAddrBits
  unless a == 1 || a == 2 do throw (IO.userError "qualified buffer address width must be 1 or 2")
  if let some dir := (System.FilePath.mk out).parent then IO.FS.createDirAll dir
  IO.FS.writeFile out ((manifest a).pretty ++ "\n")
  IO.println s!"{(TinyWiring.canonical a).name}: {(inputWires (TinyWiring.canonical a)).length} input wires, \
    {(outputWires (TinyWiring.canonical a)).length} output wires, {stateBits a} state bits -> {out}"
