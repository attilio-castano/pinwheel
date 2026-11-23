import Pinwheel.Hardware.StreamingReady.TinyWiring
import Pinwheel.Hardware.StreamingReady.CoreEmit
import Pinwheel.Hardware.Streaming.FrontendEmit

/-! A machine-readable description of the sampled-ready Tiny Tapeout top.

The pin table is not typed by hand: `inputWires` and `outputWires` probe the
same `TinyWiring.canonical` expressions that the package refinement proofs use,
one public bit at a time. `input_bit` and `pad_bit` prove that the probed table
determines every engine input bit and every output pad bit, for all pin values
and engine outputs. The register census reuses the emitter enumerations.

`Targets` are declared design intentions (tile allocation, clock period). They
are recorded once here so other files can be checked against them; nothing in
this module proves that the physical layout meets them. -/
namespace Pinwheel.Hardware.StreamingReady.ChipManifest
open Pinwheel.Hardware

/-! ## Signal names -/

/-- Engine inputs that public pads drive, in `Wiring.interface` order. -/
def physicalPorts : List (Sigma Wiring.Physical) :=
  [⟨1, .initialize⟩, ⟨1, .csn⟩, ⟨1, .sck⟩, ⟨4, .mosi⟩, ⟨2, .rawInputs⟩]

def physicalLabel : Wiring.Physical w → String
  | .initialize => "initialize" | .csn => "csn" | .sck => "sck"
  | .mosi => "mosi" | .rawInputs => "raw_inputs"

/-- Engine outputs that reach public pads, in `Wiring.interface` order. -/
def outputPorts : List (Sigma Package.Output) :=
  [⟨4, .miso⟩, ⟨1, .ready⟩, ⟨1, .busy⟩, ⟨3, .levels⟩, ⟨3, .enabled⟩]

def outputLabel : Package.Output w → String
  | .miso => "miso" | .ready => "ready" | .busy => "busy"
  | .levels => "levels" | .enabled => "enabled"

def outputIndex : Package.Output w → Nat
  | .miso => 0 | .ready => 1 | .busy => 2 | .levels => 3 | .enabled => 4

/-- The labels and widths above are exactly the package's declared ports. -/
theorem labels_match_interface :
    (physicalPorts.map fun ⟨w, p⟩ => (⟨physicalLabel p, w, true⟩ : Wiring.Port)) ++
      (outputPorts.map fun ⟨w, o⟩ => (⟨outputLabel o, w, false⟩ : Wiring.Port)) =
    Wiring.interface.filter (·.name != "clk") := by
  decide

def padLabel : TinyWiring.Pad → String
  | .uo => "uo_out" | .uio => "uio_out" | .oe => "uio_oe"

def pads : List TinyWiring.Pad := [.uo, .uio, .oe]

/-! ## Probed pin table -/

/-- One public bit connected to one engine bit by a plain wire. For inputs the
pad drives the signal; for outputs the signal drives the pad. -/
structure Wire where
  pad : String
  padBit : Nat
  signal : String
  signalBit : Nat
  deriving DecidableEq, Repr

/-- Enabled and out of reset; every other public input low. -/
def activePins : TinyWiring.Pins := {}

def oneHot8 (k : Nat) : BitVec 8 := BitVec.ofNat 8 (2 ^ k)

def probeInputs (d : TinyWiring.Description) (pad : String)
    (set : BitVec 8 → TinyWiring.Pins) : List Wire :=
  let base := d.enginePins activePins
  (List.range 8).flatMap fun k =>
    let hit := d.enginePins (set (oneHot8 k))
    physicalPorts.flatMap fun ⟨w, port⟩ =>
      (List.range w).filterMap fun j =>
        if (port.eval hit).getLsbD j != (port.eval base).getLsbD j then
          some ⟨pad, k, physicalLabel port, j⟩
        else none

def inputWires (d : TinyWiring.Description) : List Wire :=
  probeInputs d "ui_in" (fun v => {ui := v}) ++ probeInputs d "uio_in" (fun v => {uio := v})

def oneHotOutput (o : Package.Output v) (j : Nat) : Values Package.Output :=
  fun {w} q => if outputIndex q = outputIndex o then BitVec.ofNat w (2 ^ j) else 0

def outputWires (d : TinyWiring.Description) : List Wire :=
  outputPorts.flatMap fun ⟨w, o⟩ => (List.range w).flatMap fun j =>
    pads.flatMap fun pad => (List.range 8).filterMap fun k =>
      if (d.pads activePins (oneHotOutput o j) pad).getLsbD k &&
          !(d.pads activePins (fun _ => 0) pad).getLsbD k then
        some ⟨padLabel pad, k, outputLabel o, j⟩
      else none

/-- Pad bits that no engine bit drives and that stay low even with every
engine output high. For the canonical top, `pad_bit` proves them zero. -/
def zeroBits (d : TinyWiring.Description) (pad : TinyWiring.Pad) : List Nat :=
  (List.range 8).filter fun k =>
    !(outputWires d).any (fun x => x.pad == padLabel pad && x.padBit == k) &&
      !(d.pads activePins (fun {w} _ => BitVec.allOnes w) pad).getLsbD k

/-! ## The table for the canonical top

These literals are what the manifest records. Each equation is checked by the
kernel against the probe of the actual `canonical` expressions. -/

def expectedInputs : List Wire :=
  [⟨"ui_in", 0, "csn", 0⟩, ⟨"ui_in", 1, "sck", 0⟩, ⟨"ui_in", 2, "mosi", 0⟩,
   ⟨"ui_in", 3, "raw_inputs", 0⟩, ⟨"ui_in", 4, "raw_inputs", 1⟩,
   ⟨"ui_in", 5, "mosi", 1⟩, ⟨"ui_in", 6, "mosi", 2⟩, ⟨"ui_in", 7, "mosi", 3⟩]

def expectedOutputs : List Wire :=
  [⟨"uo_out", 0, "miso", 0⟩, ⟨"uo_out", 1, "miso", 1⟩, ⟨"uo_out", 2, "miso", 2⟩,
   ⟨"uo_out", 3, "miso", 3⟩, ⟨"uo_out", 4, "ready", 0⟩, ⟨"uo_out", 5, "busy", 0⟩,
   ⟨"uio_out", 0, "levels", 0⟩, ⟨"uio_out", 1, "levels", 1⟩, ⟨"uio_out", 2, "levels", 2⟩,
   ⟨"uio_oe", 0, "enabled", 0⟩, ⟨"uio_oe", 1, "enabled", 1⟩, ⟨"uio_oe", 2, "enabled", 2⟩]

theorem inputWires_canonical (a : Nat) :
    inputWires (TinyWiring.canonical a) = expectedInputs :=
  (by decide : inputWires (TinyWiring.canonical 0) = expectedInputs)

theorem outputWires_canonical (a : Nat) :
    outputWires (TinyWiring.canonical a) = expectedOutputs :=
  (by decide : outputWires (TinyWiring.canonical 0) = expectedOutputs)

theorem zeroBits_canonical (a : Nat) :
    pads.map (zeroBits (TinyWiring.canonical a)) = [[6, 7], [3, 4, 5, 6, 7], [3, 4, 5, 6, 7]] :=
  (by decide : pads.map (zeroBits (TinyWiring.canonical 0)) = _)

/-! ## The table determines the wiring

The probe alone shows only that each listed bit is connected. These theorems
show the converse for every pin value: no other public bit influences an engine
input, and no other engine bit (or constant one) reaches a pad. -/

/-- The value on a named public input pad. Other names read as zero. -/
def inputPad (p : TinyWiring.Pins) : String → BitVec 8
  | "ui_in" => p.ui | "uio_in" => p.uio | _ => 0

/-- The bit an engine signal receives under a wire table, or zero if unlisted. -/
def inputBit (wires : List Wire) (p : TinyWiring.Pins) (signal : String) (j : Nat) : Bool :=
  match wires.find? (fun x => x.signal == signal && x.signalBit == j) with
  | some x => (inputPad p x.pad).getLsbD x.padBit
  | none => false

/-- The value of a named engine output bit. Other names read as zero. -/
def outputBit (e : Values Package.Output) : String → Nat → Bool
  | "miso", j => (e .miso).getLsbD j | "ready", j => (e .ready).getLsbD j
  | "busy", j => (e .busy).getLsbD j | "levels", j => (e .levels).getLsbD j
  | "enabled", j => (e .enabled).getLsbD j | _, _ => false

/-- The bit a pad shows under a wire table, or zero if unlisted. -/
def padBit (wires : List Wire) (e : Values Package.Output) (pad : String) (k : Nat) : Bool :=
  match wires.find? (fun x => x.pad == pad && x.padBit == k) with
  | some x => outputBit e x.signal x.signalBit
  | none => false

theorem enginePins_canonical (a : Nat) (p : TinyWiring.Pins) :
    (TinyWiring.canonical a).enginePins p =
      ⟨~~~(p.ena &&& p.rstN), p.ui.extractLsb' 0 1, p.ui.extractLsb' 1 1,
       p.ui.extractLsb' 5 3 ++ p.ui.extractLsb' 2 1, p.ui.extractLsb' 3 2⟩ := rfl

/-- The engine is held in initialization unless `ena` and `rst_n` are both high. -/
theorem initialize_canonical (a : Nat) (p : TinyWiring.Pins) :
    ((TinyWiring.canonical a).enginePins p).initialize = ~~~(p.ena &&& p.rstN) := rfl

/-- Every bit of every other engine input is the public bit the table names. -/
theorem input_bit (a : Nat) (p : TinyWiring.Pins) (port : Wiring.Physical w)
    (h : physicalLabel port ≠ "initialize") (j : Nat) (hj : j < w) :
    (port.eval ((TinyWiring.canonical a).enginePins p)).getLsbD j =
      inputBit expectedInputs p (physicalLabel port) j := by
  rw [enginePins_canonical]
  cases port
  · exact absurd rfl h
  all_goals
    rcases j with _|_|_|_|j <;> (try omega) <;>
    simp only [Wiring.Physical.eval, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb'] <;>
    simp [inputBit, expectedInputs, inputPad, physicalLabel]

theorem pads_canonical (a : Nat) (p : TinyWiring.Pins) (e : Values Package.Output) :
    (TinyWiring.canonical a).pads p e .uo =
        (if p.ena &&& p.rstN = 1 then (0 : BitVec 2) ++ (e .busy ++ (e .ready ++ e .miso)) else 0) ∧
    (TinyWiring.canonical a).pads p e .uio =
        (if p.ena &&& p.rstN = 1 then (0 : BitVec 5) ++ e .levels else 0) ∧
    (TinyWiring.canonical a).pads p e .oe =
        (if p.ena &&& p.rstN = 1 then (0 : BitVec 5) ++ e .enabled else 0) :=
  ⟨rfl, rfl, rfl⟩

/-- While `ena` and `rst_n` are high, each pad bit is the engine bit the table
names, or zero if it names none. Otherwise every pad bit is zero. -/
theorem pad_bit (a : Nat) (p : TinyWiring.Pins) (e : Values Package.Output)
    (pad : TinyWiring.Pad) (k : Nat) (hk : k < 8) :
    ((TinyWiring.canonical a).pads p e pad).getLsbD k =
      (p.ena &&& p.rstN == 1 && padBit expectedOutputs e (padLabel pad) k) := by
  obtain ⟨huo, huio, hoe⟩ := pads_canonical a p e
  cases pad <;> simp only [huo, huio, hoe] <;> split <;>
    rcases k with _|_|_|_|_|_|_|_|k <;> (try omega) <;>
    (try simp only [BitVec.getLsbD_append]) <;>
    simp_all [padBit, expectedOutputs, outputBit, padLabel]

/-! ## State census

Taken from the same enumerations that the emitter uses to print each module's
registers, so a register added to the circuit but not to the enumeration would
already break emission and RTL read-back. -/

structure ModuleCensus where
  module : String
  registers : Nat
  bits : Nat

def census (a : Nat) : List ModuleCensus :=
  [⟨(Wiring.canonical a).instances.headD ("", "") |>.2,
     Streaming.Frontend.registers.size,
     (Streaming.Frontend.registers.map (·.1)).foldl (· + ·) 0⟩,
   ⟨s!"pinwheel_streaming_ready_core_d{2^a}",
     (Core.registers a).size, ((Core.registers a).map (·.1)).foldl (· + ·) 0⟩]

def stateBits (a : Nat) : Nat := ((census a).map (·.bits)).foldl (· + ·) 0

/-! ## Release selection and declared targets -/

/-- The frozen entry uses buffer address width one, i.e. depth two. -/
def releaseAddrBits : Nat := 1

theorem release_state_bits : stateBits releaseAddrBits = 6039 := by decide +kernel

/-- Declared, not proved: the tile allocation and clock period the physical
implementation is built for. Recorded once so other files can be checked. -/
structure Targets where
  tiles : String
  clockPeriodNs : Nat

def targets : Targets := ⟨"8x4", 20⟩

end Pinwheel.Hardware.StreamingReady.ChipManifest
