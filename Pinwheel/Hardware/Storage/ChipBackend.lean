import Pinwheel.Hardware.Chip
import Pinwheel.Hardware.Storage.OnePortEmit
import Pinwheel.Hardware.Storage.TwoPortEmit

/-! The whole chip around a proved fetch-policy backend: the theorem from pins
to the reference machine, and the emitted Tiny Tapeout module. -/
namespace Pinwheel.Hardware.Storage.Backend.Policy
open Loader

variable {p : Nat} {σ : Type} {X : Nat → Type} {P : FetchPolicy.Policy p σ}

/-- **From the pins to the reference machine.** For every pin history, whatever
the samplers and the receiver held at the start: the chip's pins show what the
atomic reference machine shows on the history the serial loader feeds it, edge
for edge — on histories whose fed inputs satisfy the policy's rule. -/
theorem chip_trace (Z : Realization P X) (C : FetchPolicy.Correct P) (R : Rules C) (s : State σ)
    (h : Valid C s) (x : Chip.State) (pins : List Chip.Pins)
    (hr : ∀ e ∈ Chip.history x pins, R.Rule e.1) :
    ((Chip.netlist Z.netlist).componentOf Chip.Pins.values).trace
        (Chip.values (s.values Z.values) x) pins =
      (referenceComponent.pairTrace s.reference.machine (Chip.history x pins)).map Chip.shownEdge := by
  rw [Chip.trace_eq]
  congr 1
  exact (completeRefinement Z C R).pairTrace_eq _ _ (related Z C R s h) _ hr

/-! ### Emission -/

def chipInputs : Array (Sigma Chip.Pin) := #[⟨8, .uiIn⟩, ⟨8, .uioIn⟩, ⟨1, .ena⟩, ⟨1, .rstN⟩]

def chipOutputs : Array (Sigma Chip.Output) := #[⟨8, .uoOut⟩, ⟨8, .uioOut⟩, ⟨8, .uioOe⟩]

def chipInputLabel : {w : Nat} → Chip.Pin w → String
  | _, .uiIn => "ui_in" | _, .uioIn => "uio_in" | _, .ena => "ena" | _, .rstN => "rst_n"

def chipOutputLabel : {w : Nat} → Chip.Output w → String
  | _, .uoOut => "uo_out" | _, .uioOut => "uio_out" | _, .uioOe => "uio_oe"

def serialRegisters : Array (Sigma Serial.Register) :=
  #[⟨1, .sckPrev⟩, ⟨7, .count⟩, ⟨64, .shift⟩, ⟨3, .command⟩, ⟨1, .fire⟩]

def serialLabel : {w : Nat} → Serial.Register w → String
  | _, .sckPrev => "serial_sck_prev" | _, .count => "serial_count" | _, .shift => "serial_shift"
  | _, .command => "serial_command" | _, .fire => "serial_fire"

def serialInputs : Array (Sigma Serial.Input) :=
  #[⟨1, .init⟩, ⟨1, .sck⟩, ⟨1, .mosi⟩, ⟨1, .csn⟩, ⟨2, .incoming⟩]

def serialInputLabel : {w : Nat} → Serial.Input w → String
  | _, .init => "init" | _, .sck => "sck" | _, .mosi => "mosi" | _, .csn => "csn"
  | _, .incoming => "incoming"

def sampledRegisterList : Array (Sigma (Feeder.Sampled Serial.Input)) :=
  serialInputs.map (fun ⟨w, q⟩ => ⟨w, .first q⟩) ++ serialInputs.map (fun ⟨w, q⟩ => ⟨w, .second q⟩)

def sampledRegisterLabel : {w : Nat} → Feeder.Sampled Serial.Input w → String
  | _, .first q => "pin_first_" ++ serialInputLabel q
  | _, .second q => "pin_second_" ++ serialInputLabel q

/-- The core's registers, the receiver's, the samplers'. -/
def chipRegisters (extra : Array (Sigma X)) : Array (Sigma (Chip.Register (Register X))) :=
  (registers extra).map (fun ⟨w, r⟩ => ⟨w, .inner (.inner (.inner r))⟩) ++
    serialRegisters.map (fun ⟨w, r⟩ => ⟨w, .inner (.inner (.extra r))⟩) ++
    sampledRegisterList.map (fun ⟨w, r⟩ => ⟨w, .inner (.extra r)⟩)

def chipRegisterLabel (label : {w : Nat} → X w → String) :
    {w : Nat} → Chip.Register (Register X) w → String
  | _, .inner (.inner (.inner r)) => registerLabel label r
  | _, .inner (.inner (.extra r)) => serialLabel r
  | _, .inner (.extra r) => sampledRegisterLabel r
  | _, .extra r => nomatch r

/-- The Tiny Tapeout user module: its ports are the template's. -/
def chipText (name : String) (n : Netlist (Register X) Machine.Output Machine.Input)
    (extra : Array (Sigma X)) (label : {w : Nat} → X w → String) : Except String String :=
  Hardware.Netlist.moduleText name (Chip.netlist n) chipInputs (chipRegisters extra) chipOutputs
    chipInputLabel (chipRegisterLabel label) chipOutputLabel

end Pinwheel.Hardware.Storage.Backend.Policy

namespace Pinwheel.Hardware.Storage.Backend
open Loader

/-- The one-port chip: the reference machine from the pins, on ready programs. -/
theorem OnePort.chip_trace (s : OnePort.State) (h : OnePort.Valid s) (x : Chip.State)
    (pins : List Chip.Pins) (hr : ∀ e ∈ Chip.history x pins, OnePort.Rule e.1) :
    ((Chip.netlist OnePort.netlist).componentOf Chip.Pins.values).trace
        (Chip.values (s.values OnePort.values) x) pins =
      (referenceComponent.pairTrace s.reference.machine (Chip.history x pins)).map Chip.shownEdge :=
  Policy.chip_trace OnePort.realization SinglePort.correct OnePort.rules s h x pins hr

/-- The two-port chip: the reference machine from the pins, for every pin history. -/
theorem TwoPort.chip_trace (s : TwoPort.State) (h : TwoPort.Valid s) (x : Chip.State)
    (pins : List Chip.Pins) :
    ((Chip.netlist TwoPort.netlist).componentOf Chip.Pins.values).trace
        (Chip.values (s.values TwoPort.values) x) pins =
      (referenceComponent.pairTrace s.reference.machine (Chip.history x pins)).map Chip.shownEdge :=
  Policy.chip_trace TwoPort.realization Storage.TwoPort.correct TwoPort.rules s h x pins
    (fun _ _ => trivial)

def OnePort.chipText : Except String String :=
  Policy.chipText "tt_um_pinwheel" OnePort.netlist OnePort.extra OnePort.label

def TwoPort.chipText : Except String String :=
  Policy.chipText "tt_um_pinwheel" TwoPort.netlist TwoPort.extra TwoPort.label

end Pinwheel.Hardware.Storage.Backend
