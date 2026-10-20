import Pinwheel.Hardware.Buffered.ArtifactPackageSession

/-! Conditional digital interpretation of the frozen TinyTapeout pin adapter.
The actual wrapper artifact still requires its independent wiring certificate.
One step means one positive clock edge; immediate pad masking is combinational.
No asynchronous sampling, pad-cell or electrical memory law is inferred. -/
namespace Pinwheel.Hardware.Buffered.ArtifactTinyTapeout
open Pinwheel.Hardware

structure Pins where
  ui : BitVec 8 := 0
  uio : BitVec 8 := 0
  ena : Bool := true
  rstN : Bool := true
  deriving DecidableEq, Repr

def Pins.active (p : Pins) : Bool := p.ena && p.rstN

def Pins.enginePins (p : Pins) : SerialPackage.Pins :=
  ⟨!p.active, p.ui.getLsbD 1, p.ui.getLsbD 2, p.ui.getLsbD 0, p.ui.extractLsb' 3 2⟩

def encode (p : SerialPackage.Pins) : Pins :=
  ⟨(0#3) ++ (p.rawInputs ++ (BitVec.ofBool p.mosi ++
    (BitVec.ofBool p.sck ++ BitVec.ofBool p.csn))), 0, true, !p.cold⟩

private theorem encode_fields : ∀ cold sck mosi csn : Bool, ∀ raw : BitVec 2,
    (encode ⟨cold,sck,mosi,csn,raw⟩).enginePins = ⟨cold,sck,mosi,csn,raw⟩ := by
  decide +kernel

theorem enginePins_encode (p : SerialPackage.Pins) : (encode p).enginePins = p := by
  cases p
  exact encode_fields _ _ _ _ _
  done

structure Pads where
  uo : BitVec 8
  uio : BitVec 8
  oe : BitVec 8
  deriving DecidableEq, Repr

def pads (p : Pins) (status : Values SerialPackage.Output) : Pads :=
  if p.active then
    ⟨((status .busy) ++ ((status .ready) ++ (status .miso))).setWidth 8,
      (status .levels).setWidth 8, (status .enabled).setWidth 8⟩
  else ⟨0,0,0⟩

def step {M : Type} (components : ArtifactPackage.Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M) (p : Pins) :
    ArtifactPackage.State M := s.step components memory p.enginePins

def observe {M : Type} (components : ArtifactPackage.Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M) (p : Pins) : Pads :=
  pads p (s.observe components memory p.enginePins)

def referenceObserve (s : SerialPackage.State) (p : Pins) : Pads :=
  pads p (s.observe p.enginePins)

def run {M : Type} (components : ArtifactPackage.Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M) (pins : List Pins) :
    ArtifactPackage.State M := s.run components memory (pins.map Pins.enginePins)

theorem view_step {M : Type} {components : ArtifactPackage.Components}
    (correct : ArtifactPackage.Correct components) (memory : Memory.SinglePort.Contract M 6 64)
    (s : ArtifactPackage.State M) (p : Pins) :
    (step components memory s p).view memory = (s.view memory).step p.enginePins :=
  s.view_step correct memory p.enginePins

theorem view_observe {M : Type} {components : ArtifactPackage.Components}
    (correct : ArtifactPackage.Correct components) (memory : Memory.SinglePort.Contract M 6 64)
    (s : ArtifactPackage.State M) (p : Pins) :
    observe components memory s p = referenceObserve (s.view memory) p :=
  congrArg (pads p) (funext fun _ => funext fun output => s.view_observe correct memory p.enginePins output)

theorem view_run {M : Type} {components : ArtifactPackage.Components}
    (correct : ArtifactPackage.Correct components) (memory : Memory.SinglePort.Contract M 6 64)
    (s : ArtifactPackage.State M) (pins : List Pins) :
    (run components memory s pins).view memory = (s.view memory).run (pins.map Pins.enginePins) :=
  s.view_run correct memory _

theorem masked {M : Type} (components : ArtifactPackage.Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M) (p : Pins)
    (inactive : p.active = false) : observe components memory s p = ⟨0,0,0⟩ := by
  simp only [observe, pads, inactive, Bool.false_eq_true, ↓reduceIte]
  done

theorem uio_unobserved {M : Type} (components : ArtifactPackage.Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M) (p : Pins)
    (unused : BitVec 8) :
    step components memory s {p with uio := unused} = step components memory s p ∧
      observe components memory s {p with uio := unused} = observe components memory s p := ⟨rfl,rfl⟩

theorem encoded_run {M : Type} (components : ArtifactPackage.Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M)
    (pins : List SerialPackage.Pins) :
    run components memory s (pins.map encode) = s.run components memory pins := by
  simp only [run, List.map_map, Function.comp_def, enginePins_encode]
  change s.run components memory (pins.map id) = s.run components memory pins
  rw [List.map_id]
  done

end Pinwheel.Hardware.Buffered.ArtifactTinyTapeout
