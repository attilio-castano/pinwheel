import Pinwheel.Program.StreamingReadyCompile

/-! One autonomous sampled 8N1 receive frame. The Ready instruction set and
hardware remain generic; the serial schedule is a certified source image. -/
namespace Pinwheel.Program.StreamingUART
open Pinwheel.Program.StreamingReady

structure Profile where
  quarterMinusFour : Fin 125
  rxInput : Fin 2 := 0
  deriving DecidableEq, Repr

def Profile.Q (p : Profile) : Nat := p.quarterMinusFour.val + 4

theorem Profile.Q_ge4 (p : Profile) : 4 ≤ p.Q := by unfold Profile.Q; omega
theorem Profile.Q_le128 (p : Profile) : p.Q ≤ 128 := by
  have := p.quarterMinusFour.isLt
  unfold Profile.Q
  omega

def pulseA (p : Profile) : Cell :=
  {lowDuration := ⟨p.Q-3,by have := p.Q_le128; omega⟩,
   highDuration := ⟨p.Q-3,by have := p.Q_le128; omega⟩}

def pulseB (p : Profile) : Cell :=
  {lowDuration := ⟨p.Q-3,by have := p.Q_le128; omega⟩,
   highDuration := ⟨p.Q-2,by have := p.Q_le128; omega⟩}

def cell (p : Profile) : Cell :=
  {lowDuration := ⟨2*p.Q-2,by have := p.Q_le128; omega⟩,
   highDuration := ⟨2*p.Q-1,by have := p.Q_le128; omega⟩,
   receive := true,rxInput := p.rxInput}

def mask (p : Profile) : BitVec 2 := 1#2 <<< p.rxInput.val

def markGuard (p : Profile) : Guard := ⟨mask p,mask p,.unbounded⟩
def startGuard (p : Profile) : Guard := ⟨mask p,0,.unbounded⟩
def checkStart (p : Profile) : Guard := ⟨mask p,0,.misses 0⟩
def checkStop (p : Profile) : Guard := ⟨mask p,mask p,.misses 0⟩

def source (p : Profile) : List Instruction :=
  [.driveWait ⟨0,0⟩ (markGuard p),
   .driveWait ⟨0,0⟩ (startGuard p),
   .pulse (pulseA p),
   .driveWait ⟨0,0⟩ (checkStart p),
   .pulse (pulseB p),
   .stream (cell p) none,
   .pulse (pulseA p),
   .driveWait ⟨0,0⟩ (checkStop p),
   .halt]

theorem supported (p : Profile) : Supported (source p) := by
  simp [Supported,source,supportedFrom,List.countP_cons,Instruction.isStream,
    Instruction.Canonical,Streaming.Cell.PulseCanonical,pulseA,pulseB,
    markGuard,startGuard,checkStart,checkStop,Guard.Canonical]
  done

def image (p : Profile) : Compiled (source p) (Engine.Reactive.Pins.mk 0 0) :=
  ⟨(source p).map encode,supported p,rfl⟩

theorem source_length (p : Profile) : (source p).length = 9 := rfl

theorem image_rows (p : Profile) : (image p).words.length = 9 := rfl

theorem source_fetch (p : Profile) (k : Nat) (within : k < 9) :
    (image p).program.fetch k = (source p)[k]? :=
  (image p).program_fetch k (by simpa only [source_length] using within)

theorem pulseA_fields (p : Profile) :
    (pulseA p).lowDuration.val = p.Q-3 ∧ (pulseA p).highDuration.val = p.Q-3 ∧
    (pulseA p).lowPins = Engine.Reactive.Pins.mk 0 0 ∧
    (pulseA p).highPins = Engine.Reactive.Pins.mk 0 0 := ⟨rfl,rfl,rfl,rfl⟩

theorem pulseB_fields (p : Profile) :
    (pulseB p).lowDuration.val = p.Q-3 ∧ (pulseB p).highDuration.val = p.Q-2 ∧
    (pulseB p).lowPins = Engine.Reactive.Pins.mk 0 0 ∧
    (pulseB p).highPins = Engine.Reactive.Pins.mk 0 0 := ⟨rfl,rfl,rfl,rfl⟩

theorem cell_fields (p : Profile) :
    (cell p).lowDuration.val = 2*p.Q-2 ∧ (cell p).highDuration.val = 2*p.Q-1 ∧
    (cell p).transmit = false ∧ (cell p).receive = true ∧ (cell p).rxInput = p.rxInput ∧
    (cell p).lowPins = Engine.Reactive.Pins.mk 0 0 ∧
    (cell p).highPins = Engine.Reactive.Pins.mk 0 0 := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end Pinwheel.Program.StreamingUART
