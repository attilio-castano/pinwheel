import Lean
import Pinwheel.Program.StreamingUARTFrameStarted

/-! Public theorem-shape obligations. These universally quantify over the
profile, selector, payload, old state, and inactive operands; they are not a
finite enumeration of the received bytes. -/
namespace Pinwheel.Test.StreamingUARTSource
open Pinwheel.Program.StreamingReady
open Pinwheel.Program.StreamingUART
open QuietTiming FrameSamples FrameData Frame

/-- Conventional stable frames are received autonomously at every supported
quarter period, with a real admitted START and sampler arming derived. -/
example (p : Profile) (s : State a) (start : Input) (marks : List Input)
    (payload : BitVec 8) (incoming : Nat → Input)
    (runtime : start.Runtime) (admitted : (start.command == 3 && s.canStart start) = true)
    (count : start.startCount = 8)
    (markQuiet : ∀ i ∈ marks,Quiet i) (markRaw : ∀ i ∈ marks,i.rawInputs = 3) (long : 6 ≤ marks.length)
    (quiet : ∀ n,Quiet (incoming n)) (frame : StableFrame p incoming payload) :
    let finalState := run (image p).program s (start :: (marks ++ clocks incoming 0 (38*p.Q+4)))
    finalState.phase = .completed ∧ Received s.generation (s.transfer+1) payload finalState :=
  admitted_stable_frame p s start marks payload incoming runtime admitted count markQuiet markRaw long quiet frame

/-- Sparse raw sample contracts also suffice; no assumed capture or outcome is
an input to the theorem. There are exactly eight received bits and zero TX bits. -/
example {a : Nat} (p : Profile) (generation transfer : BitVec 16) (payload : BitVec 8)
    (incoming : Nat → Input) (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload)
    (stopHigh : (incoming (38*p.Q)).rawInputs[p.rxInput.val] = true) :
    let finalState := run (image p).program (Arm.armed (a := a) p generation transfer)
      (clocks incoming 0 (38*p.Q+4))
    finalState.phase = .completed ∧ Received generation transfer payload finalState :=
  good_frame_result p generation transfer payload incoming quiet falling startLow samples stopHigh

/-- A bad stop faults one edge before HALT and preserves the same eight-bit
receipt, including the owner and decoded byte. -/
example {a : Nat} (p : Profile) (generation transfer : BitVec 16) (payload : BitVec 8)
    (incoming : Nat → Input) (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload)
    (stopLow : (incoming (38*p.Q)).rawInputs[p.rxInput.val] = false) :
    let finalState := run (image p).program (Arm.armed (a := a) p generation transfer)
      (clocks incoming 0 (38*p.Q+3))
    finalState.phase = .fault ∧ Received generation transfer payload finalState :=
  bad_stop_result p generation transfer payload incoming quiet falling startLow samples stopLow

/-- False-start validation occurs at half a bit and produces no RX sample. -/
example (p : Profile) (s : State a) (start : Input) (marks : List Input)
    (incoming : Nat → Input)
    (runtime : start.Runtime) (admitted : (start.command == 3 && s.canStart start) = true)
    (count : start.startCount = 8)
    (markQuiet : ∀ i ∈ marks,Quiet i) (markRaw : ∀ i ∈ marks,i.rawInputs = 3) (long : 6 ≤ marks.length)
    (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startHigh : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = true) :
    let finalState := run (image p).program s (start :: (marks ++ clocks incoming 0 (2*p.Q+3)))
    finalState.phase = .fault ∧ finalState.rx.count.val = 0 ∧ finalState.rxProduced = 0#16 ∧
      finalState.txConsumed = 0#16 ∧ finalState.remaining = 8#16 ∧
      finalState.generation = s.generation ∧ finalState.transfer = s.transfer+1 :=
  admitted_false_start p s start marks incoming runtime admitted count markQuiet markRaw long quiet falling startHigh

/-- This asymmetric byte distinguishes UART chronology from the raw assembler
word: the latter is 0xa4, while UART decoding returns the original 0x25. -/
example : Pinwheel.Program.Streaming.Packing.rxWord (bits 37#8) = 164#32 ∧ decodeBits (bits 37#8) = 37#8 := by decide +kernel

example (p : Profile) : 16 ≤ 4*p.Q ∧ 4*p.Q ≤ 512 := by
  have := p.Q_ge4
  have := p.Q_le128
  omega

end Pinwheel.Test.StreamingUARTSource

open Lean Elab Command

/-- Include every compiled production declaration and every private proof in
this dependency closure. A public-theorem-only audit would miss definitions. -/
elab "#audit_uart_source" : command => do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name,info) in env.constants.toList do
    let text := name.toString
    if text.startsWith "Pinwheel." || text.startsWith "_private.Pinwheel." then
      declarations := declarations+1
      if info.isTheorem then theorems := theorems+1
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax =>
        ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
      unless unexpected.isEmpty do
        throwError "Unapproved axioms in {name}: {unexpected}"
  if declarations == 0 || theorems == 0 then throwError "Empty UART proof audit"
  logInfo m!"UART source audit: {declarations} declarations, {theorems} theorems; standard axioms only."

#audit_uart_source
