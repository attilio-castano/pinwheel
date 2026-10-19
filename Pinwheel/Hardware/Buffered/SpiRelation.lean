import Pinwheel.Hardware.Buffered.SpiPacking
import Pinwheel.Hardware.Buffered.SpiGeometry
import Pinwheel.Hardware.Buffered.SpiInterpreter
import Pinwheel.Hardware.Buffered.SpiCoordinates
import Pinwheel.Hardware.Buffered.SpiCircuit
import Pinwheel.Hardware.Buffered.SpiStart

/-! One admitted compact SPI transfer: an explicit relation between the typed
Buffered source and the actual packed digital circuit. Original payload bits
outside the declared TX length remain a ghost; stopped sampler values are
deliberately abstracted because the source stops sampling on completion. -/
namespace Pinwheel.Hardware.Buffered.SpiRefinement
open Pinwheel.Hardware Pinwheel.Program

def capacity : Transfer.Capacity := ⟨32, 32⟩

/-- Datapath representation includes the exact logical request and diagnostic
prefix. The complete original payload is retained even for a short TX length.
-/
structure Datapath (payload : BitVec 32) (r : Values Reactive.Register)
    (e : Transfer.Execution) : Prop where
  bounded : e.Bounded capacity
  tx : e.request.tx = SpiPacking.txBits payload e.request.tx.length
  txLength : (r .txLength).toNat = e.request.tx.length
  rxCapacity : (r .rxCapacity).toNat = e.request.rxLimit
  consumed : (r .txConsumed).toNat = e.txConsumed
  shifted : r .txData = payload >>> e.txConsumed
  rxLength : (r .rxLength).toNat = e.rx.length
  received : r .rxData = SpiPacking.rxWord e.rx
  generation : (r .generation).toNat = e.request.programGeneration
  transfer : (r .transfer).toNat = e.request.identity.sequence

structure Common (c : SpiSource.Config) (payload : BitVec 32)
    (r : Values Reactive.Register) (s : Program.Buffered.State)
    (e : Transfer.Execution) : Prop where
  geometry : SpiGeometry.Geometry c r
  image : ∀ k, r (.word k) = SpiSource.fullWords c k
  valid : r .valid = 1
  data : Datapath payload r e
  owner : e.request.identity = s.owner
  pins : s.core.pins = ⟨r .levels, r .enabled⟩
  samples : s.core.samples = Vector.replicate 16 false
  scratch : r .scratch = 0

structure Running (c : SpiSource.Config) (payload : BitVec 32)
    (r : Values Reactive.Register) (s : Program.Buffered.State)
    (e : Transfer.Execution) (pc : Program.Buffered.PC) (remaining : Fin 256) : Prop where
  common : Common c payload r s e
  slot : s.buffers.slot = .running e
  control : s.core.control = .active pc remaining
  within : pc.val ≤ SpiCoordinates.bitSpan c
  coordinates : SpiCoordinates.At c pc.val r
  remaining_eq : r .remaining = BitVec.ofNat 8 remaining.val
  retained : r .retained = 0
  first : s.samplerFirst = r .stage1
  second : s.samplerSecond = r .stage2

def stopReason (complete : Bool) : Engine.Reactive.Stop :=
  if complete then .completed else .fault

def outcome (complete : Bool) : Transfer.Outcome :=
  if complete then .complete else .fault

structure Stopped (c : SpiSource.Config) (payload : BitVec 32)
    (r : Values Reactive.Register) (s : Program.Buffered.State)
    (e : Transfer.Execution) (complete : Bool) : Prop where
  common : Common c payload r s e
  slot : s.buffers.slot = .completed ⟨e, outcome complete⟩
  control : s.core.control = .stopped (stopReason complete)
  phase : r .phase = if complete then 5 else 7
  retained : r .retained = 1
  pc : r .pc = 0
  virtualPC : r .virtualPC = 0
  outer : r .outer = 0
  inner : r .inner = 0
  currentControl : r .currentControl = 0
  remaining : r .remaining = 0

/-- Agreement is a reachable invariant established at START and preserved by
clock steps. It is not an assumed equality of the two execution traces. -/
def Related (c : SpiSource.Config) (payload : BitVec 32)
    (r : Values Reactive.Register) (s : Program.Buffered.State) : Prop :=
  (∃ e pc remaining, Running c payload r s e pc remaining) ∨
  (∃ e complete, Stopped c payload r s e complete)

theorem Datapath.sampleTick {payload : BitVec 32} {r : Values Reactive.Register}
    {e : Transfer.Execution} (h : Datapath payload r e) (raw : BitVec 2) :
    Datapath payload (SpiCircuit.sampleTick r raw) e :=
  ⟨h.bounded, h.tx, h.txLength, h.rxCapacity, h.consumed, h.shifted,
    h.rxLength, h.received, h.generation, h.transfer⟩

theorem Datapath.countdownTick {payload : BitVec 32} {r : Values Reactive.Register}
    {e : Transfer.Execution} (h : Datapath payload r e) (raw : BitVec 2) :
    Datapath payload (SpiCircuit.countdownTick r raw) e :=
  ⟨h.bounded, h.tx, h.txLength, h.rxCapacity, h.consumed, h.shifted,
    h.rxLength, h.received, h.generation, h.transfer⟩

theorem Common.sampleTick {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    (h : Common c payload r s e) (raw : BitVec 2) :
    Common c payload (SpiCircuit.sampleTick r raw) s e :=
  ⟨⟨h.geometry.count, h.geometry.virtualSpan, h.geometry.idleLevels, h.geometry.idleEnabled⟩,
    h.image, h.valid, h.data.sampleTick raw, h.owner, h.pins, h.samples, h.scratch⟩

theorem Common.countdownTick {c : SpiSource.Config} {payload : BitVec 32}
    {r : Values Reactive.Register} {s : Program.Buffered.State} {e : Transfer.Execution}
    (h : Common c payload r s e) (raw : BitVec 2) (control : Engine.Reactive.Control 1023) :
    Common c payload (SpiCircuit.countdownTick r raw)
      {s with
        core := {s.core with control}
        samplerFirst := raw
        samplerSecond := s.samplerFirst} e :=
  ⟨⟨h.geometry.count, h.geometry.virtualSpan, h.geometry.idleLevels, h.geometry.idleEnabled⟩,
    h.image, h.valid, h.data.countdownTick raw, h.owner, h.pins, h.samples, h.scratch⟩

end Pinwheel.Hardware.Buffered.SpiRefinement
