import Pinwheel.Hardware.Storage.DenseEmit
import Pinwheel.Compile.I2CLoopCorrectness

namespace Pinwheel.Hardware.Storage.Repetition

/-- Bounded two-byte/four-phase layout. The four bytes are start, byte span,
bit-body span, and STOP address. They remain physically stored and validated. -/
structure Image where
  templates : Vector (BitVec 64) 15
  bytes : Vector (BitVec 8) 2
  descriptors : Vector (BitVec 8) 4

structure Location where
  template : BitVec 4
  byte : BitVec 1
  bit : BitVec 3
  serial : Bool
  ackCapture : Bool
  ackFinish : Bool
  padding : Bool

def locate (m : Image) (pc : BitVec 8) : Location :=
  let start := m.descriptors[0]
  let span := m.descriptors[1]
  let bits := m.descriptors[2]
  let stop := m.descriptors[3]
  let offset := pc - start
  let second := !(offset.toNat < span.toNat)
  let within := if second then offset - span else offset
  let body := !(pc.toNat < start.toNat) && pc.toNat < stop.toNat
  let serial := body && within.toNat < bits.toNat
  { template := if pc.toNat < start.toNat then pc.extractLsb' 0 4
      else if pc.toNat < stop.toNat then
        if within.toNat < bits.toNat then ((0#2) ++ within.extractLsb' 0 2) - 14
        else ((0#2) ++ (within - bits).extractLsb' 0 2) - 10
      else (pc - stop).extractLsb' 0 4 - 6
    byte := BitVec.ofBool second
    bit := ~~~within.extractLsb' 2 3
    serial := serial
    ackCapture := body && within == bits - 254
    ackFinish := body && within == bits - 253 && second
    padding := !(pc.toNat < (stop - 251).toNat) }

def patch (word : BitVec 64) (m : Image) (l : Location) : BitVec 64 :=
  let word := if l.serial then word.extractLsb' 8 56 ++
    ~~~((m.bytes[l.byte.toNat]).extractLsb' l.bit.toNat 1) ++ word.extractLsb' 0 7 else word
  let word := if l.ackCapture then word.extractLsb' 38 26 ++ l.byte ++ word.extractLsb' 0 37 else word
  let word := if l.ackFinish then (0#23) ++ word.extractLsb' 0 41 else word
  if l.padding then 4 else word

def read (m : Image) (pc : BitVec 8) : BitVec 64 :=
  let l := locate m pc
  patch (if h : l.template.toNat < 15 then m.templates[l.template.toNat] else 4) m l

def compile (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request) : Image :=
  let p := Execution.widenProgram (Compile.I2C.program cfg ⟨0, 0⟩)
  let locations : Vector Nat 15 := #v[0, 1, 2, 3, 4, 5, 34, 35, 36, 37, 74, 75, 76, 77, 78]
  {templates := Vector.ofFn fun k => Execution.encode (p.fetch (Fin.ofNat 256 locations[k.val]))
   bytes := #v[BitVec.ofNat 8 (r.address.val * 2), r.data]
   descriptors := #v[2, 36, 32, 74]}

def words (m : Image) : Execution.Words := Vector.ofFn fun pc => read m (BitVec.ofFin pc)

/-- This bounded backend is accepted only with exact lookup equality. It is not
a general compiler for arbitrary nested counted programs. -/
def lower (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request) :
    Option {m : Image // words m = Execution.imageWords (Execution.widenProgram (Compile.I2C.program cfg r))} :=
  let m := compile cfg r
  if h : words m = Execution.imageWords (Execution.widenProgram (Compile.I2C.program cfg r)) then some ⟨m, h⟩ else none

def store (m : Image) (p : Execution.Image) : Engine.Reactive.Fetch.Store 255 15 :=
  ⟨fun pc => Execution.decode (read m (BitVec.ofFin pc)), p.idle, p.last⟩

theorem store_agrees (m : Image) (p : Execution.Image) (h : words m = Execution.imageWords p) :
    Engine.Reactive.Fetch.Agrees (store m p) p := by
  constructor
  · intro pc
    have hw := congrArg (fun v : Execution.Words => v[pc.val]) h
    simp only [words, Execution.imageWords, Vector.getElem_ofFn] at hw
    simpa only [store, hw, Vector.getElem_map, Engine.Reactive.Program.fetch] using Execution.decode_encode (p.fetch pc)
  · rfl
  · rfl
  done

theorem run_eq (m : Image) (p : Execution.Image) (h : words m = Execution.imageWords p)
    (s : Engine.Reactive.State 255 15) (incoming : Nat → Engine.Reactive.Inputs) (n : Nat) :
    Engine.Reactive.Fetch.run (store m p) s incoming n = Engine.Reactive.run p s incoming n := by
  exact Engine.Reactive.Fetch.run_eq _ _ (store_agrees m p h) s incoming n
  done

end Pinwheel.Hardware.Storage.Repetition
