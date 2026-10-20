import Pinwheel.Hardware.Buffered.SerialWireTransaction

/-! Deterministic sampled-pin inhabitants of the universal wire witnesses.
Each bit uses one low and one high sample. Live controller status is arbitrary;
MOSI read bits are unrelated to the MISO receipt being observed. -/
namespace Pinwheel.Hardware.Buffered.SerialWire
open Pinwheel.Hardware Serial.Frames
set_option maxRecDepth 4096

def selected (raw : BitVec 2) (clock bit : Bool) : SerialPackage.Pins :=
  {sck := clock,mosi := bit,csn := false,rawInputs := raw}
def idle (raw : BitVec 2) : SerialPackage.Pins := {rawInputs := raw}

def bitSamples (raw : BitVec 2) : List Bool → List SerialPackage.Pins
  | [] => []
  | bit :: rest => selected raw false bit :: selected raw true bit :: bitSamples raw rest

theorem bitSamples_bits (before : SerialPackage.State) (raw : BitVec 2) (bits : List Bool) :
    IsBits bits (before.frontendInputs (bitSamples raw bits)) := by
  induction bits generalizing before with
  | nil => exact .nil
  | cons bit rest ih =>
    let low := selected raw false bit
    let high := selected raw true bit
    change IsBits (bit :: rest)
      ([before.inputs low,(before.step low).inputs high] ++
        ((before.step low).step high).frontendInputs (bitSamples raw rest))
    apply IsBits.cons
    · refine ⟨⟨[before.inputs low],(before.step low).inputs high,[],rfl,by simp,?_,?_,rfl,by simp⟩⟩
      · intro input member
        simp only [List.mem_singleton] at member
        subst input
        exact ⟨rfl,rfl,rfl⟩
      · exact ⟨rfl,rfl,rfl⟩
    · exact ih ((before.step low).step high)

def request (before : SerialPackage.State) (available : Available before.record)
    (word : BitVec 160) (raw : BitVec 2 := 0) : Request before where
  word := word
  assert := selected raw false false
  close := idle raw
  samples := bitSamples raw (wordBits word)
  available := available
  low := ⟨rfl,rfl,rfl⟩
  bits := bitSamples_bits (before.step (selected raw false false)) raw (wordBits word)
  idle := ⟨rfl,rfl⟩

def read (before : SerialPackage.State) (raw : BitVec 2 := 0) : Read before where
  assert := selected raw false false
  close := idle raw
  bits := List.replicate 192 false
  samples := bitSamples raw (List.replicate 192 false)
  low := ⟨rfl,rfl,rfl⟩
  wire := bitSamples_bits (before.step (selected raw false false)) raw (List.replicate 192 false)
  idle := ⟨rfl,rfl⟩
  length := by simp

def concrete (before : SerialPackage.State) (available : Available before.record)
    (word : BitVec 160) (raw : BitVec 2 := 0) : Transaction before where
  request := request before available word raw
  dispatch := idle raw
  capture := idle raw
  dispatchIdle := ⟨rfl,rfl⟩
  captureIdle := ⟨rfl,rfl⟩
  read := read ((((request before available word raw).framed.step (idle raw)).step (idle raw))) raw

@[simp] theorem concrete_word (before : SerialPackage.State) (available : Available before.record)
    (word : BitVec 160) (raw : BitVec 2) : (concrete before available word raw).request.word = word := rfl

theorem concrete_available (before : SerialPackage.State) (available : Available before.record)
    (word : BitVec 160) (raw : BitVec 2) : Available (concrete before available word raw).after.record :=
  (concrete before available word raw).exact.1

theorem bitSamples_length (raw : BitVec 2) (bits : List Bool) :
    (bitSamples raw bits).length = 2*bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [bitSamples,List.length_cons,ih]; omega

theorem concrete_length (before : SerialPackage.State) (available : Available before.record)
    (word : BitVec 160) (raw : BitVec 2) : (concrete before available word raw).pins.length = 710 := by
  simp [Transaction.pins,Request.pins,Read.pins,concrete,request,read,bitSamples_length,wordBits_length]

end Pinwheel.Hardware.Buffered.SerialWire
