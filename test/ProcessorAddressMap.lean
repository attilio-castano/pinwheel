import Lean
import Pinwheel.Hardware.Processor.AddressMap

open Lean Elab Command
open Pinwheel.Hardware.Processor.AddressMap
open Pinwheel.Hardware.Memory.ByteAccess

namespace ProcessorAddressMapTests

inductive Observation where
  | misaligned | access
  | hit (region word offset : Nat)
  deriving BEq, Repr

def regionNumber : Region → Nat
  | .rom => 0 | .ram => 1 | .gpio => 2 | .timer => 3 | .uart => 4

def observe (l : Layout rw aw) (a : Access) : Observation :=
  match route l a with
  | .error .misaligned => .misaligned
  | .error .access => .access
  | .ok h => .hit (regionNumber h.region) h.wordIndex h.byteOffset

/-- Independent table: byte capacities are powers of two, not library interval
projections. The oracle uses division for alignment and remaining capacity for
the complete footprint check. -/
def table (c : Config rw aw) : Array (Nat × Nat) :=
  #[(0, 2^(rw+2)), (c.ramBase.toNat, 2^(aw+2)),
    (c.gpioBase.toNat, 256), (c.timerBase.toNat, 256), (c.uartBase.toNat, 256)]

def referenceValid (c : Config rw aw) : Bool := Id.run do
  let rows := table c
  for k in [0:rows.size] do
    let (base, bytes) := rows[k]!
    if base / 4 * 4 != base || bytes == 0 || base + bytes > 4294967296 then
      return false
    for j in [0:k] do
      let (other, count) := rows[j]!
      if base < other + count && other < base + bytes then return false
  return true

def reference (c : Config rw aw) (a : Access) : Observation := Id.run do
  let address := a.address.toNat
  let width := if a.kind == .fetch then 4 else
    match a.size with | .byte => 1 | .half => 2 | .word => 4
  if address / width * width != address then return .misaligned
  let rows := table c
  for r in [0:rows.size] do
    let (base, bytes) := rows[r]!
    if address >= base && address < base + bytes && width <= base + bytes - address then
      let permitted := if r == 0 then
          a.kind == .load || (a.kind == .fetch && a.size == .word)
        else if r == 1 then a.kind != .fetch
        else a.kind != .fetch && a.size == .word
      if !permitted then return .access
      return .hit r ((address-base)/4) ((address-base)-4*((address-base)/4))
  return .access

def config (rw aw ram gpio timer uart : Nat) : Config rw aw :=
  ⟨BitVec.ofNat 32 ram, BitVec.ofNat 32 gpio, BitVec.ofNat 32 timer, BitVec.ofNat 32 uart⟩

def checked (c : Config rw aw) : IO (Layout rw aw) :=
  match check c with
  | some l => pure l
  | none => throw (IO.userError s!"Unexpected rejected layout: {repr c}")

def layoutCases : IO Nat := do
  let widths := #[0, 1, 2, 10, 28, 29, 30, 31, 32]
  let bases := #[0, 1, 3, 4, 8, 252, 256, 260, 512, 768, 65536,
    0x40000000, 0x40000100, 0x40000200, 0xffffff00, 0xfffffffc, 0xffffffff]
  let mut checks := 0
  for rw in widths do
    for aw in widths do
      for index in [0:bases.size] do
        let value := bases[index]!
        let cases := #[
          config rw aw value 0x40000000 0x40000100 0x40000200,
          config rw aw 65536 value 0x40000100 0x40000200,
          config rw aw 65536 0x40000000 value 0x40000200,
          config rw aw 65536 0x40000000 0x40000100 value,
          config rw aw value bases[(index+1)%bases.size]!
            bases[(index+3)%bases.size]! bases[(index+7)%bases.size]!]
        for c in cases do
          unless (check c).isSome == referenceValid c do
            throw (IO.userError s!"Layout reference mismatch rw{rw} aw{aw}: {repr c}")
          checks := checks + 1
  return checks

def addresses (c : Config rw aw) : Array Nat := Id.run do
  let mut result := Array.range 1060
  result := result ++ #[0x10000, 0x10001, 0x10002, 0x10003, 0x10004,
    0x80000000, 0xfffffff8, 0xfffffff9, 0xfffffffa, 0xfffffffb,
    0xfffffffc, 0xfffffffd, 0xfffffffe, 0xffffffff]
  for (base, bytes) in table c do
    for center in #[base, base+bytes/2, base+bytes] do
      for delta in [0:20] do
        result := result.push ((center+4294967296+delta-10)%4294967296)
    if bytes <= 256 then
      for index in [0:bytes] do result := result.push (base+index)
  let mut seed := 0x4a291365
  for _ in [0:256] do
    seed := (1664525*seed+1013904223)%4294967296
    result := result.push seed
  return result

def routeCases (c : Config rw aw) : IO Nat := do
  let l ← checked c
  let mut checks := 0
  for address in addresses c do
    for kind in #[Kind.fetch, .load, .store] do
      for size in #[Size.byte, .half, .word] do
        let a : Access := ⟨kind, size, BitVec.ofNat 32 address⟩
        let expected := reference c a
        let actual := observe l a
        unless actual == expected do
          throw (IO.userError s!"Route rw{rw} aw{aw} {repr a}: expected {repr expected}, got {repr actual}")
        if let .ok h := route l a then
          let base := (table c)[regionNumber h.region]!.1
          let bytes := (table c)[regionNumber h.region]!.2
          unless h.wordAddress.toNat == h.wordIndex && h.offset.toNat == h.byteOffset &&
              base+4*h.wordIndex+h.byteOffset == address &&
              h.wordIndex < 2^(h.region.wordWidth rw aw) && h.byteOffset < 4 do
            throw (IO.userError "Successful route truncated a local address")
          for byte in [0:a.bytes] do
            unless base <= address+byte && address+byte < base+bytes && address+byte < 4294967296 do
              throw (IO.userError "Successful route lost a byte of the access footprint")
        checks := checks + 1
  return checks

/-- Retained boundary assertions also guard the oracle's intended policy. -/
def probes : IO Nat := do
  let l := defaultLayout
  let cases : Array (Access × Observation) := #[
    (⟨.fetch, .word, 0⟩, .hit 0 0 0),
    (⟨.fetch, .byte, 1⟩, .misaligned),
    (⟨.fetch, .byte, 0⟩, .access),
    (⟨.load, .byte, 4095⟩, .hit 0 1023 3),
    (⟨.load, .half, 4095⟩, .misaligned),
    (⟨.load, .word, 4096⟩, .access),
    (⟨.store, .byte, 0⟩, .access),
    (⟨.store, .word, 65536⟩, .hit 1 0 0),
    (⟨.fetch, .word, 65536⟩, .access),
    (⟨.load, .byte, 0x40000000⟩, .access),
    (⟨.load, .half, 0x40000001⟩, .misaligned),
    (⟨.store, .word, 0x400000fc⟩, .hit 2 63 0),
    (⟨.load, .word, 0x40000100⟩, .hit 3 0 0),
    (⟨.store, .word, 0x40000200⟩, .hit 4 0 0),
    (⟨.fetch, .word, 0x40000200⟩, .access),
    (⟨.load, .word, 0x80010000⟩, .access),
    (⟨.load, .word, 0xfffffffc⟩, .access),
    (⟨.load, .word, 0xffffffff⟩, .misaligned)]
  for (a, expected) in cases do
    unless observe l a == expected && reference defaultConfig a == expected do
      throw (IO.userError s!"Policy probe failed: {repr a}")
  let top ← checked (config 0 0 0xfffffffc 256 512 768)
  unless observe top ⟨.store, .word, 0xfffffffc⟩ == .hit 1 0 0 &&
      observe top ⟨.load, .byte, 0xffffffff⟩ == .hit 1 0 3 &&
      observe top ⟨.load, .word, (0xffffffff : BitVec 32)+1⟩ == .hit 0 0 0 do
    throw (IO.userError "Top-of-address-space or prior architectural wrapping failed")
  return cases.size+3

example : (check defaultConfig).isSome = true := by decide +kernel
example : (check (config 0 0 4 256 512 768)).isSome = true := by decide +kernel
example : (check (config 0 0 0xfffffffc 256 512 768)).isSome = true := by decide +kernel
example : (check (config 0 0 4 0xffffff00 256 512)).isSome = true := by decide +kernel
example : (check (config 0 0 4 0xffffff04 256 512)).isSome = false := by decide +kernel
example : (check (config 30 0 4 256 512 768)).isSome = false := by decide +kernel
example (l : Layout rw aw) (a : Access) (h k : Hit l a) : h = k := h.unique k
example (l : Layout rw aw) (a : Access) (h : Hit l a) :
    a.address.toNat = l.config.base h.region + 4*h.wordAddress.toNat+h.offset.toNat :=
  h.narrow_reconstruct

end ProcessorAddressMapTests

elab "#audit_address_map" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Processor.AddressMap." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Processor.AddressMap." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty address-map audit"
  logInfo m!"Address map audit: {count} declarations, standard axioms only."

#audit_address_map

def main : IO Unit := do
  let layouts ← ProcessorAddressMapTests.layoutCases
  let mut accesses := 0
  accesses := accesses + (← ProcessorAddressMapTests.routeCases defaultConfig)
  accesses := accesses + (← ProcessorAddressMapTests.routeCases (ProcessorAddressMapTests.config 0 0 4 256 512 768))
  accesses := accesses + (← ProcessorAddressMapTests.routeCases (ProcessorAddressMapTests.config 1 3 8 256 512 768))
  accesses := accesses + (← ProcessorAddressMapTests.routeCases (ProcessorAddressMapTests.config 0 0 0xfffffffc 256 512 768))
  accesses := accesses + (← ProcessorAddressMapTests.routeCases (ProcessorAddressMapTests.config 2 3 65536 256 512 0xffffff00))
  accesses := accesses + (← ProcessorAddressMapTests.routeCases (ProcessorAddressMapTests.config 29 28 0x80000000 0xc0000000 0xc0000100 0xc0000200))
  let probes ← ProcessorAddressMapTests.probes
  IO.println s!"Address map: {layouts} independently checked layouts, {accesses} full routing/address checks, {probes} policy/boundary probes."
