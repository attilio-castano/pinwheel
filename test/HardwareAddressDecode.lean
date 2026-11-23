import Lean
import Pinwheel.Hardware.Processor.AddressDecode

open Lean Elab Command Pinwheel.Hardware
open Pinwheel.Hardware.Processor

namespace HardwareAddressDecodeTests

inductive Input (w : Nat) : Nat → Type where
  | address : Input w w
  | kind : Input w 2
  | size : Input w 2

abbrev NoRegister (_ : Nat) := Empty
def empty : Values NoRegister := fun r => nomatch r
def pins (w address kind size : Nat) : Values (Input w) := fun p => match p with
  | .address => BitVec.ofNat w address
  | .kind => BitVec.ofNat 2 kind
  | .size => BitVec.ofNat 2 size
abbrev E (w b : Nat) := Expr (Input w) NoRegister b
def address (w : Nat) : E w w := .input .address

def footprint (w bytes : Nat) : IO (AddressWindow.Footprint w) :=
  if h : 0 < bytes ∧ bytes ≤ 2^w then pure ⟨bytes, h.1, h.2⟩
  else throw (IO.userError "Invalid test footprint")

/-- The oracle measures remaining bytes with naturals. It never narrows an
endpoint, calls a production containment predicate, or evaluates an expression. -/
def containsReference (lower upper bytes a : Nat) : Bool :=
  lower ≤ a && a < upper && bytes ≤ upper-a

def require (label : String) (actual expected : Nat) : IO Unit := do
  unless actual == expected do throw (IO.userError s!"{label}: expected {expected}, got {actual}")

def checkWindow (w lower upper : Nat) (amounts addresses : List Nat) : IO Nat := do
  let result := AddressWindow.check w lower upper
  unless result.isSome == (lower ≤ upper && upper ≤ 2^w) do
    throw (IO.userError "Window constructor admission mismatch")
  let some window := result | return 0
  let mut count := 0
  for bytes in amounts do
    let width ← footprint w bytes
    let expression := AddressWindow.covers window width (address w)
    let localAddress := AddressWindow.offset window (address w)
    for raw in addresses do
      let a := raw % 2^w
      let i : Values (Input w) := pins w raw 0 0
      let expected := containsReference lower upper bytes a
      require s!"range w{w}/{lower}/{upper}/{bytes}/{a}" (expression.eval i empty).toNat expected.toNat
      if expected then
        require "admitted local address" (localAddress.eval i empty).toNat (a-lower)
      count := count+1
  return count

def windowCampaign : IO (Nat × Nat) := do
  let mut layouts := 0
  let mut checks := 0
  for w in [:5] do
    for lower in [:2^w+2] do
      for upper in [:2^w+2] do
        checks := checks + (← checkWindow w lower upper (List.range (2^w) |>.map (·+1)) (List.range (2^w)))
        layouts := layouts+1
  for w in [8, 17, 32, 64] do
    let limit := 2^w
    for (lower, upper) in [(0,limit), (0,limit-1), (limit-4,limit), (4,limit-4), (4,4)] do
      checks := checks + (← checkWindow w lower upper [1,2,4,limit]
        [0,1,3,4,5,limit-5,limit-4,limit-3,limit-2,limit-1,limit,limit+1])
      layouts := layouts+1
  return (layouts, checks)

def table (c : AddressMap.Config rw aw) : Array (Nat × Nat) :=
  #[(0,2^(rw+2)), (c.ramBase.toNat,2^(aw+2)),
    (c.gpioBase.toNat,256), (c.timerBase.toNat,256), (c.uartBase.toNat,256)]

/-- Independent integer table and raw-control policy. No AddressMap route,
permission, size, region-code, or AddressDecode model functions are used. -/
def routeReference (c : AddressMap.Config rw aw) (kind size a : Nat) : Nat := Id.run do
  if kind == 3 || size == 3 then return 7
  let bytes := if kind == 0 then 4 else 2^size
  if a / bytes * bytes != a then return 5
  let rows := table c
  for r in [:rows.size] do
    let (lower, count) := rows[r]!
    if lower ≤ a && a < lower+count && bytes ≤ lower+count-a then
      let permitted := if r == 0 then kind == 1 || (kind == 0 && size == 2)
        else if r == 1 then kind != 0 else kind != 0 && size == 2
      return if permitted then r else 6
  return 6

def addresses (c : AddressMap.Config rw aw) : Array Nat := Id.run do
  let mut values := #[0,1,2,3,0x80000000,0xfffffff8,0xfffffffc,0xfffffffd,0xfffffffe,0xffffffff]
  for (lower, count) in table c do
    for center in [lower,lower+count/2,lower+count] do
      for delta in [:17] do
        values := values.push ((center+2^32+delta-8)%2^32)
    if count ≤ 256 then
      values := values ++ (Array.range count |>.map (lower+·))
  let mut seed := 0x92b0e7
  for _ in [:256] do
    seed := (1664525*seed+1013904223)%2^32
    values := values.push seed
  return values

def routeCampaign : IO Nat := do
  let configurations : List (Nat × Nat × Nat × Nat × Nat × Nat) := [
    (10,10,0x10000,0x40000000,0x40000100,0x40000200),
    (0,0,4,256,512,768), (3,1,0xfffffff8,256,512,768),
    (10,10,0x10004,0x40000004,0x40000104,0x40000204),
    (28,28,0x40000000,0x80000000,0x80000100,0xffffff00)]
  let mut checks := 0
  for (rw,aw,ram,gpio,timer,uart) in configurations do
    let config : AddressMap.Config rw aw := ⟨BitVec.ofNat 32 ram,
      BitVec.ofNat 32 gpio, BitVec.ofNat 32 timer, BitVec.ofNat 32 uart⟩
    let some layout := AddressMap.check config | throw (IO.userError "Invalid route test layout")
    let expression : E 32 3 := AddressDecode.runtime layout (.input .kind) (.input .size) (address 32)
    for a in addresses config do
      for kind in [:4] do
        for size in [:4] do
          require s!"route {rw}/{aw}/{kind}/{size}/{a}"
            (expression.eval (pins 32 a kind size) empty).toNat (routeReference config kind size a)
          checks := checks+1
  return checks

def reject {w b : Nat} (name : String) (good bad : E w b) (a kind size expected : Nat) : IO Unit := do
  let i : Values (Input w) := pins w a kind size
  require s!"positive {name}" (good.eval i empty).toNat expected
  if (bad.eval i empty).toNat == expected then throw (IO.userError s!"Mutation escaped: {name}")

def mutations : IO Nat := do
  let almost : AddressWindow.Window 8 := ⟨0,255,by decide,by decide⟩
  let last : AddressWindow.Window 8 := ⟨0,256,by decide,by decide⟩
  let middle : AddressWindow.Window 8 := ⟨16,32,by decide,by decide⟩
  let short : AddressWindow.Window 8 := ⟨16,31,by decide,by decide⟩
  let bytes : AddressWindow.Footprint 8 := ⟨4,by decide,by decide⟩
  let a := address 8
  let endWide := WordOps.add (AddressWindow.widen a) (.lit 4)
  reject "endpoint wraps before range check" (AddressWindow.covers almost bytes a)
    (.inv (.ult (.lit 255) (WordOps.add a (.lit 4)))) 254 0 0 0
  reject "upper address-space endpoint narrowed" (AddressWindow.covers last bytes a)
    (.inv (.ult (.lit 0) endWide)) 252 0 0 1
  reject "lower bound omitted" (AddressWindow.covers middle bytes a)
    (.inv (.ult (.lit 32) endWide)) 0 0 0 0
  reject "footprint omitted" (AddressWindow.covers short bytes a) (.ult a (.lit 31)) 28 0 0 0
  reject "exact ending access rejected" (AddressWindow.covers middle bytes a) (.ult endWide (.lit 32)) 28 0 0 1
  reject "local address base omitted" (AddressWindow.offset middle a) a 20 0 0 4
  let l := AddressMap.defaultLayout
  let good : E 32 3 := AddressDecode.runtime l (.input .kind) (.input .size) (address 32)
  reject "ROM store permitted" good (AddressDecode.result l .load .word (address 32)) 0 2 2 6
  reject "alignment priority lost" good (.lit 6) 1 1 2 5
  reject "reserved kind aliases load" good (AddressDecode.runtimeSize l .load (.input .size) (address 32)) 0 3 2 7
  reject "RAM executable" good (AddressDecode.result l .load .word (address 32)) 0x10000 0 2 6
  reject "MMIO subword admitted" good (AddressDecode.result l .load .word (address 32)) 0x40000000 1 0 6
  return 11

example :
    (AddressWindow.covers (⟨0,2^32,by decide,by decide⟩ : AddressWindow.Window 32)
      ⟨4,by decide,by decide⟩ (address 32)).eval (pins 32 0xfffffffc 0 0) empty = 1 := by decide +kernel

end HardwareAddressDecodeTests

elab "#audit_address_decode" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if ["Pinwheel.Hardware.AddressWindow.", "_private.Pinwheel.Hardware.AddressWindow.",
        "Pinwheel.Hardware.Processor.AddressDecode.", "_private.Pinwheel.Hardware.Processor.AddressDecode.",
        "HardwareAddressDecodeTests."].any (fun pfx => name.toString.startsWith pfx) then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved address decoding axioms in {name}: {bad}"
  if count < 40 then throwError "Incomplete address-decoding audit"
  logInfo m!"Address decoding audit: {count} declarations, standard axioms only."

#audit_address_decode

def main : IO Unit := do
  let (layouts, windows) ← HardwareAddressDecodeTests.windowCampaign
  let routes ← HardwareAddressDecodeTests.routeCampaign
  let mutants ← HardwareAddressDecodeTests.mutations
  IO.println s!"Address decoding: {layouts} window configurations, {windows} full-footprint checks, {routes} runtime routing checks, {mutants} actual-expression mutations rejected."
