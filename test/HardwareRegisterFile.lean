import Lean
import Pinwheel.Hardware.Processor.RV32I.RegisterFile

open Lean Elab Command Pinwheel.Hardware
namespace HardwareRegisterFileTests

structure Pins where
  reset : Bool := false
  enable : Bool := false
  dest : Nat := 0
  data : Nat := 0
  left : Nat := 0
  right : Nat := 0
  deriving Repr, Inhabited

def Pins.values (p : Pins) (a w : Nat) : Values (RegisterFile.Input a w)
  | _, .at ⟨0, _⟩ => BitVec.ofBool p.reset
  | _, .at ⟨1, _⟩ => BitVec.ofBool p.enable
  | _, .at ⟨2, _⟩ => BitVec.ofNat a p.dest
  | _, .at ⟨3, _⟩ => BitVec.ofNat w p.data
  | _, .at ⟨4, _⟩ => BitVec.ofNat a p.left
  | _, .at ⟨5, _⟩ => BitVec.ofNat a p.right
  | _, .at ⟨n+6, h⟩ => False.elim (by change n+6 < 6 at h; omega)

def physical (a w : Nat) (bank : Array Nat) : Values (RegisterFile.Register a w)
  | _, .at k => BitVec.ofNat w bank[k.val]!

def snapshot (a w : Nat) (state : Values (RegisterFile.Register a w)) : Array Nat :=
  Array.ofFn fun k : Fin (2^a-1) => (state (RegisterFile.word k)).toNat

/-- Independent natural/array oracle. Physical index zero represents address
one; architectural zero never indexes the array. No production read/write,
specification, circuit expression, or RV32I semantic operation is called. -/
def referenceRead (a : Nat) (bank : Array Nat) (address : Nat) : Nat :=
  let index := address % 2^a
  if index = 0 then 0 else bank[index-1]!

def referenceStep (a w : Nat) (bank : Array Nat) (p : Pins) : Array Nat :=
  if p.reset then Array.replicate (2^a-1) 0
  else if p.enable && p.dest % 2^a != 0 then bank.set! (p.dest % 2^a-1) (p.data % 2^w)
  else bank

def outputs (a w : Nat) (c : Circuit (RegisterFile.Input a w) (RegisterFile.Register a w) (RegisterFile.Output w))
    (p : Pins) (state : Values (RegisterFile.Register a w)) : Array Nat :=
  Array.ofFn fun port : Fin 2 => (c.observe (p.values a w) state (RegisterFile.readData port)).toNat

def expectedOutputs (a : Nat) (bank : Array Nat) (p : Pins) : Array Nat :=
  #[referenceRead a bank p.left, referenceRead a bank p.right]

def check (a w : Nat) (bank : Array Nat) (p : Pins) : IO (Array Nat) := do
  unless bank.size = 2^a-1 do throw (IO.userError "Incorrect oracle bank length")
  let c := RegisterFile.circuit a w
  let state : Values (RegisterFile.Register a w) := physical a w bank
  let before := outputs a w c p state
  let next : Values (RegisterFile.Register a w) := c.step (p.values a w) state
  let actual := snapshot a w next
  let expected := referenceStep a w bank p
  unless before = expectedOutputs a bank p do
    throw (IO.userError s!"Pre-edge read mismatch a{a}/w{w}, {repr p}: {before}")
  unless actual = expected do throw (IO.userError s!"Raw register mismatch a{a}/w{w}, {repr p}: {actual} vs {expected}")
  unless outputs a w c p next = expectedOutputs a expected p do
    throw (IO.userError s!"Post-edge read mismatch a{a}/w{w}, {repr p}")
  -- Snapshot every register before the next edge; no lazy transition chain.
  return actual

def descriptor (a w : Nat) : IO Unit := do
  let ins := (RegisterFile.inputInterface a w).ports
  let outs := (RegisterFile.outputInterface w).ports
  let regs := (RegisterFile.registerInterface a w).ports
  unless ins.map Sigma.fst = #[1,1,a,w,a,a] && outs.map Sigma.fst = #[w,w] do
    throw (IO.userError "Incomplete typed port descriptor")
  unless regs.size = 2^a-1 && regs.all (fun p => p.1 == w) do
    throw (IO.userError "Register descriptor has a missing or extra word")
  let names := regs.map (fun p => (RegisterFile.registerInterface a w).label p.2)
  unless names = (Array.range (2^a-1)).map (fun k => s!"word_{k+1}") do
    throw (IO.userError "Zero register storage or descriptor ordering mismatch")

def exhaustive : IO Nat := do
  let mut edges := 0
  for a in [:3] do
    for w in [:3] do
      descriptor a w
      let wordCount := 2^a-1
      let valueCount := 2^w
      for rawBank in [:valueCount^wordCount] do
        let bank := (Array.range wordCount).map (fun k => rawBank / valueCount^k % valueCount)
        for reset in [false,true] do
          for enable in [false,true] do
            for dest in [:2^a] do
              for data in [:valueCount] do
                for left in [:2^a] do
                  for right in [:2^a] do
                    let _ ← check a w bank ⟨reset,enable,dest,data,left,right⟩
                    edges := edges+1
  return edges

def lcg (seed : Nat) : Nat := (1664525*seed+1013904223)%2^64

def traces : IO Nat := do
  let mut edges := 0
  for a in [0,1,2,3,5,6] do
    for w in [0,1,8,17,32,64] do
      descriptor a w
      let mut bank := (Array.range (2^a-1)).map fun k => (2^w-1-k)%2^w
      let mut seed := 0x381ac9+a*137+w
      -- Dirty storage is observable before a reset edge; simultaneous writing
      -- loses to reset. Then write/read every address, including x0.
      bank ← check a w bank ⟨true,true,1,2^w-1,1,2^a-1⟩
      edges := edges+1
      for dest in [:2^a] do
        bank ← check a w bank ⟨false,true,dest,2^w-1,dest,(dest+1)%2^a⟩
        bank ← check a w bank ⟨false,false,dest,0,dest,0⟩
        edges := edges+2
      for cycle in [:256] do
        seed := lcg seed
        let dest := seed / 8
        let left := if cycle%3 = 0 then dest else seed / 128
        let right := if cycle%5 = 0 then 0 else seed / 65536
        bank ← check a w bank ⟨cycle%37 = 0,seed%4 != 0,dest,lcg seed,left,right⟩
        edges := edges+1
  return edges

def rv32 : IO Nat := do
  let bank := (Array.range 31).map fun k => (0x80000000 + k*0x1234567)%2^32
  let state : Values (RegisterFile.Register 5 32) := physical 5 32 bank
  let arch := Processor.RV32I.RegisterFile.view state
  let mut checks := 0
  for address in [:32] do
    unless (Processor.RV32I.Semantics.read arch (BitVec.ofNat 5 address)).toNat = referenceRead 5 bank address do
      throw (IO.userError "RV32 architectural projection mismatch")
    for dest in [:32] do
      for data in [0,1,0x7fffffff,0x80000000,0xffffffff] do
        let p : Pins := ⟨false,true,dest,data,address,dest⟩
        let next : Values Processor.RV32I.RegisterFile.Register := Processor.RV32I.RegisterFile.circuit.step (p.values 5 32) state
        let written := Processor.RV32I.Semantics.write arch (BitVec.ofNat 5 dest) (BitVec.ofNat 32 data)
        unless (Processor.RV32I.Semantics.read (Processor.RV32I.RegisterFile.view next) (BitVec.ofNat 5 address)) =
            Processor.RV32I.Semantics.read written (BitVec.ofNat 5 address) do
          throw (IO.userError "RV32 writeback projection mismatch")
        let _ ← check 5 32 bank p
        checks := checks+1
  return checks

abbrev TestCircuit := Circuit (RegisterFile.Input 2 8) (RegisterFile.Register 2 8) (RegisterFile.Output 8)
abbrev E (w : Nat) := Expr (RegisterFile.Input 2 8) (RegisterFile.Register 2 8) w

def mutant (mode : Nat) : TestCircuit :=
  let good := RegisterFile.circuit 2 8
  { next := fun r => match r with
      | .at k =>
        let r := RegisterFile.word (a := 2) (w := 8) k
        let reset : E 1 := .input RegisterFile.reset
        let enable : E 1 := .input RegisterFile.writeEnable
        let dest : E 2 := .input RegisterFile.writeAddress
        let data : E 8 := .input RegisterFile.writeData
        let matched : E 1 := .equal dest (.lit (BitVec.ofNat 2 (k.val+1)))
        if mode = 1 then .mux reset (.lit 0) (.mux enable data (.reg r))
        else if mode = 3 then .mux reset (.reg r) (good.next r)
        else if mode = 4 then .mux (.band enable matched) data (good.next r)
        else if mode = 5 then .mux reset (.lit 0) (.mux matched data (.reg r))
        else if mode = 6 then .mux reset (.lit 0)
          (.mux (.band enable (.equal dest (.lit (BitVec.ofNat 2 (k.val+2))))) data (.reg r))
        else if mode = 7 then .mux enable (.inv (good.next r)) (good.next r)
        else if mode = 10 then .mux enable (good.next r) (.inv (.reg r))
        else good.next r
    output := fun o => match o with
      | .at port =>
        let o := RegisterFile.readData (w := 8) port
        let address : E 2 := .input (RegisterFile.readAddress port)
        if mode = 0 then .mux (.zero address) (.reg (RegisterFile.word ⟨0,by decide⟩)) (good.output o)
        else if mode = 2 then .mux (.band (.input RegisterFile.writeEnable)
          (.equal address (.input RegisterFile.writeAddress))) (.input RegisterFile.writeData) (good.output o)
        else if mode = 8 then good.output (RegisterFile.readData 0)
        else if mode = 9 then .mux (.input RegisterFile.reset) (.lit 0) (good.output o)
        else if mode = 11 then RegisterFile.readExpr (.concat (.lit (0#1)) (.slice 0 1 (by decide) address))
        else good.output o }

def mutations : IO Nat := do
  let bank := #[0x35,0x72,0xa9]
  let samples : Array Pins := #[
    ⟨false,false,0,0,0,0⟩, ⟨false,true,0,0xfa,1,2⟩,
    ⟨false,true,1,0xfa,1,2⟩, ⟨true,false,0,0,1,2⟩,
    ⟨true,true,1,0xfa,1,2⟩, ⟨false,false,1,0xfa,1,2⟩,
    ⟨false,true,2,0xfa,1,2⟩, ⟨false,true,1,0xfa,2,3⟩,
    ⟨false,false,0,0,1,2⟩, ⟨true,false,0,0,1,2⟩,
    ⟨false,false,0,0,1,2⟩, ⟨false,false,0,0,3,2⟩]
  for mode in [:samples.size] do
    let p := samples[mode]!
    let _ ← check 2 8 bank p
    let wrong := mutant mode
    let state : Values (RegisterFile.Register 2 8) := physical 2 8 bank
    let next : Values (RegisterFile.Register 2 8) := wrong.step (p.values 2 8) state
    let expected := referenceStep 2 8 bank p
    unless outputs 2 8 wrong p state != expectedOutputs 2 bank p || snapshot 2 8 next != expected ||
        outputs 2 8 wrong p next != expectedOutputs 2 expected p do
      throw (IO.userError s!"Actual expression mutation {mode} escaped")
  return samples.size

end HardwareRegisterFileTests

elab "#audit_register_file" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if ["Pinwheel.Hardware.RegisterFile.", "_private.Pinwheel.Hardware.RegisterFile.",
        "Pinwheel.Hardware.Processor.RV32I.RegisterFile.", "_private.Pinwheel.Hardware.Processor.RV32I.RegisterFile.",
        "HardwareRegisterFileTests."].any (fun stem => name.toString.startsWith stem) then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved register-file axioms in {name}: {bad}"
  if count < 90 then throwError "Incomplete register-file audit"
  logInfo m!"Register-file audit: {count} declarations, standard axioms only."

#audit_register_file

def main : IO Unit := do
  let exhaustive ← HardwareRegisterFileTests.exhaustive
  let traces ← HardwareRegisterFileTests.traces
  let rv32 ← HardwareRegisterFileTests.rv32
  let mutants ← HardwareRegisterFileTests.mutations
  IO.println s!"Register file: {exhaustive} exhaustive raw edges, {traces} mixed-width trace edges, {rv32} RV32 projection edges, {mutants} actual expression mutations rejected."
