import Pinwheel.Hardware.Stream.ParallelCircuit
import Pinwheel.Hardware.Emit

namespace Pinwheel.Hardware.Stream

/-- A hierarchy is a typed tree. Flattening uses the proved serial builder;
leaf implementations and contracts remain reusable independently of the tree. -/
inductive Design : Nat → Nat → Type 1 where
  | leaf (name : String) (component : Certified wi wo) : Design wi wo
  | serial : Design wi wm → Design wm wo → Design wi wo
  | parallel : Design wi wa → Design wi wb → Design wi (wa + wb)

def Design.flatten : Design wi wo → Certified wi wo
  | .leaf _ c => c
  | .serial a b => a.flatten.serial b.flatten
  | .parallel a b => a.flatten.parallel b.flatten

def Design.pipeline (m : Map wi wo) : Nat → Design wi wo
  | 0 => .leaf "map" (Elastic.certified m)
  | n + 1 => .serial (.leaf "map" (Elastic.certified m)) (pipeline (Map.identity wo) n)

def Design.buffered (m : Map wi wo) (depth : Nat) (hd : 0 < depth) (extra : Nat) : Design wi wo :=
  .serial (.leaf "fifo" (fifoCertified wi depth hd)) (.pipeline m extra)

def sumHalves (w : Nat) (x : BitVec (w + w)) : BitVec w :=
  x.extractLsb' 0 w + x.extractLsb' w w

def adder (w : Nat) : Map (w + w) w where
  expression := (Expr.slice 0 w (by omega) (.input .data)).plus
    (.slice w w (by omega) (.input .data))
  function := sumHalves w
  correct := by intro v; simp [sumHalves, Expr.eval, dataValues]

def adderDesign (width depth extra : Nat) (hd : 0 < depth) : Design (width + width) width :=
  Design.buffered (adder width) depth hd extra

def Certified.rtl (c : Certified wi wo) (name : String) : Except String String :=
  Emit.moduleText name c.circuit (inputPorts wi).interface.ports c.registers.ports
    (outputPorts wo).interface.ports (inputPorts wi).interface.label
    c.registers.label (outputPorts wo).interface.label

def decodeOutput (o : Values (Out w)) : Output (BitVec w) :=
  ⟨o inReady == 1, if o outValid = 1 then some (o outData) else none⟩

theorem decode_outputValues (o : Output (BitVec w)) : decodeOutput (outputValues o) = o := by
  cases o with
  | mk r v => cases r <;> cases v <;> rfl

def Certified.simulator (c : Certified wi wo) :
    Timed.Component (Input (BitVec wi)) (Values c.Register) (Output (BitVec wo)) :=
  ⟨fun i s => c.circuit.step (inputValues i) s,
   fun i s => decodeOutput (c.circuit.observe (inputValues i) s)⟩

def Certified.refinement (c : Certified wi wo) : Timed.Refinement c.simulator c.machine.component where
  Rel := fun r s => c.contract.Valid s ∧ @r = @c.encode s
  step := by
    intro i r s h
    rcases h with ⟨hv, rfl⟩
    exact ⟨c.contract.preserved i s hv, funext fun b => funext fun p => c.step_eq i s hv p⟩
  observe := by
    intro i r s h
    rcases h with ⟨hv, rfl⟩
    have he : (fun {b} (p : Out wo b) => c.circuit.observe (inputValues i) (c.encode s) p) =
        @outputValues wo (c.machine.component.observe i s) :=
      funext fun b => funext fun p => c.output_eq i s hv p
    exact (congrArg decodeOutput he).trans (decode_outputValues _)

theorem Certified.trace_correct (c : Certified wi wo) (inputs : List (Input (BitVec wi))) :
    c.simulator.trace (c.encode c.initial) inputs = c.machine.component.trace c.initial inputs :=
  c.refinement.trace_eq _ _ ⟨c.initial_valid, rfl⟩ inputs

/-- The complete accepted/emitted/pending theorem is inherited without opening
the FIFO or pipeline implementation. Reset starts a fresh accounting epoch. -/
theorem Certified.transactions (c : Certified wi wo) (inputs : List (Input (BitVec wi))) :
    let result := runHistory c.machine.component c.initial {} inputs
    result.2.inputs.map c.function = result.2.outputs ++ c.contract.pending result.1 :=
  c.contract.history c.initial {} c.initial_valid (by simp [c.initial_empty]) inputs

end Pinwheel.Hardware.Stream
