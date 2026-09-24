import Pinwheel.Hardware.Reactive.Interface
import Pinwheel.Hardware.Storage.CacheContract
import Pinwheel.Hardware.Storage.SramSchedule

open Pinwheel.Hardware

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def renamedLabel : {w : Nat} → Reactive.Register w → String
  | _, .pc => "program_counter" | _, r => Reactive.registerLabel r

private def renamedRegisters : Interface Reactive.Register :=
  Reactive.registerInterface.rename renamedLabel (by decide +kernel)

private def typedToken : {w : Nat} → Reactive.Register w → Nat
  | _, .mode => 101 | _, .pc => 503 | _, .remaining => 107 | _, .waitLeft => 109
  | _, .levels => 113 | _, .enabled => 127 | _, .sample k => 1000 + k.val

private def cacheCore : Timed.Component Loader.Machine.Inputs Storage.Cache.State (Values Reactive.Output) :=
  ⟨Storage.Cache.next, fun i s => fun {w} (o : Reactive.Output w) => Storage.Cache.component.observe i s (.core o)⟩

def main : IO Unit := do
  -- Renaming PC must not change either effect order or typed result lookup.
  let emit {w : Nat} (p : Reactive.Register w) : StateM (Array Nat) Nat := do
    modify (·.push (typedToken p))
    return typedToken p
  let (original, order) := (Reactive.registerInterface.mapM emit).run #[]
  let (renamed, renamedOrder) := (renamedRegisters.mapM emit).run #[]
  let expectedOrder := #[101, 503, 107, 109, 113, 127] ++ Array.ofFn (fun k : Fin 16 => 1000 + k.val)
  ensure (order == expectedOrder && renamedOrder == expectedOrder) "emission traversal order changed"
  ensure (renamedRegisters.label Reactive.Register.pc == "program_counter") "rename not exercised"
  for ⟨_, p⟩ in Reactive.registers do
    ensure (original p == typedToken p && renamed p == typedToken p) "typed result lookup changed"
  ensure (renamed Reactive.Register.pc == 503) "renamed PC lost its next-state wire"
  -- Exercise named observations on the actual cache component, from idle with
  -- arbitrary current-word bits. Initialization determines the post-edge state.
  let core : Reactive.State := ⟨0, 0, 0, 0, {}, Vector.replicate 16 false⟩
  let machine : Loader.Machine.State := ⟨{}, core, fun _ {_w} _ => 0⟩
  let state : Storage.Cache.State := ⟨machine, 0xdeadbeef⟩
  let input : Loader.Machine.Inputs := {init := true}
  let expected : Values Reactive.Output × Values Reactive.Output := cacheCore.edge input state
  let named := (Reactive.outputInterface.namedComponent cacheCore).edge input state
  ensure (named.1.size == 25 && named.2.size == 25) "named edge omitted outputs"
  ensure (named.1[1]? == some ⟨"pc", 8, 0⟩ && named.2[21]? == some ⟨"sample15", 1, 0⟩)
    "named output width, value or order changed"
  ensure ((Reactive.outputInterface.edgeDifferences 42 "cache.core" expected expected).isEmpty)
    "equal edges reported a difference"
  let wrongPC : Values Reactive.Output := fun {w} (p : Reactive.Output w) => match w, p with
    | _, .state .pc => 1 | _, p => expected.2 p
  let after := Reactive.outputInterface.edgeDifferences 42 "cache.core" expected (expected.1, wrongPC)
  ensure (after == #[⟨42, .after, "cache.core", "pc", 8, 0, 1⟩]) "post-edge mismatch attribution"
  let wrongSample : Values Reactive.Output := fun {w} (p : Reactive.Output w) => match w, p with
    | _, .state (.sample k) => if k.val == 15 then 1 else expected.1 (.state (.sample k))
    | _, p => expected.1 p
  let before := Reactive.outputInterface.edgeDifferences 42 "cache.core" expected (wrongSample, expected.2)
  ensure (before == #[⟨42, .before, "cache.core", "sample15", 1, 0, 1⟩]) "pre-edge sample mismatch attribution"
  ensure (after[0]?.map Interface.Mismatch.describe == some "cycle 42 after cache.core.pc (8 bits): expected 0, got 1")
    "diagnostic lost cycle, phase, component, width or values"
  for mismatch in after do IO.println mismatch.describe
  -- The SRAM request interface diagnoses an illegal extra write on the actual
  -- idle controller's read edge, with the physical boundary and phase named.
  let ramInput : Values Storage.SramController.Input := Storage.SramController.inputValues {} (fun _ => 0)
  let ramState : Values Storage.SramController.Register := fun _ => 0
  let actual : Values Storage.SramController.Port := Storage.SramController.portValues false ramInput ramState
  let collision : Values Storage.SramController.Port := fun {w} p => match w, p with
    | _, .write => 1 | _, p => actual p
  let badAccess := Storage.SramAssembly.requestInterface.differences 7 "sram.request" .before actual collision
  ensure (badAccess == #[⟨7, .before, "sram.request", "mem_write", 1, 0, 1⟩])
    "SRAM request interface hid or misattributed a simultaneous write"
  IO.println "SRAM request interface: conflicting write attributed to the actual typed pre-edge port."
  IO.println "Interfaces: renamed typed lookup, effect order, named cache edges and phase-specific mutations passed."
