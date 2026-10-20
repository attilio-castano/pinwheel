import Pinwheel.Hardware.StreamingReady.Initialization
import Pinwheel.Hardware.Streaming.BootCorrespondence
import Pinwheel.Hardware.StreamingReady.InitializedSession
import Pinwheel.Program.StreamingReadyBootPins

/-! Physical boot transport. Loader acceptance is derived from actual free
metadata; it is not supplied as an agreement premise. -/
namespace Pinwheel.Hardware.StreamingReady.BootCorrespondence
open Pinwheel.Hardware Pinwheel.Program.StreamingReady Initialization
open Pinwheel.Hardware.Streaming
set_option linter.unusedSimpArgs false

theorem core_inputs (s : Package.State a) (pin : Session.Pins) (control : Pinwheel.Program.Streaming.Host.BootControl.State)
    (project : Pinwheel.Program.Streaming.Host.BootControl.project (HostCorrespondence.stateFromValues s.frontend) = control) :
    (fun {w} => s.coreInputs (Package.Components.typed a) (SessionCorrespondence.pins pin) (w := w)) =
      @HostCorrespondence.commandValues (Pinwheel.Program.Streaming.Host.BootControl.command (pin.host {}) control) := by
  have represented := HostCorrespondence.state_roundtrip s.frontend
  have inputs : @(SessionCorrespondence.pins pin).inputs (fun _ => 0) =
      @HostCorrespondence.inputs (pin.host {}) := by
    funext w port
    cases port <;> try rfl
    case status output => cases output <;> rfl
  funext w port
  change Frontend.circuit.observe ((SessionCorrespondence.pins pin).inputs (fun _ => 0))
    s.frontend (.core port) = _
  rw [inputs,← represented]
  change (Frontend.coreInput port).eval (HostCorrespondence.inputs (pin.host {}))
    (HostCorrespondence.values (HostCorrespondence.stateFromValues s.frontend)) = _
  rw [HostCorrespondence.coreInput_eval]
  have command := Pinwheel.Program.Streaming.Host.BootControl.command_correct (pin.host {}) (HostCorrespondence.stateFromValues s.frontend)
  rw [project] at command
  rw [command]

def metadata (p : Program) (n : Nat) (installed : Bool) : Metadata :=
  if installed then (metadataAfter p n).commit (loaderGeometry p) else metadataAfter p n

structure Related (image : Compiled source idle) (control : Pinwheel.Program.Streaming.Host.BootControl.State) (n : Nat) (installed : Bool)
    (actual : Package.State a) (sourceCore : Carrier a) : Prop where
  project : Pinwheel.Program.Streaming.Host.BootControl.project (HostCorrespondence.stateFromValues actual.frontend) = control
  core : (fun {w} => actual.core (w := w)) = @Initialization.values a (metadata image.program n installed) sourceCore
  phase : sourceCore.phase = .free
  generation : sourceCore.generation = if installed then 1 else 0
  transfer : sourceCore.transfer = 0
  structural : (ofCarrier sourceCore).Structural
  within : n ≤ image.program.length
  complete : installed = true → n = image.program.length

theorem rejected_quiet (i : Values Core.Input) (r : Values (Core.Register a))
    (command : i .command = 0) (tx : i .txPush = 0) (rx : i .rxPop = 0) :
    (Core.circuit a).observe i r .rejected = 0 := by
  simp [Core.circuit,Circuit.observe,Core.output,Core.rejected,Core.both,Core.either,
    Core.cmd,Expr.eval,command,tx,rx]

theorem rejected_write (metadata : Metadata) (s : Carrier a) (i : Values Core.Input)
    (address : BitVec 6) (word : BitVec 64) (input : Write i address word)
    (phase : s.phase = .free) (tx : i .txPush = 0) (rx : i .rxPop = 0) :
    (Core.circuit a).observe i (values metadata s) .rejected = 0 := by
  rw [LoaderEquivalence.free_observe_equal i (values metadata s)
    (by change s.phase.code = 0; rw [phase]; rfl)]
  exact Streaming.BootCorrespondence.rejected_write metadata s i address word input phase tx rx

theorem rejected_commit (p : Program) (metadata : Metadata) (s : Carrier a) (i : Values Core.Input)
    (input : Commit p i) (phase : s.phase = .free) (pending : metadata.pending = 1)
    (room : s.generation ≠ 65535#16)
    (covered : ∀ k : Fin 64, k.val < p.length → metadata.written.getLsbD k.val = true)
    (tx : i .txPush = 0) (rx : i .rxPop = 0) :
    (Core.circuit a).observe i (values metadata s) .rejected = 0 := by
  rw [LoaderEquivalence.free_observe_equal i (values metadata s)
    (by change s.phase.code = 0; rw [phase]; rfl)]
  exact Streaming.BootCorrespondence.rejected_commit (loaderGeometry p) metadata s i input phase pending room covered tx rx

theorem image_length (image : Compiled source idle) : image.words.length = image.program.length := by
  rw [image.wordsEqual,List.length_map,image.program_length]

theorem image_row (image : Compiled source idle) (n : Nat) (within : n < image.words.length) :
    image.words[n]?.getD 0 = rowWord image.program n := by
  rw [List.getElem?_eq_getElem within,Option.getD_some]
  exact (compiled_row image n (by simpa only [image.wordsEqual,List.length_map] using within)).symm

structure Effects (image : Compiled source idle) (n : Nat) (installed : Bool) (c : Pinwheel.Program.Streaming.Host.Command)
    (before : Carrier a) (nextN : Nat) (nextInstalled : Bool) (after : Carrier a) : Prop where
  step : @Circuit.step _ _ _ (Core.circuit a) (HostCorrespondence.commandValues c)
      (Initialization.values (metadata image.program n installed) before) =
    @Initialization.values a (metadata image.program nextN nextInstalled) after
  rejected : (Core.circuit a).observe (HostCorrespondence.commandValues c)
      (Initialization.values (metadata image.program n installed) before) .rejected = 0
  phase : after.phase = .free
  generation : after.generation = if nextInstalled then 1 else 0
  transfer : after.transfer = before.transfer
  structural : (ofCarrier after).Structural
  within : nextN ≤ image.program.length
  complete : nextInstalled = true → nextN = image.program.length

theorem delivery_effects (image : Compiled source idle) (n : Nat) (installed : Bool) (c : Pinwheel.Program.Streaming.Host.Command)
    (before : Carrier a) (phase : before.phase = .free)
    (generation : before.generation = if installed then 1 else 0) (structural : (ofCarrier before).Structural)
    (within : n ≤ image.program.length) (complete : installed = true → n = image.program.length)
    (delivery : BootPins.Delivery image.words idle n installed c nextN nextInstalled) :
    ∃ after : Carrier a, Effects image n installed c before nextN nextInstalled after := by
  have coldInput (safe : BootPins.CommandSafe c) : HostCorrespondence.commandValues c .initialize = 0 := by
    change BitVec.ofBool c.runtime.initialize = 0
    rw [safe.cold]
    rfl
  have txInput (safe : BootPins.CommandSafe c) : HostCorrespondence.commandValues c .txPush = 0 := by
    change BitVec.ofBool c.runtime.txPush = 0
    rw [safe.tx]
    rfl
  have rxInput (safe : BootPins.CommandSafe c) : HostCorrespondence.commandValues c .rxPop = 0 := by
    change BitVec.ofBool c.runtime.rxPop = 0
    rw [safe.rx]
    rfl
  cases delivery with
  | quiet safe command =>
    refine ⟨before.sample c.runtime.rawInputs,?_,?_,phase,generation,rfl,ofCarrier_sample_structural _ _ structural,within,complete⟩
    · funext w port
      exact idle_step _ _ _ (coldInput safe) command phase port
    · exact rejected_quiet _ _ command (txInput safe) (rxInput safe)
  | write safe uninstalled live command address word =>
    have actualWrite : Write (HostCorrespondence.commandValues c) (BitVec.ofNat 6 n) (rowWord image.program n) :=
      ⟨coldInput safe,command,address,word.trans (image_row image n live)⟩
    have bound : n+1 ≤ image.program.length := by rw [← image_length image]; omega
    refine ⟨before.sample c.runtime.rawInputs,?_,?_,phase,?_,rfl,ofCarrier_sample_structural _ _ structural,bound,?_,⟩
    · subst installed
      funext w port
      exact write_step _ _ _ _ _ actualWrite phase port
    · exact rejected_write _ _ _ _ _ actualWrite phase (txInput safe) (rxInput safe)
    · simpa only [Pinwheel.Program.Streaming.State.sample,uninstalled,Bool.false_eq_true,ite_false] using generation
    · intro impossible; contradiction
  | commit safe uninstalled allWritten command count pins =>
    have allRows : nextN = image.program.length := allWritten.trans (image_length image)
    have actualCommit : Commit image.program (HostCorrespondence.commandValues c) :=
      ⟨coldInput safe,command,count.trans (congrArg (BitVec.ofNat 7) (image_length image)),
        congrArg Engine.Reactive.Pins.levels pins,congrArg Engine.Reactive.Pins.enabled pins⟩
    have pending : (metadataAfter image.program nextN).pending = 1 :=
      metadata_pending _ _ (by rw [allRows]; exact Initialization.length_positive _)
    have room : before.generation ≠ 65535#16 := by
      rw [generation,uninstalled]
      decide
    have covered : ∀ k : Fin 64, k.val < image.program.length →
        (metadataAfter image.program nextN).written.getLsbD k.val = true := by
      rw [allRows]
      exact metadata_covered _ _ (Initialization.length_le _)
    refine ⟨Streaming.Initialization.committed before c.runtime.rawInputs,?_,?_,phase,?_,rfl,⟨structural.accepted,structural.txValid,structural.rxUsed,structural.reservationCredit,structural.partialCredit⟩,within,fun _ => allRows⟩
    · subst installed
      funext w port
      exact commit_step _ _ _ _ actualCommit phase pending room covered port
    · subst installed
      exact rejected_commit _ _ _ _ actualCommit phase pending room covered (txInput safe) (rxInput safe)
    · change before.generation + 1#16 = 1#16
      rw [generation,uninstalled]
      rfl

theorem frontend_project (actual : Package.State a) (pin : Session.Pins) (control : Pinwheel.Program.Streaming.Host.BootControl.State)
    (project : Pinwheel.Program.Streaming.Host.BootControl.project (HostCorrespondence.stateFromValues actual.frontend) = control)
    (safe : Pinwheel.Program.Streaming.Host.BootControl.Safe control)
    (rejected : actual.status (Package.Components.typed a) (SessionCorrespondence.pins pin) .rejected = 0) :
    Pinwheel.Program.Streaming.Host.BootControl.project (HostCorrespondence.stateFromValues
      (actual.step (Package.Components.typed a) (SessionCorrespondence.pins pin)).frontend) =
      Pinwheel.Program.Streaming.Host.BootControl.step false (pin.host {}) control := by
  let input := HostCorrespondence.inputFromValues
    (actual.frontendInputs (Package.Components.typed a) (SessionCorrespondence.pins pin))
  have fields : Pinwheel.Program.Streaming.Host.BootControl.input false input = Pinwheel.Program.Streaming.Host.BootControl.input false (pin.host {}) := by
    simp only [input,Pinwheel.Program.Streaming.Host.BootControl.input,HostCorrespondence.inputFromValues,
      Package.State.frontendInputs,Streaming.Package.State.frontendInputs,Package.Pins.inputs,Streaming.Package.Pins.inputs,SessionCorrespondence.pins,
      Session.Pins.host,Pinwheel.Program.Streaming.Session.Pins.host,BitVec.getLsbD_ofBool,decide_true,Bool.true_and]
  have rejectedFalse : input.status.rejected = false := by
    change (actual.status (Package.Components.typed a) (SessionCorrespondence.pins pin) .rejected).getLsbD 0 = false
    rw [rejected]
    rfl
  have full : HostCorrespondence.stateFromValues
      (actual.step (Package.Components.typed a) (SessionCorrespondence.pins pin)).frontend =
      Pinwheel.Program.Streaming.Host.step input (HostCorrespondence.stateFromValues actual.frontend) := by
    have equal := HostCorrespondence.step_fromRaw
      (actual.frontendInputs (Package.Components.typed a) (SessionCorrespondence.pins pin)) actual.frontend
    exact (congrArg HostCorrespondence.stateFromValues equal).trans
      (InitializedSession.frontend_source_roundtrip _)
  rw [full,Pinwheel.Program.Streaming.Host.BootControl.step_correct input _ (by rw [project]; exact safe),project,rejectedFalse]
  unfold Pinwheel.Program.Streaming.Host.BootControl.step
  rw [fields]

theorem Related.step (image : Compiled source idle) (control : Pinwheel.Program.Streaming.Host.BootControl.State)
    (n : Nat) (installed : Bool) (actual : Package.State a) (sourceCore : Carrier a)
    (related : Related image control n installed actual sourceCore) (pin : Session.Pins)
    (safe : Pinwheel.Program.Streaming.Host.BootControl.Safe control)
    (delivery : BootPins.Delivery image.words idle n installed
      (Pinwheel.Program.Streaming.Host.BootControl.command (pin.host {}) control) nextN nextInstalled) :
    ∃ after : Carrier a, Related image (Pinwheel.Program.Streaming.Host.BootControl.step false (pin.host {}) control)
      nextN nextInstalled (actual.step (Package.Components.typed a) (SessionCorrespondence.pins pin)) after := by
  have input := core_inputs actual pin control related.project
  obtain ⟨after,effects⟩ := delivery_effects image n installed _ sourceCore related.phase
    related.generation related.structural related.within related.complete delivery
  have rejected : actual.status (Package.Components.typed a) (SessionCorrespondence.pins pin) .rejected = 0 := by
    unfold Package.State.status Streaming.Package.State.status
    rw [input,related.core]
    exact effects.rejected
  refine ⟨after,frontend_project actual pin control related.project safe rejected,?_,effects.phase,
    effects.generation,effects.transfer.trans related.transfer,effects.structural,effects.within,effects.complete⟩
  change @Circuit.step _ _ _ (Core.circuit a)
    (actual.coreInputs (Package.Components.typed a) (SessionCorrespondence.pins pin)) actual.core = _
  rw [input,related.core]
  exact effects.step

structure Initialized (image : Compiled source idle) (actual : Package.State a)
    (final : Session.State a) : Prop where
  package : actual = SessionCorrespondence.values (compiledImage image) final
  structural : final.core.Structural
  free : final.core.phase = .free
  generation : final.core.generation = 1
  transfer : final.core.transfer = 0
  phase : final.host.phase = 0
  ready : final.host.ready = false
  active : final.host.active = false

theorem certified_run (image : Compiled source idle) (control : Pinwheel.Program.Streaming.Host.BootControl.State)
    (n : Nat) (installed : Bool) (pins : List Session.Pins)
    (certificate : BootPins.Certified image.words idle control n installed pins)
    (actual : Package.State a) (sourceCore : Carrier a)
    (related : Related image control n installed actual sourceCore) :
    ∃ final : Session.State a, Initialized image
      (actual.run (Package.Components.typed a) (pins.map SessionCorrespondence.pins)) final := by
  induction certificate generalizing actual sourceCore with
  | nil control n installed complete done phase ready active =>
    have allRows : n = image.program.length := complete.trans (image_length image)
    have core : (fun {w} => actual.core (w := w)) =
        @SourceRefinement.values image.program a (compiledImage image) (ofCarrier sourceCore) := by
      rw [related.core]
      simp only [metadata,done,↓reduceIte,allRows]
      exact values_installed image.program (@compiledCanonical source idle image) sourceCore
    have generation : sourceCore.generation = 1 := by
      simpa only [done,↓reduceIte] using related.generation
    refine ⟨⟨HostCorrespondence.stateFromValues actual.frontend,ofCarrier sourceCore⟩,?_,related.structural,
      (by change phaseLift sourceCore.phase = .free; rw [related.phase]; rfl),generation,related.transfer,?_,?_,?_⟩
    · apply InitializedSession.state_ext
      · exact (HostCorrespondence.state_roundtrip actual.frontend).symm
      · exact core
    · exact (congrArg Pinwheel.Program.Streaming.Host.BootControl.State.phase related.project).trans phase
    · exact (congrArg Pinwheel.Program.Streaming.Host.BootControl.State.ready related.project).trans ready
    · exact (congrArg Pinwheel.Program.Streaming.Host.BootControl.State.active related.project).trans active
  | cons safe delivery after ih =>
    obtain ⟨next,nextRelated⟩ := Related.step image _ _ _ actual sourceCore related _ safe delivery
    exact ih _ _ nextRelated

theorem cold_related (image : Compiled source idle) :
    Related image BootPins.initialControl 0 false
      (InitializedSession.coldState a (SessionCorrespondence.pins BootPins.coldPin)) ({} : Carrier a) := by
  constructor
  · change Pinwheel.Program.Streaming.Host.BootControl.project (HostCorrespondence.stateFromValues
      (HostCorrespondence.values (InitializedSession.coldHost (SessionCorrespondence.pins BootPins.coldPin)))) = _
    rw [InitializedSession.frontend_source_roundtrip]
    rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact initial_structural a
  · omega
  · intro impossible; contradiction

/-- Concrete sampled physical uploads establish the whole independent source
session from arbitrary power-up registers. Acceptance, VALID and image binding
are consequences of the trace certificate and actual loader guards. -/
theorem compiled_initialized (image : Compiled source idle) (pins : List Session.Pins)
    (certificate : BootPins.Certified image.words idle BootPins.initialControl 0 false pins)
    (startup : Package.State a) :
    ∃ final : Session.State a, Initialized image
      (startup.run (Package.Components.typed a)
        (SessionCorrespondence.pins BootPins.coldPin :: pins.map SessionCorrespondence.pins)) final := by
  change ∃ final : Session.State a, Initialized image
    ((startup.step (Package.Components.typed a) (SessionCorrespondence.pins BootPins.coldPin)).run (Package.Components.typed a)
      (pins.map SessionCorrespondence.pins)) final
  rw [InitializedSession.cold_correct startup (SessionCorrespondence.pins BootPins.coldPin) rfl]
  exact certified_run image _ _ _ pins certificate _ _ (cold_related image)

theorem i2c_initialized (startup : Package.State a) :
    ∃ final : Session.State a, Initialized (i2cImage .standard)
      (startup.run (Package.Components.typed a)
        (SessionCorrespondence.pins BootPins.coldPin :: BootPins.i2c.map SessionCorrespondence.pins)) final :=
  compiled_initialized (i2cImage .standard) BootPins.i2c BootPins.i2c_certified startup

end Pinwheel.Hardware.StreamingReady.BootCorrespondence
