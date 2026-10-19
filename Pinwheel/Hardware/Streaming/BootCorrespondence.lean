import Pinwheel.Hardware.Streaming.Initialization
import Pinwheel.Hardware.Streaming.InitializedSession
import Pinwheel.Program.StreamingBootPins

/-! Physical boot transport. Loader acceptance is derived from actual free
metadata; it is not supplied as an agreement premise. -/
namespace Pinwheel.Hardware.Streaming.BootCorrespondence
open Pinwheel.Hardware Pinwheel.Program.Streaming Initialization

theorem core_inputs (s : Package.State a) (pin : Session.Pins) (control : Host.BootControl.State)
    (project : Host.BootControl.project (HostCorrespondence.stateFromValues s.frontend) = control) :
    (fun {w} => s.coreInputs (.typed a) (SessionCorrespondence.pins pin) (w := w)) =
      @HostCorrespondence.commandValues (Host.BootControl.command (pin.host {}) control) := by
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
  have command := Host.BootControl.command_correct (pin.host {}) (HostCorrespondence.stateFromValues s.frontend)
  rw [project] at command
  rw [command]

def metadata (p : Program) (n : Nat) (installed : Bool) : Metadata :=
  if installed then (metadataAfter p n).commit p else metadataAfter p n

structure Related (image : Compiled source idle) (control : Host.BootControl.State) (n : Nat) (installed : Bool)
    (actual : Package.State a) (sourceCore : State a) : Prop where
  project : Host.BootControl.project (HostCorrespondence.stateFromValues actual.frontend) = control
  core : (fun {w} => actual.core (w := w)) = @Initialization.values a (metadata image.program n installed) sourceCore
  phase : sourceCore.phase = .free
  generation : sourceCore.generation = if installed then 1 else 0
  transfer : sourceCore.transfer = 0
  structural : sourceCore.Structural
  within : n ≤ image.program.length
  complete : installed = true → n = image.program.length

theorem rejected_quiet (i : Values Core.Input) (r : Values (Core.Register a))
    (command : i .command = 0) (tx : i .txPush = 0) (rx : i .rxPop = 0) :
    (Core.circuit a).observe i r .rejected = 0 := by
  simp [Core.circuit,Circuit.observe,Core.output,Core.rejected,Core.both,Core.either,
    Core.cmd,Expr.eval,command,tx,rx]

theorem rejected_write (metadata : Metadata) (s : State a) (i : Values Core.Input)
    (address : BitVec 6) (word : BitVec 64) (input : Write i address word)
    (phase : s.phase = .free) (tx : i .txPush = 0) (rx : i .rxPop = 0) :
    (Core.circuit a).observe i (values metadata s) .rejected = 0 := by
  have reset : Core.resetting.eval i (values metadata s) = 0 := by
    simp [Core.resetting,Core.cold,Core.warm,Core.cmd,Core.both,Core.either,Expr.eval,input.cold,input.command]
  have writing : Core.writing.eval i (values metadata s) = 1 := by
    simp [Core.writing,Core.free,Core.both,Core.cmd,Expr.eval,reset,values,phase,Phase.code,input.command]
  simp [Core.circuit,Circuit.observe,Core.output,Core.rejected,Core.both,Core.either,
    Expr.eval,reset,writing,tx,rx]

theorem rejected_commit (p : Program) (metadata : Metadata) (s : State a) (i : Values Core.Input)
    (input : Commit p i) (phase : s.phase = .free) (pending : metadata.pending = 1)
    (room : s.generation ≠ 65535#16)
    (covered : ∀ k : Fin 64, k.val < p.length → metadata.written.getLsbD k.val = true)
    (tx : i .txPush = 0) (rx : i .rxPop = 0) :
    (Core.circuit a).observe i (values metadata s) .rejected = 0 := by
  have committing := commit_accepted p metadata s i input phase pending room covered
  simp [Core.circuit,Circuit.observe,Core.output,Core.rejected,Core.both,Core.either,
    Expr.eval,committing,tx,rx]

theorem image_length (image : Compiled source idle) : image.words.length = image.program.length := by
  rw [image.wordsEqual,List.length_map,image.program_length]

theorem image_row (image : Compiled source idle) (n : Nat) (within : n < image.words.length) :
    image.words[n]?.getD 0 = rowWord image.program n := by
  rw [List.getElem?_eq_getElem within,Option.getD_some]
  exact (compiled_row image n (by simpa only [image.wordsEqual,List.length_map] using within)).symm

structure Effects (image : Compiled source idle) (n : Nat) (installed : Bool) (c : Host.Command)
    (before : State a) (nextN : Nat) (nextInstalled : Bool) (after : State a) : Prop where
  step : @Circuit.step _ _ _ (Core.circuit a) (HostCorrespondence.commandValues c)
      (Initialization.values (metadata image.program n installed) before) =
    @Initialization.values a (metadata image.program nextN nextInstalled) after
  rejected : (Core.circuit a).observe (HostCorrespondence.commandValues c)
      (Initialization.values (metadata image.program n installed) before) .rejected = 0
  phase : after.phase = .free
  generation : after.generation = if nextInstalled then 1 else 0
  transfer : after.transfer = before.transfer
  structural : after.Structural
  within : nextN ≤ image.program.length
  complete : nextInstalled = true → nextN = image.program.length

theorem delivery_effects (image : Compiled source idle) (n : Nat) (installed : Bool) (c : Host.Command)
    (before : State a) (phase : before.phase = .free)
    (generation : before.generation = if installed then 1 else 0) (structural : before.Structural)
    (within : n ≤ image.program.length) (complete : installed = true → n = image.program.length)
    (delivery : BootPins.Delivery image.words idle n installed c nextN nextInstalled) :
    ∃ after : State a, Effects image n installed c before nextN nextInstalled after := by
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
    refine ⟨before.sample c.runtime.rawInputs,?_,?_,phase,generation,rfl,sample_structural _ _ structural,within,complete⟩
    · funext w port
      exact idle_step _ _ _ (coldInput safe) command phase port
    · exact rejected_quiet _ _ command (txInput safe) (rxInput safe)
  | write safe uninstalled live command address word =>
    have actualWrite : Write (HostCorrespondence.commandValues c) (BitVec.ofNat 6 n) (rowWord image.program n) :=
      ⟨coldInput safe,command,address,word.trans (image_row image n live)⟩
    have bound : n+1 ≤ image.program.length := by rw [← image_length image]; omega
    refine ⟨before.sample c.runtime.rawInputs,?_,?_,phase,?_,rfl,sample_structural _ _ structural,bound,?_,⟩
    · subst installed
      funext w port
      exact write_step _ _ _ _ _ actualWrite phase port
    · exact rejected_write _ _ _ _ _ actualWrite phase (txInput safe) (rxInput safe)
    · simpa only [State.sample,uninstalled,Bool.false_eq_true,ite_false] using generation
    · intro impossible; contradiction
  | commit safe uninstalled allWritten command count pins =>
    have allRows : nextN = image.program.length := allWritten.trans (image_length image)
    have actualCommit : Commit image.program (HostCorrespondence.commandValues c) :=
      ⟨coldInput safe,command,count.trans (congrArg (BitVec.ofNat 7) (image_length image)),
        congrArg Engine.Reactive.Pins.levels pins,congrArg Engine.Reactive.Pins.enabled pins⟩
    have pending : (metadataAfter image.program nextN).pending = 1 :=
      metadata_pending _ _ (by rw [allRows]; exact SourceRefinement.length_positive _)
    have room : before.generation ≠ 65535#16 := by
      rw [generation,uninstalled]
      decide
    have covered : ∀ k : Fin 64, k.val < image.program.length →
        (metadataAfter image.program nextN).written.getLsbD k.val = true := by
      rw [allRows]
      exact metadata_covered _ _ (SourceRefinement.length_le _)
    refine ⟨committed before c.runtime.rawInputs,?_,?_,phase,?_,rfl,committed_structural _ _ structural,within,fun _ => allRows⟩
    · subst installed
      funext w port
      exact commit_step _ _ _ _ actualCommit phase pending room covered port
    · subst installed
      exact rejected_commit _ _ _ _ actualCommit phase pending room covered (txInput safe) (rxInput safe)
    · change before.generation + 1#16 = 1#16
      rw [generation,uninstalled]
      rfl

theorem frontend_project (actual : Package.State a) (pin : Session.Pins) (control : Host.BootControl.State)
    (project : Host.BootControl.project (HostCorrespondence.stateFromValues actual.frontend) = control)
    (safe : Host.BootControl.Safe control)
    (rejected : actual.status (.typed a) (SessionCorrespondence.pins pin) .rejected = 0) :
    Host.BootControl.project (HostCorrespondence.stateFromValues
      (actual.step (.typed a) (SessionCorrespondence.pins pin)).frontend) =
      Host.BootControl.step false (pin.host {}) control := by
  let input := HostCorrespondence.inputFromValues
    (actual.frontendInputs (.typed a) (SessionCorrespondence.pins pin))
  have fields : Host.BootControl.input false input = Host.BootControl.input false (pin.host {}) := by
    simp only [input,Host.BootControl.input,HostCorrespondence.inputFromValues,
      Package.State.frontendInputs,Package.Pins.inputs,SessionCorrespondence.pins,
      Session.Pins.host,BitVec.getLsbD_ofBool,decide_true,Bool.true_and]
  have rejectedFalse : input.status.rejected = false := by
    change (actual.status (.typed a) (SessionCorrespondence.pins pin) .rejected).getLsbD 0 = false
    rw [rejected]
    rfl
  have full : HostCorrespondence.stateFromValues
      (actual.step (.typed a) (SessionCorrespondence.pins pin)).frontend =
      Host.step input (HostCorrespondence.stateFromValues actual.frontend) := by
    have equal := HostCorrespondence.step_fromRaw
      (actual.frontendInputs (.typed a) (SessionCorrespondence.pins pin)) actual.frontend
    exact (congrArg HostCorrespondence.stateFromValues equal).trans
      (InitializedSession.frontend_source_roundtrip _)
  rw [full,Host.BootControl.step_correct input _ (by rw [project]; exact safe),project,rejectedFalse]
  unfold Host.BootControl.step
  rw [fields]

theorem Related.step (image : Compiled source idle) (control : Host.BootControl.State)
    (n : Nat) (installed : Bool) (actual : Package.State a) (sourceCore : State a)
    (related : Related image control n installed actual sourceCore) (pin : Session.Pins)
    (safe : Host.BootControl.Safe control)
    (delivery : BootPins.Delivery image.words idle n installed
      (Host.BootControl.command (pin.host {}) control) nextN nextInstalled) :
    ∃ after : State a, Related image (Host.BootControl.step false (pin.host {}) control)
      nextN nextInstalled (actual.step (.typed a) (SessionCorrespondence.pins pin)) after := by
  have input := core_inputs actual pin control related.project
  obtain ⟨after,effects⟩ := delivery_effects image n installed _ sourceCore related.phase
    related.generation related.structural related.within related.complete delivery
  have rejected : actual.status (.typed a) (SessionCorrespondence.pins pin) .rejected = 0 := by
    unfold Package.State.status
    rw [input,related.core]
    exact effects.rejected
  refine ⟨after,frontend_project actual pin control related.project safe rejected,?_,effects.phase,
    effects.generation,effects.transfer.trans related.transfer,effects.structural,effects.within,effects.complete⟩
  change @Circuit.step _ _ _ (Core.circuit a)
    (actual.coreInputs (.typed a) (SessionCorrespondence.pins pin)) actual.core = _
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

theorem certified_run (image : Compiled source idle) (control : Host.BootControl.State)
    (n : Nat) (installed : Bool) (pins : List Session.Pins)
    (certificate : BootPins.Certified image.words idle control n installed pins)
    (actual : Package.State a) (sourceCore : State a)
    (related : Related image control n installed actual sourceCore) :
    ∃ final : Session.State a, Initialized image
      (actual.run (.typed a) (pins.map SessionCorrespondence.pins)) final := by
  induction certificate generalizing actual sourceCore with
  | nil control n installed complete done phase ready active =>
    have allRows : n = image.program.length := complete.trans (image_length image)
    have core : (fun {w} => actual.core (w := w)) =
        @SourceRefinement.values image.program a (compiledImage image) sourceCore := by
      rw [related.core]
      simp only [metadata,done,↓reduceIte,allRows]
      exact values_installed image.program (@compiledCanonical source idle image) sourceCore
    have generation : sourceCore.generation = 1 := by
      simpa only [done,↓reduceIte] using related.generation
    refine ⟨⟨HostCorrespondence.stateFromValues actual.frontend,sourceCore⟩,?_,related.structural,
      related.phase,generation,related.transfer,?_,?_,?_⟩
    · apply InitializedSession.state_ext
      · exact (HostCorrespondence.state_roundtrip actual.frontend).symm
      · exact core
    · exact (congrArg Host.BootControl.State.phase related.project).trans phase
    · exact (congrArg Host.BootControl.State.ready related.project).trans ready
    · exact (congrArg Host.BootControl.State.active related.project).trans active
  | cons safe delivery after ih =>
    obtain ⟨next,nextRelated⟩ := Related.step image _ _ _ actual sourceCore related _ safe delivery
    exact ih _ _ nextRelated

theorem cold_related (image : Compiled source idle) :
    Related image BootPins.initialControl 0 false
      (InitializedSession.coldState a (SessionCorrespondence.pins BootPins.coldPin)) ({} : State a) := by
  constructor
  · change Host.BootControl.project (HostCorrespondence.stateFromValues
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
      (startup.run (.typed a)
        (SessionCorrespondence.pins BootPins.coldPin :: pins.map SessionCorrespondence.pins)) final := by
  change ∃ final : Session.State a, Initialized image
    ((startup.step (.typed a) (SessionCorrespondence.pins BootPins.coldPin)).run (.typed a)
      (pins.map SessionCorrespondence.pins)) final
  rw [InitializedSession.cold_correct startup (SessionCorrespondence.pins BootPins.coldPin) rfl]
  exact certified_run image _ _ _ pins certificate _ _ (cold_related image)

theorem spi_initialized (startup : Package.State a) :
    ∃ final : Session.State a, Initialized (spiImage 3)
      (startup.run (.typed a)
        (SessionCorrespondence.pins BootPins.coldPin :: BootPins.spi.map SessionCorrespondence.pins)) final :=
  compiled_initialized (spiImage 3) BootPins.spi BootPins.spi_certified startup

theorem jtag_initialized (startup : Package.State a) :
    ∃ final : Session.State a, Initialized (jtagImage 3)
      (startup.run (.typed a)
        (SessionCorrespondence.pins BootPins.coldPin :: BootPins.jtag.map SessionCorrespondence.pins)) final :=
  compiled_initialized (jtagImage 3) BootPins.jtag BootPins.jtag_certified startup

end Pinwheel.Hardware.Streaming.BootCorrespondence
