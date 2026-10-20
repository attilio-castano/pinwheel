import Pinwheel.Hardware.Streaming.BootCorrespondence

/-! The concrete physical boot certificate also derives the actual command
history's ordered Upload/COMMIT grammar. No delivered command list is assumed. -/
namespace Pinwheel.Hardware.Streaming.BootUpload
open Pinwheel.Hardware Pinwheel.Program.Streaming Initialization BootCorrespondence

def projectedHistory (control : Host.BootControl.State) : List Session.Pins → List (Values Core.Input)
  | [] => []
  | pin::rest =>
      @HostCorrespondence.commandValues (Host.BootControl.command (pin.host {}) control) ::
        projectedHistory (Host.BootControl.step false (pin.host {}) control) rest

theorem history_eq (image : Compiled source idle) (control : Host.BootControl.State)
    (n : Nat) (installed : Bool) (pins : List Session.Pins)
    (certificate : BootPins.Certified image.words idle control n installed pins)
    (actual : Package.State a) (sourceCore : State a)
    (related : Related image control n installed actual sourceCore) :
    InitializedSession.coreHistory actual (pins.map SessionCorrespondence.pins) = projectedHistory control pins := by
  induction certificate generalizing actual sourceCore with
  | nil => rfl
  | cons safe delivery after ih =>
    obtain ⟨next,nextRelated⟩ := Related.step image _ _ _ actual sourceCore related _ safe delivery
    change (fun {w} => actual.coreInputs (.typed a) _ (w := w)) :: _ = _ :: _
    rw [core_inputs actual _ _ related.project]
    congr 1
    exact ih _ _ nextRelated

theorem certified_cut (image : Compiled source idle) (control : Host.BootControl.State)
    (n : Nat) (pins : List Session.Pins)
    (certificate : BootPins.Certified image.words idle control n false pins)
    (previous : List (Values Core.Input)) (upload : Upload image.program n previous) :
    ∃ before command suffix, projectedHistory control pins = before ++ command :: suffix ∧
      Upload image.program image.program.length (previous ++ before) ∧ Commit image.program command := by
  induction pins generalizing control n previous with
  | nil =>
    cases certificate with
    | nil _ _ _ _ impossible => contradiction
  | cons pin rest ih =>
    cases certificate with
    | cons safe delivery after =>
      cases delivery with
      | quiet ordinary command =>
        have cold : HostCorrespondence.commandValues
            (Host.BootControl.command (pin.host {}) control) .initialize = 0 := by
          change BitVec.ofBool (Host.BootControl.command (pin.host {}) control).runtime.initialize = 0
          rw [ordinary.cold]
          rfl
        obtain ⟨before,commit,suffix,history,loaded,committing⟩ := ih _ _ after _
          (Upload.idle upload _ cold command)
        refine ⟨@HostCorrespondence.commandValues (Host.BootControl.command (pin.host {}) control) :: before,
          commit,suffix,?_,?_,committing⟩
        · simpa only [projectedHistory,List.cons_append] using congrArg
            (fun rest => @HostCorrespondence.commandValues (Host.BootControl.command (pin.host {}) control) :: rest) history
        · simpa only [List.append_assoc,List.singleton_append] using loaded
      | write ordinary uninstalled live command address word =>
        have write : Write (HostCorrespondence.commandValues (Host.BootControl.command (pin.host {}) control))
            (BitVec.ofNat 6 n) (rowWord image.program n) := by
          refine ⟨?_,command,address,word.trans (image_row image n live)⟩
          change BitVec.ofBool (Host.BootControl.command (pin.host {}) control).runtime.initialize = 0
          rw [ordinary.cold]
          rfl
        have within : n < image.program.length := by rwa [← image_length image]
        obtain ⟨before,commit,suffix,history,loaded,committing⟩ := ih _ _ after _
          (Upload.write upload within _ write)
        refine ⟨@HostCorrespondence.commandValues (Host.BootControl.command (pin.host {}) control) :: before,
          commit,suffix,?_,?_,committing⟩
        · simpa only [projectedHistory,List.cons_append] using congrArg
            (fun rest => @HostCorrespondence.commandValues (Host.BootControl.command (pin.host {}) control) :: rest) history
        · simpa only [List.append_assoc,List.singleton_append] using loaded
      | commit ordinary uninstalled complete command count pins =>
        have committing : Commit image.program
            (HostCorrespondence.commandValues (Host.BootControl.command (pin.host {}) control)) := by
          refine ⟨?_,command,count.trans (congrArg (BitVec.ofNat 7) (image_length image)),
            congrArg Engine.Reactive.Pins.levels pins,congrArg Engine.Reactive.Pins.enabled pins⟩
          change BitVec.ofBool (Host.BootControl.command (pin.host {}) control).runtime.initialize = 0
          rw [ordinary.cold]
          rfl
        refine ⟨[],@HostCorrespondence.commandValues (Host.BootControl.command (pin.host {}) control),
          projectedHistory _ rest,rfl,?_,committing⟩
        have allRows := complete.trans (image_length image)
        simpa only [List.append_nil,← allRows] using upload

def UploadCut (image : Compiled source idle) (actual : Package.State a) (pins : List Session.Pins) : Prop :=
  ∃ before command suffix,
    InitializedSession.coreHistory actual (pins.map SessionCorrespondence.pins) = before ++ command :: suffix ∧
    Upload image.program image.program.length before ∧ Commit image.program command

theorem concrete_cut (image : Compiled source idle) (pins : List Session.Pins)
    (certificate : BootPins.Certified image.words idle BootPins.initialControl 0 false pins) :
    UploadCut image (InitializedSession.coldState a (SessionCorrespondence.pins BootPins.coldPin)) pins := by
  obtain ⟨before,command,suffix,history,loaded,committing⟩ :=
    certified_cut image _ _ pins certificate [] Upload.nil
  refine ⟨before,command,suffix,?_,?_,committing⟩
  · rw [history_eq image _ _ _ pins certificate _ _ (cold_related image)]
    exact history
  · exact loaded

theorem spi_upload : UploadCut (spiImage 3)
    (InitializedSession.coldState a (SessionCorrespondence.pins BootPins.coldPin)) BootPins.spi :=
  concrete_cut (spiImage 3) BootPins.spi BootPins.spi_certified

theorem jtag_upload : UploadCut (jtagImage 3)
    (InitializedSession.coldState a (SessionCorrespondence.pins BootPins.coldPin)) BootPins.jtag :=
  concrete_cut (jtagImage 3) BootPins.jtag BootPins.jtag_certified

end Pinwheel.Hardware.Streaming.BootUpload
