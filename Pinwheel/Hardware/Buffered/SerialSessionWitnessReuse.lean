import Pinwheel.Hardware.Buffered.SerialSessionWitnessRound

/-! An inhabited two-transfer I²C session: every START admission is derived
from actual free hardware, every transfer retains its bounded timeout result,
and matching sampled RELEASE returns the same installed image for reuse. -/
namespace Pinwheel.Hardware.Buffered.SerialSessionWitness
open Pinwheel.Hardware Pinwheel.Program SerialWire Serial.Frames SerialSourceSession
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem started_generation {before} (transaction : Transaction before)
    (starting : Reactive.starting.eval (transaction.framed.coreInputs transaction.dispatch)
      transaction.framed.controller.core = 1) :
    transaction.after.controller.core .generation = before.controller.core .generation := by
  have facts := SpiCircuit.starting_facts _ _ starting
  have noCommit := I2cCanonicalUpload.no_commit transaction.framed.controller
    (transaction.framed.coreInputs transaction.dispatch) (by simp [facts.command])
  have dispatch := I2cCanonicalUpload.no_commit_generation transaction.framed.controller
    (transaction.framed.coreInputs transaction.dispatch) facts.cold (by simp [facts.command]) noCommit
  have held := SerialUpload.quiet_run_hold transaction.delivered.controller
    (SerialUpload.tailCommands transaction) (SerialUpload.tail_quiet transaction)
  rw [SerialUpload.tail_run] at held
  exact held.generation.trans (dispatch.trans (SerialUpload.request_generation transaction))
  done

theorem released_generation {before} (transaction : Transaction before) (sequence : BitVec 16)
    (word : transaction.request.word = releaseWord sequence
      (before.controller.core .generation) (before.controller.core .transfer)) :
    transaction.after.controller.core .generation = before.controller.core .generation := by
  have valid : codeOf transaction.request.word = 0#4 := by
    rw [word]
    exact Serial.Encoding.encode_accepted .release sequence _
  have opcode : transaction.request.word.extractLsb' 144 4 = 4#4 := by
    rw [word]
    exact (release_fields sequence _ _).1
  have input := SerialSourceRelease.operands transaction.framed transaction.dispatch
    transaction.request.word transaction.request.closed opcode valid transaction.dispatchIdle.1
  have noCommit := I2cCanonicalUpload.no_commit transaction.framed.controller
    (transaction.framed.coreInputs transaction.dispatch) (by simp [input.command])
  have dispatch := I2cCanonicalUpload.no_commit_generation transaction.framed.controller
    (transaction.framed.coreInputs transaction.dispatch) input.cold (by simp [input.command]) noCommit
  have held := SerialUpload.quiet_run_hold transaction.delivered.controller
    (SerialUpload.tailCommands transaction) (SerialUpload.tail_quiet transaction)
  rw [SerialUpload.tail_run] at held
  exact held.generation.trans (dispatch.trans (SerialUpload.request_generation transaction))
  done

structure Round (before : SerialPackage.State) where
  start : Transaction before
  release : Transaction start.after
  accepted : Reactive.starting.eval (start.framed.coreInputs start.dispatch) start.framed.controller.core = 1
  timeout : (SerialStartAdmission.sourceAfter I2cSource.source start).core.control = .stopped .timeout
  trace : Trace I2cSource.source before .free .available (start.pins ++ release.pins) release.after .free .available
  transfer : (release.after.controller.core .transfer).toNat = (before.controller.core .transfer).toNat + 1
  generation : release.after.controller.core .generation = before.controller.core .generation

def Round.after (round : Round before) : SerialPackage.State := round.release.after
def Round.pins (round : Round before) : List SerialPackage.Pins := round.start.pins ++ round.release.pins

noncomputable opaque assembleRound (before : SerialPackage.State)
    (installed : Refinement.InstalledSram I2cSource.source I2cCertificate.layout before.controller)
    (free : SerialSourceRelease.Free before.controller) (available : Available before.record)
    (start : Transaction before) (release : Transaction start.after)
    (accepted : Reactive.starting.eval (start.framed.coreInputs start.dispatch) start.framed.controller.core = 1)
    (opcode : start.request.word.extractLsb' 144 4 = 3#4)
    (timeout : (SerialStartAdmission.sourceAfter I2cSource.source start).core.control = .stopped .timeout)
    (sequence : BitVec 16)
    (word : release.request.word = releaseWord sequence
      (start.after.controller.core .generation) (start.after.controller.core .transfer)) : Round before := by
  let startTrace := SerialStartAdmission.start_trace (program := I2cSource.source) start opcode accepted
  have post := startTrace.preserves ⟨available, installed, free⟩
  have related : Refinement.RelatedSram I2cSource.source I2cCertificate.layout
      (start.request.word.extractLsb' 0 32) start.after.controller
      (SerialStartAdmission.sourceAfter I2cSource.source start) := post.2
  let released := releaseTrace release related .timeout timeout sequence word
  have transfer := released_transfer release sequence word
  have generation := released_generation release sequence word
  exact ⟨start, release, accepted, timeout, appendTrace startTrace released,
    by rw [transfer]; exact started_transfer start accepted,
    generation.trans (started_generation start accepted)⟩
  done

@[irreducible] def roundStart (before : SerialPackage.State) (available : Available before.record)
    (sequence : BitVec 16) : Transaction before :=
  SerialStartAdmission.concreteStart before available sequence 0 0 0 0

 theorem roundStart_admitted (before : SerialPackage.State)
    (installed : Refinement.InstalledSram I2cSource.source I2cCertificate.layout before.controller)
    (free : SerialSourceRelease.Free before.controller) (available : Available before.record)
    (room : before.controller.core .transfer ≠ 65535) (sequence : BitVec 16) :
    Reactive.starting.eval ((roundStart before available sequence).framed.coreInputs
      (roundStart before available sequence).dispatch)
      (roundStart before available sequence).framed.controller.core = 1 := by
  unfold roundStart
  exact SerialStartAdmission.concrete_admitted before installed free available sequence 0 0 0 0 room (by decide) (by decide)
  done

theorem roundStart_opcode (before : SerialPackage.State) (available : Available before.record) (sequence : BitVec 16) :
    (roundStart before available sequence).request.word.extractLsb' 144 4 = 3#4 := by
  unfold roundStart SerialStartAdmission.concreteStart
  rw [concrete_word]
  exact SerialStartAdmission.start_opcode sequence (before.controller.core .generation) 0 0 0
  done

theorem roundStart_timeout (before : SerialPackage.State) (available : Available before.record) (sequence : BitVec 16) :
    (SerialStartAdmission.sourceAfter I2cSource.source (roundStart before available sequence)).core.control = .stopped .timeout := by
  unfold roundStart
  exact concrete_timeout before available sequence 0 0 0
  done

@[irreducible] def roundRelease (before : SerialPackage.State) (available : Available before.record)
    (sequence : BitVec 16) : Transaction before :=
  concrete before available (releaseWord sequence (before.controller.core .generation) (before.controller.core .transfer)) 0

theorem roundRelease_word (before : SerialPackage.State) (available : Available before.record)
    (sequence : BitVec 16) :
    (roundRelease before available sequence).request.word =
      releaseWord sequence (before.controller.core .generation) (before.controller.core .transfer) := by
  unfold roundRelease
  exact concrete_word before available _ 0
  done

set_option backward.isDefEq.respectTransparency true in
noncomputable opaque makeRound (before : SerialPackage.State)
    (installed : Refinement.InstalledSram I2cSource.source I2cCertificate.layout before.controller)
    (free : SerialSourceRelease.Free before.controller) (available : Available before.record)
    (room : before.controller.core .transfer ≠ 65535) (startSequence releaseSequence : BitVec 16) :
    Round before :=
  let start := roundStart before available startSequence
  let release := roundRelease start.after start.exact.1 releaseSequence
  assembleRound before installed free available start release
    (roundStart_admitted before installed free available room startSequence)
    (roundStart_opcode before available startSequence)
    (roundStart_timeout before available startSequence) releaseSequence
    (roundRelease_word start.after start.exact.1 releaseSequence)

theorem Round.post {before} (round : Round before)
    (installed : Refinement.InstalledSram I2cSource.source I2cCertificate.layout before.controller)
    (free : SerialSourceRelease.Free before.controller) (available : Available before.record) :
    Available round.after.record ∧
      Refinement.InstalledSram I2cSource.source I2cCertificate.layout round.after.controller ∧
      SerialSourceRelease.Free round.after.controller ∧ round.trace.Observed := by
  exact (round.trace.session available installed free).2
  done

theorem initialized_two_rounds (before : SerialPackage.State) (pin : SerialPackage.Pins)
    (cold : pin.cold = true) (idle : pin.csn = true) :
    ∃ loading : SerialUpload.Loading (before.step pin),
      ∃ first : Round loading.after, ∃ second : Round first.after,
      before.run ((pin :: loading.pins) ++ (first.pins ++ second.pins)) = second.after ∧
      Available second.after.record ∧
      Refinement.InstalledSram I2cSource.source I2cCertificate.layout second.after.controller ∧
      SerialSourceRelease.Free second.after.controller ∧
      second.after.controller.core .generation = 1 ∧ second.after.controller.core .transfer = 2 ∧
      first.trace.Observed ∧ second.trace.Observed := by
  let loading := SerialUpload.concreteLoading (before.step pin) (SerialUpload.cold_available before pin cold idle)
  have boot := SerialUpload.cold_install before pin cold idle loading
  have room : loading.after.controller.core .transfer ≠ 65535 := by rw [boot.2.2.2.2.1]; decide
  let first := makeRound loading.after boot.1 ⟨boot.2.1, boot.2.2.1⟩ boot.2.2.2.2.2.1 room 67 68
  have firstPost := first.post boot.1 ⟨boot.2.1, boot.2.2.1⟩ boot.2.2.2.2.2.1
  have firstTransfer : first.after.controller.core .transfer = 1 := by
    apply BitVec.eq_of_toNat_eq
    change (first.release.after.controller.core .transfer).toNat = (1#16).toNat
    rw [first.transfer, boot.2.2.2.2.1]
    rfl
  have nextRoom : first.after.controller.core .transfer ≠ 65535 := by rw [firstTransfer]; decide
  let second := makeRound first.after firstPost.2.1 firstPost.2.2.1 firstPost.1 nextRoom 69 70
  have secondPost := second.post firstPost.2.1 firstPost.2.2.1 firstPost.1
  refine ⟨loading, first, second, ?_, secondPost.1, secondPost.2.1, secondPost.2.2.1,
    ?_, ?_, firstPost.2.2.2, secondPost.2.2.2⟩
  · simp only [SerialPackage.State.run, List.foldl_append]
    change ((before.run (pin :: loading.pins)).run first.pins).run second.pins = _
    rw [boot.2.2.2.2.2.2]
    change (loading.after.run (first.start.pins ++ first.release.pins)).run
      (second.start.pins ++ second.release.pins) = _
    rw [first.trace.run_pins]
    exact second.trace.run_pins
  · exact second.generation.trans (first.generation.trans boot.2.2.2.1)
  · apply BitVec.eq_of_toNat_eq
    change (second.release.after.controller.core .transfer).toNat = (2#16).toNat
    rw [second.transfer, firstTransfer]
    rfl
  done

end Pinwheel.Hardware.Buffered.SerialSessionWitness
