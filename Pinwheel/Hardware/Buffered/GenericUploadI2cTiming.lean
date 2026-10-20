import Pinwheel.Hardware.Buffered.GenericWireSessionInitialized
import Pinwheel.Hardware.Buffered.I2cTimingLoading

/-! Static packing instance for every symbolic timing pair.  The certificate
is separate from, and supplies no premise about, any actual uploaded state. -/
namespace Pinwheel.Hardware.Buffered.I2cTiming
open Pinwheel.Hardware Pinwheel.Program

private theorem projected_rows (duration budget : Fin 256) (k : BitVec 6) :
    SramExecution.projectedRow 50 (rows duration budget) k = rows duration budget k := by
  by_cases live : k.toNat < 50
  · simp [SramExecution.projectedRow,SramExecution.live,SramCandidates.project,live]
  · simp [SramExecution.projectedRow,SramExecution.live,SramCandidates.project,live,
      row_tail duration budget k (by omega)]

def uploadImage (duration budget : Fin 256) : GenericUpload.Image (source duration budget) (layout duration budget) where
  word := word duration budget
  control := I2cSource.control
  branchIndex := I2cSource.branchIndex
  dictionary := I2cSource.dictionary
  packed := by
    change SramExecution.residentWords 50 (rows duration budget) I2cSource.dictionary = fullWords duration budget
    funext k
    simp only [SramExecution.residentWords,projected_rows,rows,full_words,
      BitVec.extractLsb'_append_eq_left,BitVec.extractLsb'_append_eq_right]

def programImage (duration budget : Fin 256) : GenericWireSession.ProgramImage :=
  ⟨source duration budget,layout duration budget,uploadImage duration budget⟩

end Pinwheel.Hardware.Buffered.I2cTiming
