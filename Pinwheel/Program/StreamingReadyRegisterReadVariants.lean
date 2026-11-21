import Pinwheel.Program.StreamingReadySegments

/-! Image changes that exercise the checked segment boundary of the same
register-read request. -/
namespace Pinwheel.Program.StreamingReadyRegisterReadVariants

open StreamingReady (I2cProfile)
open StreamingReadySegments

private def moveBranch : Row → Row
  | .branch target onBit => .branch (target + 2) onBit
  | row => row

/-- Put the first ACK in a one-slot row. The guard and cell are reused, and
every forward NACK target moves with its STOP and discard block. -/
def splitRows (profile : I2cProfile) : List Row :=
  let rows := registerReadRows profile
  let stream := rows[3]'(by simp [rows, registerReadRows])
  rows.take 2 ++ [.count 8, stream, .count 1, stream] ++ (rows.drop 4).map moveBranch

/-- The first branch still points to STOP but now takes it on ACK. -/
def invertedAckRows (profile : I2cProfile) : List Row :=
  (registerReadRows profile).set 4 (.branch 20 false)

set_option maxRecDepth 8192 in
/-- Every timely path executes one extra count row and one extra stream fetch.
The proof also checks that neither prefix accounting nor exit kind changes. -/
def splitImage : Image (splitRows .standard) 36 where
  outcomes := registerReadImage.outcomes.map fun end_ => {end_ with coreClocks := end_.coreClocks + 2}
  checked := by decide +kernel

set_option maxRecDepth 8192 in
/-- The structural checker explores both destinations regardless of polarity.
This image deliberately violates the register-read contract. -/
def invertedAckImage : Image (invertedAckRows .standard) 36 where
  outcomes := registerReadImage.outcomes
  checked := by decide +kernel

theorem split_first_byte (profile : I2cProfile) :
    let stream := Row.cell (.stream (StreamingReady.i2cCell profile)
      (some (StreamingReady.i2cGuard profile 1 1)))
    ((splitRows profile).drop 2).take 5 = [.count 8, stream, .count 1, stream, .branch 22 true] := rfl

theorem split_clock_bounds :
    splitImage.outcomes = registerReadImage.outcomes.map
      (fun end_ => {end_ with coreClocks := end_.coreClocks + 2}) := rfl

theorem invertedAck_same_bounds : invertedAckImage.outcomes = registerReadImage.outcomes := rfl

end Pinwheel.Program.StreamingReadyRegisterReadVariants
