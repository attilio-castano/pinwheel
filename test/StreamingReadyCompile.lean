import Pinwheel.Program.StreamingReadyCompile

open Pinwheel.Program.StreamingReady

example : (i2cImage .standard).words =
    [0x07fc000000000004,0x20801818,0x47d4080e80401819,0x30c01818,
     0x07d4000000800004,0x20801818,2] := by decide +kernel

example (profile : I2cProfile) : (i2cImage profile).program.WellFormed :=
  (i2cImage profile).wellFormed

example (profile : I2cProfile) : (i2cImage profile).words.length = 7 := rfl

example (old : Pinwheel.Program.Streaming.Instruction) :
    encode (liftInstruction old) = Pinwheel.Program.Streaming.encode old := encode_lift old

example : ¬ Supported [.stream {} none,.stream {} none,.halt] := by decide +kernel
example : ¬ Supported [.driveWait {} {},.halt] := by decide +kernel
example : ¬ Supported [.stream {} none,.halt,.fault] := by decide +kernel
example : ¬ Supported [.pulse {transmit := true},.stream {} none,.halt] := by decide +kernel
example : ¬ Supported [.stream {} (some ⟨0,1,.unbounded⟩),.halt] := by decide +kernel
example : wordCanonical 4 = true := by decide +kernel
example : wordCanonical (1 <<< 63 ||| 4) = false := by decide +kernel
example : wordCanonical (1 <<< 50 ||| 1) = false := by decide +kernel
example : wordCanonical (1 <<< 52 ||| 4) = false := by decide +kernel
example : wordCanonical (1 <<< 25 ||| 4) = false := by decide +kernel
example : wordCanonical (1 <<< 3 ||| 4) = false := by decide +kernel
example : wordCanonical (1 <<< 62 ||| 1) = true := by decide +kernel
example : wordCanonical (3 <<< 31 ||| 1) = false := by decide +kernel

def asymmetric : I2cProfile :=
  ⟨15,2,30,1,28,by decide,by decide,by decide,by decide⟩

example : (i2cImage asymmetric).words[3]? = some 0x30c01078 := by decide +kernel
example : (i2cStopLow asymmetric).cell.lowDuration.val + 1 = 16 := rfl
example : (i2cStopLow asymmetric).cell.highDuration.val + 1 = 3 := rfl
example : (i2cHold asymmetric 2).cell.lowDuration.val + 1 = 3 := rfl
example (profile : I2cProfile) : (i2cSource profile)[3]? = some (i2cStopLow profile) :=
  (i2c_stop_low_fields profile).1

#print axioms i2c_stop_low_fields
#print axioms i2c_stop_low_cycles
#print axioms encode_fields
#print axioms encode_canonical
#print axioms Compiled.program_fetch
#print axioms Compiled.installed
#print axioms i2c_supported
