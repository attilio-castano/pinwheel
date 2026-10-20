import Pinwheel.Program.StreamingCompile

open Pinwheel.Program.Streaming

example : (spiImage 3).words = [1908414488,53515130905,1908414488,2] := by
  decide +kernel

example : (jtagImage 3).words =
    [0x7de01818,0x7de01818,0x7de01818,0x7de01818,0x7de01818,
     0x75c01818,0x7de01818,0x75c01818,0x75c01818,0x24c75c01819,
     0x7de01818,0x75c01818,2] := by
  decide +kernel

example (duration : Fin 256) : (spiImage duration).program.WellFormed :=
  (spiImage duration).wellFormed

example (duration : Fin 256) : (jtagImage duration).program.WellFormed :=
  (jtagImage duration).wellFormed

example (duration : Fin 256) : (spiImage duration).words.length = 4 := rfl
example (duration : Fin 256) : (jtagImage duration).words.length = 13 := rfl

example : ¬ Supported [.stream {},.stream {},.halt] := by decide +kernel
example : ¬ Supported [.halt] := by decide +kernel
example : ¬ Supported [.stream {},.halt,.halt] := by decide +kernel
example : ¬ Supported [.pulse {transmit := true},.stream {},.halt] := by decide +kernel
example : wordCanonical (1 <<< 50 ||| 1) = false := by decide +kernel
example : wordCanonical (3 <<< 31 ||| 1) = false := by decide +kernel
example : wordCanonical 4 = false := by decide +kernel
example : wordCanonical 10 = false := by decide +kernel

#print axioms cellWord_fields
#print axioms encode_canonical
#print axioms Compiled.program_fetch
#print axioms Compiled.wellFormed
