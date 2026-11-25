import PinwheelWitness.I2CReadScenario

/-! Prints the settled loop of the I²C witness scenario as the Lean literal
`settledState` (see `PinwheelWitness/I2CReadScenario.lean`). Rerun
after changing the scenario:

  lake env lean --run scripts/print_i2c_witness_settled.lean

The build checks the literal against the scenario, so a stale copy fails. -/
open Pinwheel.Program.StreamingI2CReadWitness

/-- One field; continuation lines keep the columns `repr` laid out, which
structure instances require. -/
def field (name : String) (value : Std.Format) : String :=
  let head := s!"  {name} := "
  let pad := "".pushn ' ' head.length
  head ++ "\n".intercalate ((Std.Format.pretty value 100).splitOn "\n" |>.mapIdx
    fun k line => if k == 0 then line else pad ++ line)

def main : IO Unit := do
  let l := settled
  -- `Vector` prints as its array and a proof hole; print it as `#v[...]`.
  let vectorFix (text : String) : String := Id.run do
    let mut out : Array String := #[]
    for line in (text.replace "{ toArray := #[" "#v[").splitOn "\n" do
      let rest := line.trimAsciiStart.toString
      if rest.startsWith "size_toArray := _ }" then
        let last := out.back!
        out := out.pop.push ((last.dropEndWhile (· == ',')).toString ++
          (rest.drop "size_toArray := _ }".length).toString)
      else
        out := out.push line
    return "\n".intercalate out.toList
  IO.println "def settledState : Loop where"
  IO.println (vectorFix (field "s" (repr l.s)))
  IO.println (field "queue" (repr l.queue))
  IO.println (field "started" (repr l.started))
  IO.println (field "idle" (repr l.idle))
  IO.println (field "raw1" (repr l.raw1))
  IO.println (field "raw2" (repr l.raw2))
  IO.println (field "peer1" (repr l.peer1))
  IO.println (field "peer2" (repr l.peer2))
  IO.println (field "captures" (repr l.captures))
  IO.println (field "accepted" (repr l.accepted))
