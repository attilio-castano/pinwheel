import Pinwheel.Hardware.Serial.Frame

/-! The whole chip, as one Lean object.

Tiny Tapeout gives a user project eight inputs, eight outputs, eight
bidirectional pins, a clock, `rst_n` and `ena`. `Chip.netlist` puts any core
with the loader machine's ports behind that boundary:

    pins → pin map → two-register samplers → serial loader → core → output map

Each layer is a `Feeder` (or an output map), so the chip is the core's own
expressions rewired, and `trace_eq` says what it does for every pin history: the
core takes exactly the edges it would take on the history the layers feed it,
and the pins show the output map of what the core shows. Nothing here depends on
which core it is; with a core proved against the reference machine, the chip is
the reference machine on the fed history (`reference_trace`).

Pin assignment: `ui_in[0]` serial clock, `ui_in[1]` serial data, `ui_in[2]`
select (active low); `uio[2:0]` the three protocol pins, driven through their
enables, with `uio_in[1:0]` sampled as the engine's inputs; `uo_out` shows busy,
valid, pending, active, rejected and the engine's mode. `rst_n` low is `init`. -/
namespace Pinwheel.Hardware.Chip
open Loader

inductive Pin : Nat → Type where
  | uiIn : Pin 8 | uioIn : Pin 8 | ena : Pin 1 | rstN : Pin 1

structure Pins where
  uiIn : BitVec 8 := 4
  uioIn : BitVec 8 := 0
  ena : Bool := true
  rstN : Bool := true
  deriving Repr

def Pins.values (p : Pins) : Values Pin
  | _, .uiIn => p.uiIn | _, .uioIn => p.uioIn
  | _, .ena => BitVec.ofBool p.ena | _, .rstN => BitVec.ofBool p.rstN

inductive Output : Nat → Type where
  | uoOut : Output 8 | uioOut : Output 8 | uioOe : Output 8

/-! ### The pin map: wires and one inverter -/

def pinMap : Feeder Pin NoRegister Serial.Input where
  input := fun p => match p with
    | .init => .inv (.input .rstN)
    | .sck => .slice 0 1 (by decide) (.input .uiIn)
    | .mosi => .slice 1 1 (by decide) (.input .uiIn)
    | .csn => .slice 2 1 (by decide) (.input .uiIn)
    | .incoming => .slice 0 2 (by decide) (.input .uioIn)
  next := fun r => nomatch r

/-- What the pins mean. -/
def wired (p : Pins) : Serial.Inputs :=
  { init := !p.rstN
    sck := p.uiIn.getLsbD 0
    mosi := p.uiIn.getLsbD 1
    csn := p.uiIn.getLsbD 2
    incoming := p.uioIn.extractLsb' 0 2 }

private theorem bit_slice (x : BitVec 8) (k : Nat) :
    x.extractLsb' k 1 = BitVec.ofBool (x.getLsbD k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h0 : i = 0 := by omega
  subst h0
  simp

private theorem not_bool (a : Bool) : ~~~BitVec.ofBool a = BitVec.ofBool (!a) := by
  cases a <;> rfl

def pinModel : Feeder.Model pinMap Pins Unit Serial.Inputs where
  outer := Pins.values
  state := fun _ => NoRegister.values
  inner := Serial.Inputs.values
  feed := fun p _ => wired p
  step := fun _ _ => ()
  feed_correct := fun p _ _ q => by
    cases q with
    | init => simp only [pinMap, Expr.eval, Pins.values, not_bool]; rfl
    | sck => simp only [pinMap, Expr.eval, Pins.values, bit_slice]; rfl
    | mosi => simp only [pinMap, Expr.eval, Pins.values, bit_slice]; rfl
    | csn => simp only [pinMap, Expr.eval, Pins.values, bit_slice]; rfl
    | incoming => rfl
  step_correct := fun _ _ _ r => nomatch r

/-! ### The output map -/

def outputs : {w : Nat} → Output w → Expr Machine.Output NoRegister w
  | _, .uoOut =>
    (.concat (.input (.core (.state .mode)))
      (.concat (.input (.control .rejected))
        (.concat (.input (.control (.state .active)))
          (.concat (.input (.control (.state .pending)))
            (.concat (.input (.control (.state .valid))) (.input (.core .busy)))))) :
      Expr Machine.Output NoRegister (3 + (1 + (1 + (1 + (1 + 1))))))
  | _, .uioOut => (.concat (.lit (0 : BitVec 5)) (.input (.core (.state .levels))) :
      Expr Machine.Output NoRegister (5 + 3))
  | _, .uioOe => (.concat (.lit (0 : BitVec 5)) (.input (.core (.state .enabled))) :
      Expr Machine.Output NoRegister (5 + 3))

/-- What the pins show of what the core shows. -/
def shown (o : Values Machine.Output) : Values Output :=
  fun q => (outputs q).eval o NoRegister.values

/-- Both observations of an edge, as the pins show them. -/
def shownEdge (e : Values Machine.Output × Values Machine.Output) : Values Output × Values Output :=
  (shown e.1, shown e.2)

/-! ### The chip -/

abbrev Register (R : Nat → Type) :=
  Extended (Extended (Extended R Serial.Register) (Feeder.Sampled Serial.Input)) NoRegister

/-- Any core with the loader machine's ports, behind the Tiny Tapeout boundary. -/
def netlist (n : Netlist R Machine.Output Machine.Input) : Netlist (Register R) Output Pin :=
  (pinMap.wrap (Feeder.sampler.wrap (Serial.receiver.wrap n))).mapOutputs outputs

/-- The chip's own state: the two sampler stages and the receiver. -/
structure State where
  first : Serial.Inputs := {}
  second : Serial.Inputs := {}
  receiver : Serial.State := {}

def sampling : Feeder.Model (Feeder.sampler (J := Serial.Input)) Serial.Inputs
    (Serial.Inputs × Serial.Inputs) Serial.Inputs :=
  Feeder.samplerModel Serial.Inputs.values

/-- The registers of the chip: the core's, the receiver's, the samplers'. -/
def values (s : Values R) (x : State) : Values (Register R) :=
  Extended.values
    (Extended.values (Extended.values s x.receiver.values) (sampling.state (x.first, x.second)))
    (pinModel.state ())

/-- What the receiver sees, from what the pins show: two samples late. -/
def sampled (x : State) (pins : List Pins) : List (Serial.Inputs × Serial.Inputs) :=
  sampling.history (x.first, x.second) (pinModel.history () (pins.map fun p => (p, p)))

/-- What the core consumes and sees after each edge, from what the pins show. -/
def history (x : State) (pins : List Pins) : List (Machine.Inputs × Machine.Inputs) :=
  Serial.model.history x.receiver (sampled x pins)

/-- **The chip, for every pin history and every core**: the core takes exactly the
edges it would take on the fed history, and the pins show the output map of
what it shows. -/
theorem trace_eq (n : Netlist R Machine.Output Machine.Input) (s : Values R) (x : State)
    (pins : List Pins) :
    ((netlist n).componentOf Pins.values).trace (values s x) pins =
      ((n.componentOf Machine.Inputs.values).pairTrace s (history x pins)).map shownEdge := by
  have hmap := Timed.Component.pairTrace_map
    ((pinMap.wrap (Feeder.sampler.wrap (Serial.receiver.wrap n))).componentOf Pins.values)
    ((netlist n).componentOf Pins.values) shown
    (fun i st => funext fun w => funext fun r =>
      Netlist.mapOutputs_step _ outputs (Pins.values i) st r)
    (fun i st => funext fun w => funext fun o =>
      Netlist.mapOutputs_observe _ outputs (Pins.values i) st o)
    (values s x) (pins.map fun p => (p, p))
  rw [← Timed.Component.pairTrace_same, hmap]
  congr 1
  exact (Feeder.Model.pairTrace_eq pinModel _ _ () _).trans
    ((Feeder.Model.pairTrace_eq sampling _ _ (x.first, x.second) _).trans
      (Feeder.Model.pairTrace_eq Serial.model n s x.receiver _))

/-! ### What the core consumes -/

/-- The inputs the core consumes, edge by edge. -/
def consumed (x : State) (pins : List Pins) : List Machine.Inputs := (history x pins).map Prod.fst

theorem pin_consumed (pins : List Pins) : pinModel.consumed () pins = pins.map wired := by
  induction pins with
  | nil => rfl
  | cons p rest ih => simp only [Feeder.Model.consumed, List.map, ih]; rfl

theorem serial_consumed (s : Serial.State) (samples : List Serial.Inputs) :
    Serial.model.consumed s samples = Serial.fed s samples := by
  induction samples generalizing s with
  | nil => rfl
  | cons i rest ih => simp only [Feeder.Model.consumed, Serial.fed, ih]; rfl

/-- The receiver sees the pins two samples late, after what the samplers held. -/
theorem consumed_delayed (x : State) (pins : List Pins) (a b : Pins) :
    consumed x (pins ++ [a, b]) =
      Serial.fed x.receiver (x.second :: x.first :: pins.map wired) := by
  unfold consumed history sampled
  rw [Feeder.Model.history_fst, Feeder.Model.history_fst, Feeder.Model.history_fst, serial_consumed]
  congr 1
  have hpins : ((pins ++ [a, b]).map fun p => (p, p)).map Prod.fst = pins ++ [a, b] := by
    simp [List.map_map, Function.comp_def]
  rw [hpins, pin_consumed, List.map_append]
  exact Feeder.sampler_consumed Serial.Inputs.values x.first x.second (pins.map wired) (wired a) (wired b)

/-- **From a host session on the pins to commands at the core.** If the samplers
hold idle samples and the receiver is between frames, any session on the pins —
followed by two more samples of anything — delivers exactly its commands to the
core, in order, among quiet edges. -/
theorem session_delivers (x : State) (hcount : x.receiver.count = 0) (hfire : x.receiver.fire = false)
    (hfirst : Serial.Idle x.first) (hsecond : Serial.Idle x.second) (pins : List Pins) (a b : Pins)
    (cs : List (BitVec 3 × BitVec 64)) (hs : Serial.Session (pins.map wired) cs) :
    Machine.Delivers (consumed x (pins ++ [a, b])) cs := by
  rw [consumed_delayed]
  exact (Serial.session_delivers (.idle hsecond (.idle hfirst hs)) x.receiver hcount hfire).1

/-- The chip's own state after a pin history. -/
def advance (x : State) (pins : List Pins) : State :=
  let stages := sampling.run (x.first, x.second) (pins.map wired)
  ⟨stages.1, stages.2, Serial.model.run x.receiver (sampling.consumed (x.first, x.second) (pins.map wired))⟩

/-- The fed history splits where the pin history does. -/
theorem history_append (x : State) (a b : List Pins) :
    history x (a ++ b) = history x a ++ history (advance x a) b := by
  unfold history sampled advance
  rw [List.map_append, Feeder.Model.history_append, Feeder.Model.history_append,
    Feeder.Model.history_append, Feeder.Model.history_fst, Feeder.Model.history_fst]
  have hpins : (a.map fun p => (p, p)).map Prod.fst = a := by
    simp [List.map_map, Function.comp_def]
  rw [hpins, pin_consumed]

/-! ### What the pins can reach -/

/-- Every pin launches. -/
def anyPin : Launch Pin := fun _ => some 0

/-- **No pin has a combinational path to the core, the receiver or an output**:
every pin ends at one flip-flop of the first sampler stage. -/
theorem pins_shielded (pick : Pick) (cost : Cost) (n : Netlist R Machine.Output Machine.Input)
    (r : Extended R Serial.Register w) :
    (pinMap.wrap (Feeder.sampler.wrap (Serial.receiver.wrap n))).arrivalNext pick cost anyPin
      (fun _ => none) (.inner (.inner r)) = none := by
  rw [Feeder.wrap_arrivalNext]
  exact Feeder.wrap_shields pick cost Feeder.sampler (Serial.receiver.wrap n) _
    (fun p => Feeder.sampler_registered pick cost _ p) r

end Pinwheel.Hardware.Chip
