import Pinwheel.Hardware.Stream.FifoCircuit

namespace Pinwheel.Hardware.Stream

inductive Joint (R S : Nat → Type) : Nat → Type where
  | left : R w → Joint R S w
  | right : S w → Joint R S w

def Joint.values (r : Values R) (s : Values S) : Values (Joint R S)
  | _, .left p => r p
  | _, .right p => s p

def Joint.position (r : Interface R) (s : Interface S) : Joint R S w → Fin (r.size + s.size)
  | .left p => ⟨(r.position p).val, by have := (r.position p).isLt; omega⟩
  | .right p => ⟨r.size + (s.position p).val, by have := (s.position p).isLt; omega⟩

def Joint.signal (r : Interface R) (s : Interface S) (k : Fin (r.size + s.size)) : Sigma (Joint R S) :=
  if h : k.val < r.size then let p := r.signal ⟨k.val, h⟩; ⟨p.1, .left p.2⟩
  else let p := s.signal ⟨k.val - r.size, by omega⟩; ⟨p.1, .right p.2⟩

theorem Joint.signal_position (r : Interface R) (s : Interface S) (p : Joint R S w) :
    signal r s (position r s p) = ⟨w, p⟩ := by
  cases p with
  | left p =>
    unfold position signal
    rw [dif_pos (r.position p).isLt]
    exact congrArg (fun q : Sigma R => (⟨q.1, .left q.2⟩ : Sigma (Joint R S))) (r.signal_position p)
  | right p =>
    unfold position signal
    rw [dif_neg (Nat.not_lt_of_ge (Nat.le_add_right r.size _))]
    have he : (⟨r.size + (s.position p).val - r.size, by have := (s.position p).isLt; omega⟩ :
        Fin s.size) = s.position p := Fin.ext (Nat.add_sub_cancel_left _ _)
    rw [he]
    exact congrArg (fun q : Sigma S => (⟨q.1, .right q.2⟩ : Sigma (Joint R S))) (s.signal_position p)

theorem Joint.position_signal (r : Interface R) (s : Interface S) (k : Fin (r.size + s.size)) :
    position r s (signal r s k).2 = k := by
  by_cases h : k.val < r.size
  · have hs : signal r s k =
        ⟨(r.signal ⟨k.val, h⟩).1, .left (r.signal ⟨k.val, h⟩).2⟩ := dif_pos h
    have hp := congrArg (fun p : Sigma (Joint R S) => position r s p.2) hs
    simpa only [position, Interface.position_signal] using hp
  · have hs : signal r s k =
        ⟨(s.signal ⟨k.val - r.size, by omega⟩).1,
          .right (s.signal ⟨k.val - r.size, by omega⟩).2⟩ := dif_neg h
    have hp := congrArg (fun p : Sigma (Joint R S) => position r s p.2) hs
    simp only [position, Interface.position_signal] at hp
    exact hp.trans (Fin.ext (by dsimp; omega))

def Joint.interface (r : Interface R) (s : Interface S) : Interface (Joint R S) where
  size := r.size + s.size
  signal := signal r s
  position := position r s
  signal_position := signal_position r s
  label := fun p => "state_" ++ Nat.repr (position r s p).val
  unique := by
    intro a b h
    simp only [position_signal, String.append_right_inj] at h
    exact Fin.ext (Nat.repr_injective h)

/-- The circuit builder's typed input bundle. No port names participate in wiring. -/
def inputExpr (rst v r : Expr I R 1) (d : Expr I R w) : {b : Nat} → In w b → Expr I R b
  | _, .at ⟨0, _⟩ => rst
  | _, .at ⟨1, _⟩ => v
  | _, .at ⟨2, _⟩ => r
  | _, .at ⟨3, _⟩ => d
  | _, .at ⟨k + 4, h⟩ => False.elim (by change k + 4 < 4 at h; omega)

/-- A probe has reset and valid low, so a certified component exposes state-only
offers and its ready path without introducing a combinational dependency cycle. -/
def probeInput (r : Expr I R 1) : {b : Nat} → In w b → Expr I R b :=
  inputExpr (.lit 0) (.lit 0) r (.lit 0)

def serialReady (b : Circuit (In wm) S (Out wo)) : Expr (In wi) (Joint R S) 1 :=
  (b.output inReady).bind (probeInput (.input ready)) (fun p => .reg (.right p))

def serialOffer (a : Circuit (In wi) R (Out wm)) (o : Out wm v) : Expr (In wi) (Joint R S) v :=
  (a.output o).bind (probeInput (.lit 0)) (fun p => .reg (.left p))

def serialLeft (b : Circuit (In wm) S (Out wo)) : {v : Nat} → In wi v → Expr (In wi) (Joint R S) v :=
  inputExpr (.input reset) (.input valid) (serialReady b) (.input payload)

def serialRight (a : Circuit (In wi) R (Out wm)) : {v : Nat} → In wm v → Expr (In wi) (Joint R S) v :=
  inputExpr (.input reset) (serialOffer a outValid) (.input ready) (serialOffer a outData)

def serialCircuit (a : Circuit (In wi) R (Out wm)) (b : Circuit (In wm) S (Out wo)) :
    Circuit (In wi) (Joint R S) (Out wo) where
  next := fun p => match p with
    | .left p => (a.next p).bind (serialLeft b) (fun p => .reg (.left p))
    | .right p => (b.next p).bind (serialRight a) (fun p => .reg (.right p))
  output := streamOutputs
    ((a.output inReady).bind (serialLeft b) (fun p => .reg (.left p)))
    ((b.output outValid).bind (serialRight a) (fun p => .reg (.right p)))
    ((b.output outData).bind (serialRight a) (fun p => .reg (.right p)))

end Pinwheel.Hardware.Stream
