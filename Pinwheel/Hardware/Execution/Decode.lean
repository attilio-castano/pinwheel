import Pinwheel.Hardware.Execution.RecordProofs
import Pinwheel.Hardware.Execution.Memory

namespace Pinwheel.Hardware.Execution

def clean (word mask : BitVec 64) : Bool := word &&& ~~~mask == 0

def captureValid (bits : BitVec 6) : Bool := bits[0] || bits == 0

/-- Canonical record checks expressed solely with fixed-width masks and comparisons. -/
def validValue (word : BitVec 64) : Bool :=
  let f := unpack word
  let shape := if f.kind = 0 then clean word 0x7e001ffff
    else if f.kind = 1 then clean word 0x601ffff
    else if f.kind = 2 then
      if f.finish = 0 then clean word 0x7fffe01ffff
      else if f.finish = 1 then clean word 0x7f87fffe01ffff
      else if f.finish = 2 then clean word 0x7ffffffffe01ffff else false
    else if f.kind = 3 then clean word 0x1fffffff
    else word == 4
  shape && captureValid f.entry && captureValid f.terminal

inductive Port : Nat → Type where
  | valid : Port 1
  | kind : Port 3
  | levels : Port 3
  | enabled : Port 3
  | duration : Port 8
  | budget : Port 8
  | check : Port 4
  | entry : Port 6
  | terminal : Port 6
  | finish : Port 2
  | sample : Port 4
  | yes : Port 8
  | no : Port 8

def fieldValue (f : Fields) : {w : Nat} → Port w → BitVec w
  | _, .valid => 0
  | _, .kind => f.kind | _, .levels => f.levels | _, .enabled => f.enabled
  | _, .duration => f.duration | _, .budget => f.budget | _, .check => f.check
  | _, .entry => f.entry | _, .terminal => f.terminal | _, .finish => f.finish
  | _, .sample => f.sample | _, .yes => f.yes | _, .no => f.no

def value (word : BitVec 64) : {w : Nat} → Port w → BitVec w
  | _, .valid => BitVec.ofBool (validValue word)
  | _, port => fieldValue (unpack word) port

def bor (a b : Expr I R 1) : Expr I R 1 := .inv (.band (.inv a) (.inv b))
def cleanLogic (word : Expr I R 64) (mask : BitVec 64) : Expr I R 1 :=
  .zero (.band word (.lit (~~~mask)))
def captureLogic (bits : Expr I R 6) : Expr I R 1 := bor (.slice 0 1 (by decide) bits) (.zero bits)

def validLogic (word : Expr I R 64) : Expr I R 1 :=
  let kind := Expr.slice 0 3 (by decide) word
  let finish := Expr.slice 41 2 (by decide) word
  let shape := Expr.mux (.equal kind (.lit 0)) (cleanLogic word 0x7e001ffff)
    (.mux (.equal kind (.lit 1)) (cleanLogic word 0x601ffff)
      (.mux (.equal kind (.lit 2))
        (.mux (.equal finish (.lit 0)) (cleanLogic word 0x7fffe01ffff)
          (.mux (.equal finish (.lit 1)) (cleanLogic word 0x7f87fffe01ffff)
            (.mux (.equal finish (.lit 2)) (cleanLogic word 0x7ffffffffe01ffff) (.lit 0))))
        (.mux (.equal kind (.lit 3)) (cleanLogic word 0x1fffffff) (.equal word (.lit 4)))))
  .band (.band shape (captureLogic (.slice 29 6 (by decide) word)))
    (captureLogic (.slice 35 6 (by decide) word))

def logic (word : Expr I R 64) : {w : Nat} → Port w → Expr I R w
  | _, .valid => validLogic word
  | _, .kind => .slice 0 3 (by decide) word
  | _, .levels => .slice 3 3 (by decide) word
  | _, .enabled => .slice 6 3 (by decide) word
  | _, .duration => .slice 9 8 (by decide) word
  | _, .budget => .slice 17 8 (by decide) word
  | _, .check => .slice 25 4 (by decide) word
  | _, .entry => .slice 29 6 (by decide) word
  | _, .terminal => .slice 35 6 (by decide) word
  | _, .finish => .slice 41 2 (by decide) word
  | _, .sample => .slice 43 4 (by decide) word
  | _, .yes => .slice 47 8 (by decide) word
  | _, .no => .slice 55 8 (by decide) word

end Pinwheel.Hardware.Execution
