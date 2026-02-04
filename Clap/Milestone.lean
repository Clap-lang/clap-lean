import Clap.Circuit
import Clap.Compilation
import Clap.Spec
import Clap.Compiler.Basic

namespace Clap

open Clap Clap.Spec

variable {p : ℕ} [Fact (Nat.Prime p)]

/-
  This example showcases a circuit that takes a vector of field
  elements (the tye `ZMod p`) of length 3 and simply checks that all
  elements are zero using a very natural for loop.
-/

def ex_vec (xs : Vector (ZMod p) 3) : Option Unit := do
  for x in xs do
    eq0 x
  accept

/-
   This is how we call the first step of the compiler to curry the circuit.
   Note: in the future everything will be called by a single command,
   right now it's still split in multiple steps.
-/
#compile Clap.ex_vec

/-
The compiler produces the curried version:

def ex_vec_curried (x0 x1 x2: ZMod p) : Option Unit := do
  for x in #[x0,x1,x2] do
    eq0 x
  accept

were the vector is replaced with a series of arguments, each being a
single field elements.
-/

/-
  Here we tranform the curried version, which is still Lean code, into
  our Circuit IR of type `Circuit p`.
-/
def extract_vec :
  { c : Circuitₑ p // Simulation.sBisim (ex_vec_curried (p := p)) c.eval } := by
  extract using ex_vec_curried

-- This is what the extracted circuit looks like
abbrev extracted_vec : Circuitₑ p := (extract_vec (p := p)).1

example : extracted_vec (p := p) =
  .lam fun x_0 =>
  .lam fun x_1 =>
  .lam fun x_2 =>
  .eq0 x_0 (
  .eq0 x_1 (
  .eq0 x_2
  .nil)) := rfl

/-
  This example showcases the use of a structure (equivalent to struct
  in Rust).
  Notice that in the body of the circuit `ex_point` we can freely
  refer to any field of the struct.
-/

structure Point3 (p : ℕ) where
  x : ZMod p
  y : ZMod p
  z : ZMod p

def ex_point (point : Point p) : Option Unit := do
  eq0 (point.x + point.y)
  eq0 (point.x + point.z)
  accept

#compile Clap.ex_point

def extracted_point :
  { c:Circuitₑ p // Simulation.sBisim (ex_point_curried (p := p)) c.eval } := by
  extract using ex_point_curried

/-
  The struct is replaced by a vector of 3 elements and any reference
  to its fields is replaced by accesses to the vector at the right
  index.
  The vector is then replaced by 3 distict arguments in the currying
  phase.
-/

example : (extracted_point (p := p)).1 =
  .lam fun x_0 =>
  .lam fun x_1 =>
  .lam fun x_2 =>
  .eq0 (Exp.c (x_0 + x_1)) (
  .eq0 (Exp.c (x_0 + x_2))
  .nil) := rfl

def expected : Circuit' p := fun _ =>
  .lam fun x_0 =>
  .lam fun x_1 =>
  .lam fun x_2 =>
  .eq0 (.v x_0 + .v x_1) <|
  .eq0 (.v x_0 + .v x_2) <|
  .nil

def cs : Cs' p := Clap.toCs' expected
def wg : Wg p := Clap.toWg' expected

example : wg (p:=p) =
  .input fun _ =>
  .input fun _ =>
  .input fun _ =>
  .nil
:= rfl

#guard s!"{cs (p:=Primes.babybear) ℕ}" = "λ0 λ1 λ2 eq0 (v0 + v1) eq0 (v0 + v2) nil"
#guard s!"{wg (p:=Primes.babybear)}" = "λ0 λ1 λ2 []"

#eval (wg (p:=Primes.babybear)).run [0,1,2]

def wg_synth (point : Point p) : List (ZMod p) := sorry

-- TODO use is_zero
