--import Clap.Circuit
import Clap.Primes
import Clap.Compilation
import Clap.SpecUint
import Clap.Compiler.Basic

open Clap.Lang

variable {p : ℕ} [Fact (Nat.Prime p)] [Core p]

open Core

/-
  This example showcases a circuit that takes a vector of field
  elements (the tye `ZMod p`) of length 3 and simply checks that all
  elements are zero using a very natural for loop.
-/

def ex_vec (xs : Vector (F p) 3) : Option Unit := do
  for x in xs do
    eq0 x
  accept (p:=p)

/-
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
example : (extract_vec (p := p)).1 =
  .lam fun x_0 =>
  .lam fun x_1 =>
  .lam fun x_2 =>
  .eq0 x_0   (
  .eq0 x_1 (
  .eq0 x_2
  .nil)) := rfl
-/

/-
  This example showcases the use of a structure (equivalent to struct
  in Rust).
  Notice that in the body of the circuit `ex_point` we can freely
  refer to any field of the struct.
-/

structure Point3 where
  x : F p
  y : F p
  z : F p

def ex_point (point : Point3 (p:=p)) : Option Unit := do
  eq0 (point.x + point.y)
  eq0 (point.x + point.z)
  accept (p:=p)

/-
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
-/
