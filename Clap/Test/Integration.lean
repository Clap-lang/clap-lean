import Clap.Compiler.Basic
import Clap.Compilation
import Clap.R1CS

namespace Circuit

open Clap.Spec.Compiler

variable {p:ℕ} [Fact (Nat.Prime p)]

open Core

def test (x y z : ZMod p) : Option Unit := do
  eq0 (x * (y - z) + z)
  accept

#compile Circuit.test using p

def cs := Clap.toCs' (Circuit.test_ser p)
def r1cs := Clap.toR1CS (Circuit.test_ser p)

open Clap

example : r1cs (p:=p) = .eq0 ((Clap.Exp.v 1 * (.v 2 - .v 3)) + .v 3) .nil := by rfl

end Circuit
