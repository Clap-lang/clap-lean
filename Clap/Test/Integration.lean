import Clap.Compiler.Basic
import Clap.Compilation
import Clap.R1CS
import Clap.Lang

namespace Circuit

open Clap Lang

open Core

def test {p:ℕ} [Core p] (x y z : Core.F p) : Option Unit := do
  eq0 (x * (y - z) + z)
  accept p

open ZMod

abbrev test' (x y z : ZMod Primes.babybear) : Option Unit := do
  Spec.Compiler.eq0 (x * (y - z) + z)
  Spec.Compiler.accept


#compile Circuit.test' using Primes.babybear

#print Circuit.test'_ser_wg
#print Circuit.test'_ser

def wg := toWg' Circuit.test'_ser
#print wg
def wg' := Circuit.test'_ser_wg wg
#print wg'

def cs := Clap.toCs' (Circuit.test'_ser)
def r1cs := Clap.toR1CS (Circuit.test'_ser)

#check cs
#eval r1cs

-- open Clap

-- example : r1cs (p:=p) = .eq0 ((Clap.Exp.v 1 * (.v 2 - .v 3)) + .v 3) .nil := by rfl

end Circuit
