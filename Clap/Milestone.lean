import Clap.Lang
import Clap.Compiler.Basic
import Clap.Cfold
import Clap.Compilation
import Clap.Quadratic
import Clap.Sha2.Circuit

open Primes
open Clap
open Lang

/-
  We assume the existance of a p, prime, that fits a number up 32 bits,
-/
variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (Primes.fits p 32)]

/-
  We assume for that p, we have an instance of our Core subset
-/
variable [Core p]

open Core

structure MyCouple (p:ℕ) [Core p] where
  x : F (p:=p)
  y : F (p:=p)

def test (xy : MyCouple p) : Option Unit := do
  eq0 xy.x
  eq0 xy.y
  F.assert_eq xy.x xy.y
  accept p

-- def test {p:ℕ} [Core p] [Fact (Primes.fits p 32)]
--   (x y z : Vector (FB p) 32) : Option Unit := do
--   let x : F32 p := x.toList
--   let y : F32 p := y.toList
--   let z : F32 p := z.toList
--   F32.assert_eq (Clap.Sha2.Circuit.ch x y z) F32.default
--   -- accept p

-- def test (x y : F p) : Option Unit := do
--   let e := 5 * x - 3+1
--   F.assert_eq e y
--   accept p

-- def test2 (x y : F p) : Option Unit := do
--   let xs := F32.ofF x
--   let ys := F32.ofF y
--   let res := F32.add xs ys
--   F32.assert_eq F32.default res
--   accept p

-- def test3 (x : F p) : Option Unit := do
--   let xs := isZero x
--   FB.assert_eq xs FB.true
--   accept p

open Clap.Lang.ZMod

#compile test using Primes.bn254

/- The compiler gives us a circuit that we can compile further. -/
def test_circ : Circuit' bn254 := test_ser

/- But also a wg_wrap which we can use to wrap our witness generator. -/
def test_wg_wrap : Wg bn254 -> MyCouple bn254 -> Array (ZMod bn254) := test_ser_wg

/- We can optimize the circuit. -/
def test_circ_opt := Clap.cfold' test_circ

/- Compile the circuit to a cs. -/
def test_cs : Clap.Cs' bn254 := Clap.toCs' test_circ

/- Compile the circuit to a wg. -/
def test_wg_raw : Clap.Wg bn254 := Clap.toWg' test_circ
/- And use the wrapper to get nicer arguments. -/
def test_wg : MyCouple bn254 → Array (ZMod bn254) := test_wg_wrap (Clap.toWg' test_circ)

/- Serialize the cs to r1cs -/
def r1cs : R1CSv1 := quadraticToR1CS (Clap.toLevels test_cs)

def main (args : List String) : IO UInt32 := do
  IO.println s!"snarkjs ri {args[0]!}"
  serializeR1CS args[0]! r1cs
  return 0
