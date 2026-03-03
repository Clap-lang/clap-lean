import Clap.Lang
import Clap.Spec
import Clap.Compiler.Basic

namespace Clap

namespace Test

open Primes
open Clap Lang

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (Primes.fits p 32)]
variable [Core p]

open Core

def testAdd (x y : F p) : Option Unit := do
  let xs := F32.ofF x
  let ys := F32.ofF y
  let res := F32.add xs ys
  F32.assert_eq F32.default res
  accept p

open Clap.Lang.ZMod

--#compile testAdd using Primes.bn254

example (x y : F bn254) : testAdd x y = sorry := by
  test_reduce
  let l1 := Spec.Compiler.num2bits 32 x
  have eq1 : l1 = Spec.Compiler.num2bits 32 x := by aesop
  symm at eq1
  have : List.foldr (fun b acc => b + 2 * acc) 0 (Spec.Compiler.num2bits 32 x) = List.foldr (fun b acc => b + 2 * acc) 0 l1 := by grind
  have : List.take 32
          (Spec.Compiler.num2bits ((Spec.Compiler.num2bits 32 x).length + 1)
            (List.foldr (fun b acc => b + 2 * acc) 0 (Spec.Compiler.num2bits 32 x) +
             List.foldr (fun b acc => b + 2 * acc) 0 (Spec.Compiler.num2bits 32 y))) = List.take 32
          (Spec.Compiler.num2bits (l1.length + 1)
            (List.foldr (fun b acc => b + 2 * acc) 0 l1 +
             List.foldr (fun b acc => b + 2 * acc) 0 (Spec.Compiler.num2bits 32 y))) := by grind
  let l2 := Spec.Compiler.num2bits 32 y
  have eq2 : l2 = Spec.Compiler.num2bits 32 y := by aesop
  have : List.take 32
          (Spec.Compiler.num2bits ((Spec.Compiler.num2bits 32 x).length + 1)
            (List.foldr (fun b acc => b + 2 * acc) 0 (Spec.Compiler.num2bits 32 x) +
             List.foldr (fun b acc => b + 2 * acc) 0 (Spec.Compiler.num2bits 32 y))) = List.take 32
          (Spec.Compiler.num2bits (l1.length + 1)
            (List.foldr (fun b acc => b + 2 * acc) 0 l1 +
             List.foldr (fun b acc => b + 2 * acc) 0 l2)) := by grind
  have : FBitVec.assert_eq [(0:FB bn254), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
          (List.take 32
            (Spec.Compiler.num2bits ((Spec.Compiler.num2bits 32 x).length + 1)
              (List.foldr (fun b acc => b + 2 * acc) 0 (Spec.Compiler.num2bits 32 x) +
                List.foldr (fun b acc => b + 2 * acc) 0 (Spec.Compiler.num2bits 32 y)))) =
  FBitVec.assert_eq [(0:FB bn254), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (
  List.take 32 (Spec.Compiler.num2bits (l1.length + 1) (List.foldr (fun b acc => b + 2 * acc) 0 l1 + List.foldr (fun b acc => b + 2 * acc) 0 l2))) := by grind

--  generalize eq : Spec.Compiler.num2bits 32 x = l1
