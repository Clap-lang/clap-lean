import Clap.Spec
import Clap.Lang
import Clap.Spec.F
import Clap.Spec.FB

namespace Clap

open Clap.Lang

variable {p : ℕ} [Core p]

open Core

-- def FB.lessThanEq (a b : FB p) : Option (FB p) := do
--   let na ← not a
--   return or na b

-- def F.lessThanEq (w : ℕ) (a b : F p) : Option (FB p) := do
--   let a ← num2bits w a
--   let b ← num2bits w b
--   -- we want to check from the MSB
--   let ab := (List.reverse (a.zip b))
--   List.foldl (fun acc (a,b) => do
--     let l : FB p ← FB.lessThanEq a b
--     (<-acc) &&& l) (some 1) ab

def F.lessThan (w : ℕ) (a b : F p) : Option (FB p) := do
  let c ← num2bits (w + 1) (a + const ((1 <<< w) : ZMod p) - b)
  return 1 - c[w]!

def F.lessThanEq (w : ℕ) (a b : F p) : Option (FB p) :=
  F.lessThan w a (b + 1)

def F.greaterThan (w : ℕ) (a b : F p) : Option (FB p) :=
  F.lessThan w b a

def F.greaterThanEq (w : ℕ) (a b : F p) : Option (FB p) :=
  F.lessThan w b (a + 1)

end Clap

notation l " <[" w "] " r  => Clap.F.lessThan w l r
notation l " <=[" w "] " r => Clap.F.lessThanEq w l r
notation l " ≤[" w "] " r  => Clap.F.lessThanEq w l r

notation l " >[" w "] " r  => Clap.F.greaterThan w l r
notation l " >=[" w "] " r => Clap.F.greaterThanEq w l r
notation l " ≥[" w "] " r  => Clap.F.greaterThanEq w l r

namespace Clap.Spec.Comparators.Test

open Clap.Lang

abbrev p := Primes.goldilocks
abbrev F' := ZMod p

open Clap.Spec

instance instCoreZMod : Core p where
  F := F'
  FB := F'
  convert := id
  const := id
  accept := Compiler.accept
  eq0 := Compiler.eq0
  share := Compiler.share
  shareB := Compiler.share
  isZero := Compiler.is_zero
  num2bits := Compiler.num2bits
  bits2num := Compiler.bits2num

attribute [instance] instCoreZMod

def testLTE (w : ℕ) (a b : F') : Option Unit := do
  assert (p := p) (← a ≤[w] b)

def testLT (w : ℕ) (a b : F') : Option Unit := do
  assert (p := p) (← a <[w] b)

def testGTE (w : ℕ) (a b : F') : Option Unit := do
  assert (p := p) (← a ≥[w] b)

def testGT (w : ℕ) (a b : F') : Option Unit := do
  assert (p := p) (← a >[w] b)

#guard (testLTE 3 4 5) = some ()
#guard (testLTE 3 5 5) = some ()
#guard (testLTE 3 5 4) = none
#guard (testLTE 3 2 1) = none

#guard (testLT 3 4 5) = some ()
#guard (testLT 3 5 5) = none
#guard (testLT 3 5 4) = none
#guard (testLT 3 2 1) = none

#guard (testGTE 3 5 4) = some ()
#guard (testGTE 3 5 5) = some ()
#guard (testGTE 3 4 5) = none
#guard (testGTE 3 1 2) = none

#guard (testGT 3 5 4) = some ()
#guard (testGT 3 5 5) = none
#guard (testGT 3 4 5) = none
#guard (testGT 3 1 2) = none

end Clap.Spec.Comparators.Test
