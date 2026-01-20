import Clap.Primes
import Clap.Spec

namespace Clap.Lang

class Core (p : ℕ) [Fact (Nat.Prime p)] : Type _ where
  F           : Type
  [instF      : Field F]
  [instFChar  : CharP F p]
  FB          : Type
  [instFB     : Field FB]
  [instFBChar : CharP FB p]
  convert     : FB → F
  const       : ZMod p → F
  accept      : Unit
  eq0         : F → Option Unit
  isZero      : F → Option FB
  num2bits    : ℕ → F → Option (List FB)
  [onlyForDebugF  : ToString F  ]
  [onlyForDebugFB : ToString FB ]

attribute [instance] Core.instF Core.instFChar Core.instFB Core.instFBChar

variable {p : ℕ} [Fact (Nat.Prime p)] [Core p]

open Core

namespace F

def assert_range (w : ℕ) (e : F p) : Option Unit := do
  let _ <- num2bits w e ; ()

def assert_eq (a b : F p) : Option Unit := do
  eq0 (a - b)

def eq (a b : F p) : Option (FB p) := do
  isZero (a - b)

end F

namespace FB

/-
  For now we assume that true is anything ≠ 0, double check this and
  make sure that any use of covert does not rely on true=1
-/

def eq (a b : FB p) : Option (FB p) := do
  F.eq (convert a) (convert b)

-- 0 0 0
-- 0 t 0
-- t 0 0
-- t t t*t
def and (a b : FB p) : FB p := a * b

instance : HAnd (FB p) (FB p) (FB p) where
  hAnd := and

-- 0 0 0
-- 0 t t
-- t 0 t
-- t t 2t
def or (a b : FB p) : FB p := a + b

instance : HOr (FB p) (FB p) (FB p) where
  hOr := or

-- 0 1
-- t 0
def not (a : FB p) : Option (FB p) := isZero (convert a)

-- 0 0 0
-- 0 t -t
-- t 0 t
-- t t 0
def xor (a b : FB p) : (FB p) := a - b

instance : HXor (FB p) (FB p) (FB p) where
  hXor := xor

-- a → b or ¬a ∨ b
-- 0 0 1
-- 0 1 1
-- 1 0 0
-- 1 1 1

def lessThanEq (a b : FB p) : Option (FB p) := do
  let na <- not a
  return or na b

def assert (a : FB p) : Option Unit := do
  let b <- isZero (convert a)
  eq0 (convert b)

def assert_eq (a b : FB p) : Option Unit := do
  F.assert_eq (convert a) (convert b)

end FB

def F.lessThanEq (w : ℕ) (a b : F p) : Option (FB p) := do
  let a <- num2bits w a
  let b <- num2bits w b
  -- we want to check from the MSB
  let ab := (List.reverse (a.zip b))
  List.foldl (fun acc (a,b) => do
    let l : FB p <- FB.lessThanEq a b
    (<-acc) &&& l) (some 1) ab

/-- LSB first, like the output of num2bits -/
abbrev FBitVec := List (FB p)

def FBitVec.toF (v : FBitVec (p:=p)) : F p :=
  aux (1:ZMod p) (const 0) v
where
  aux pow acc v :=
    match v with
    | [] => acc
    | b::rest =>
        let acc := acc + ((convert b) * (const pow))
        aux (pow*2) acc rest

-- if arguments are both n-bit long, result is n+1 bits
def FBitVec.binSum (a b : FBitVec (p:=p)) : Option (FBitVec (p:=p)) :=
  let sum : F p := a.toF + b.toF
  num2bits (List.length a + 1) sum

def FBitVec.assert_eq (a b : FBitVec (p:=p)) : Option Unit :=
  for (a,b) in a.zip b do
    FB.assert_eq a b

namespace Test

abbrev F' := ZMod Primes.babybear

open Clap.Spec

instance instCoreZMod : Core Primes.babybear where
  F := F'
  FB := F'
  convert := id
  const := id
  accept := Compiler.accept
  eq0 := Compiler.eq0
  isZero := Compiler.is_zero
  num2bits := Compiler.num2bits

attribute [instance] instCoreZMod

def testLTE (w:ℕ) (a b : F') : Option Unit := do
  FB.assert (p:=Primes.babybear) (<-F.lessThanEq w a b)

#guard (testLTE 3 4 5) = some ()
#guard (testLTE 3 5 5) = some ()
#guard (testLTE 3 5 4) = none
#guard (testLTE 3 2 1) = none


def testBinSum (a b expected : FBitVec (p:=Primes.babybear)) : Option Unit := do
  FBitVec.assert_eq (<-FBitVec.binSum a b) expected

#guard (testBinSum [1,0,0] [1,0,0] [0,1,0,0]) = some ()
#guard (testBinSum [0,0,1] [0,0,1] [0,0,0,1]) = some ()
#guard (testBinSum [1,1,1] [1,0,0] [0,0,0,1]) = some ()

end Test

end Clap.Lang
