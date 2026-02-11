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
  bits2num    : List FB → F

  [onlyForDebugF  : ToString F  ]
  [onlyForDebugFB : ToString FB ]

attribute [instance] Core.instF Core.instFChar Core.instFB Core.instFBChar Core.onlyForDebugF Core.onlyForDebugFB

variable {p : ℕ} [Fact (Nat.Prime p)] [Core p]

open Core

namespace F

instance : Inhabited (F p) where
  default := 42

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

def true : FB p := 1

def false : FB p := 0

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
abbrev FBitVec (p:ℕ) [Fact (Nat.Prime p)] [Core p] := List (FB p)

namespace FBitVec

def default (l:ℕ) : FBitVec p := List.replicate l 0

def ofF (w:ℕ) (e:F p) : FBitVec p :=
  Option.getD (num2bits w e) (default w)

abbrev toF (v:FBitVec p) : F p := Core.bits2num v

-- if arguments are both n-bit long, result is n+1 bits
def binSum (a b : FBitVec p) : FBitVec p := Option.getD (do
  let sum : F p := a.toF + b.toF
  num2bits (a.length + 1) sum)
  (FBitVec.default (a.length + 1))

def assert_eq (a b : FBitVec p) : Option Unit :=
  for (a,b) in a.zip b do
    FB.assert_eq a b

end FBitVec

abbrev F8 (p:ℕ) [Fact (Primes.fits p 8)] [Fact (Nat.Prime p)] [Core p] := FBitVec p

namespace F8

variable [Fact (Primes.fits p 8)]

def ofF (x:F p) : (F8 p) :=
  FBitVec.ofF 8 x

def ofUInt8 (u:UInt8) : Option (F8 p) :=
  num2bits 8 (u.toNat)

def zero : F8 p := FBitVec.default 8

def eq (a b : F8 p) : Option (FB p) :=
  List.foldlM (fun acc (a,b) => (FB.and acc) <$> (FB.eq a b)) FB.true (a.zip b)

def assert_eq (a b : F8 p) := FBitVec.assert_eq a b

end F8


abbrev F32 (p:ℕ) [Fact (Primes.fits p 32)] [Fact (Nat.Prime p)] [Core p] := FBitVec p

namespace F32

variable [Fact (Primes.fits p 8)] [Fact (Primes.fits p 32)]

def default : F32 p := FBitVec.default 32

instance : Inhabited (F32 p) where
  default

def ofF (x:F p) : (F32 p) :=
  FBitVec.ofF 32 x

def ofF8 (u8 : F8 p) : F32 p :=
  u8 ++ (List.replicate 24 (0:FB p))

def ofUInt32 (u:UInt32) : Option (F32 p) :=
  num2bits 32 (u.toNat)

def add (a b : F32 p) : (F32 p) :=
  List.take 32 (FBitVec.binSum a b)

instance : HAdd (F32 p) (F32 p) (F32 p) where
  hAdd := add

def assert_eq (a b : F32 p) := FBitVec.assert_eq a b

end F32

end Clap.Lang


namespace Test

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
  isZero := Compiler.is_zero
  num2bits := Compiler.num2bits
  bits2num := Compiler.bits2num

attribute [instance] instCoreZMod

def testLTE (w:ℕ) (a b : F') : Option Unit := do
  FB.assert (p:=p) (<-F.lessThanEq w a b)

#guard (testLTE 3 4 5) = some ()
#guard (testLTE 3 5 5) = some ()
#guard (testLTE 3 5 4) = none
#guard (testLTE 3 2 1) = none


def testBinSum (a b expected : FBitVec p) : Option Unit := do
  FBitVec.assert_eq (FBitVec.binSum a b) expected

#guard (testBinSum [1,0,0] [1,0,0] [0,1,0,0]) = some ()
#guard (testBinSum [0,0,1] [0,0,1] [0,0,0,1]) = some ()
#guard (testBinSum [1,1,1] [1,0,0] [0,0,0,1]) = some ()

end Test
