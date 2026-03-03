import Clap.Primes
import Clap.Spec

namespace Clap.Lang

class Core (p : ℕ) : Type _ where
  F           : Type
  [instF      : Field F]
  [instFChar  : CharP F p]
  FB          : Type
  [instFB     : Field FB]
  [instFBChar : CharP FB p]
  convert     : FB → F -- true = 1, false = 0
  const       : ZMod p → F
  accept      : Unit
  eq0         : F → Option Unit
  share       : F → F
  shareB      : FB → FB
  isZero      : F → FB
  assertRange : ℕ → F → Option Unit
  num2bits    : ℕ → F → List FB
  bits2num    : List FB → F

  [onlyForDebugF  : ToString F  ]
  [onlyForDebugFB : ToString FB ]

attribute [instance] Core.instF Core.instFChar Core.instFB Core.instFBChar Core.onlyForDebugF Core.onlyForDebugFB

variable {p : ℕ} [Core p]

open Core

namespace F

instance : Inhabited (F p) where
  default := 42

def assert_eq (a b : F p) : Option Unit := do
  eq0 (a - b)

def eq (a b : F p) : Option (FB p) := do
  isZero (a - b)

end F

namespace FB

def true : FB p := 1

def false : FB p := 0

def eq (a b : FB p) : Option (FB p) := do
  F.eq (convert a) (convert b)

def and (a b : FB p) : FB p := a * b

instance : HAnd (FB p) (FB p) (FB p) where
  hAnd := and

def or (a b : FB p) : FB p := a + b - a * b

instance : HOr (FB p) (FB p) (FB p) where
  hOr := or

def not (a : FB p) : FB p := 1 - a

def xor (a b : FB p) : FB p := a + b - 2 * a * b

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
  eq0 (convert (not a))

def assert_eq (a b : FB p) : Option Unit := do
  F.assert_eq (convert a) (convert b)

end FB

def F.lessThanEq (w : ℕ) (a b : F p) : Option (FB p) := do
  let a := num2bits w a
  let b := num2bits w b
  -- we want to check from the MSB
  let ab := (List.reverse (a.zip b))
  List.foldl (fun acc (a,b) => do
    let l : FB p <- FB.lessThanEq a b
    (<-acc) &&& l) (some 1) ab

/-- LSB first, like the output of num2bits -/
abbrev FBitVec (p:ℕ) [Core p] := List (FB p)

namespace FBitVec

def default (l:ℕ) : FBitVec p := List.replicate l FB.false

def ofF! (w:ℕ) (e:F p) : FBitVec p :=
  num2bits w e

abbrev toF (v:FBitVec p) : F p := Core.bits2num v

-- if arguments are both n-bit long, result is n+1 bits
def binSum (a b : FBitVec p) : FBitVec p :=
  let sum : F p := a.toF + b.toF
  num2bits (a.length + 1) sum

def assert_eq (a b : FBitVec p) : Option Unit :=
  match a,b with
  | [],[] => some ()
  | ha::tla,hb::tlb => do
      FB.assert_eq ha hb
      assert_eq tla tlb
  | _,_ => none

end FBitVec

abbrev F8 (p:ℕ) [Fact (Primes.fits p 8)] [Core p] := FBitVec p

namespace F8

variable [Fact (Primes.fits p 8)]

def assertRange (x:F p) : Option Unit :=
  Core.assertRange 8 x

def ofF! (x:F p) : F8 p := do
  FBitVec.ofF! 8 x

def ofF (x:F p) : Option (F8 p) := do
  assertRange x
  ofF! x

def ofUInt8 (u:UInt8) : Option (F8 p) := do
  assertRange (u.toNat:F p)
  some (num2bits 8 u.toNat)

def zero : F8 p := FBitVec.default 8

def eq (a b : F8 p) : Option (FB p) :=
  List.foldlM (fun acc (a,b) => (FB.and acc) <$> (FB.eq a b)) FB.true (a.zip b)

def assert_eq (a b : F8 p) := FBitVec.assert_eq a b

end F8


abbrev F32 (p:ℕ) [Fact (Primes.fits p 32)] [Core p] := FBitVec p

namespace F32

variable [Fact (Primes.fits p 8)] [Fact (Primes.fits p 32)]

def default : F32 p := FBitVec.default 32

instance : Inhabited (F32 p) where
  default

def assertRange (x:F p) : Option Unit :=
  Core.assertRange 32 x

def ofF! (x:F p) : F32 p := do
  FBitVec.ofF! 32 x

def ofF (x:F p) : Option (F8 p) := do
  assertRange x
  ofF! x

def ofF8 (u8 : F8 p) : F32 p :=
  u8 ++ (List.replicate 24 (0:FB p))

def ofUInt32 (u:UInt32) : Option (F32 p) := do
  assertRange (u.toNat:F p)
  some (num2bits 32 u.toNat)

def add (a b : F32 p) : (F32 p) :=
  List.take 32 (FBitVec.binSum a b)

instance : HAdd (F32 p) (F32 p) (F32 p) where
  hAdd := add

def assert_eq (a b : F32 p) := FBitVec.assert_eq a b

end F32

abbrev F64 (p:ℕ) [Fact (Primes.fits p 64)] [Core p] := FBitVec p

namespace F64

variable [Fact (Primes.fits p 64)]

def assertRange (x:F p) : Option Unit :=
  Core.assertRange 64 x

def ofF! (x:F p) : F64 p := do
  FBitVec.ofF! 64 x

def ofF (x:F p) : Option (F64 p) := do
  assertRange x
  ofF! x

end F64

namespace ZMod

open Clap.Spec

instance onlyForDebugF {p:ℕ} : ToString (ZMod p) where
  toString f := natToHex f.val

/-
  This instance should be avaible only when proving or testing a
  circuit, never while writing it. The risk is that a circuit which
  breaks the abstraction of Core won't be compilable.
-/
scoped instance instCoreZMod (p:ℕ) [Fact (Nat.Prime p)] : Core p where
  F := ZMod p
  FB := ZMod p
  convert := id
  const := id
  accept := Compiler.accept
  eq0 := Compiler.eq0
  share := Compiler.share
  shareB := Compiler.share
  isZero := Compiler.is_zero
  assertRange := Compiler.assertRange
  num2bits := Compiler.num2bits
  bits2num := Compiler.bits2num
  onlyForDebugF
  onlyForDebugFB := onlyForDebugF


/-
TODO it should be possible to replace the extended definition below with this definition but there is an error
class Extended (p:ℕ) [Fact (Nat.Prime p)] : Type _ extends Core p, DecidableEq (Core.F p)
-/

class extended (p:ℕ) [Fact (Nat.Prime p)] [Core p] : Type _ where
  ins : Core p
  [i₀ : DecidableEq (Core.F p)]
  [i₁ : {n:ℕ} → OfNat (Core.F p) n]
  [i₂ : DecidableEq (Core.FB p)]

attribute [instance] extended.i₀ extended.i₁ extended.i₂

scoped instance bla (p:ℕ) [Fact (Nat.Prime p)] : extended p where
  ins := instCoreZMod p
  i₀ := inferInstanceAs (DecidableEq (ZMod p))
  i₁ := inferInstanceAs ({n:ℕ} → OfNat (ZMod p) n)
  i₂ := inferInstanceAs (DecidableEq (ZMod p))

end ZMod

end Clap.Lang


namespace Test

abbrev p := Primes.goldilocks

open Clap.Lang Core ZMod

def testLTE (w:ℕ) (a b : F p) : Option Unit := do
  FB.assert (p:=p) (<-F.lessThanEq w a b)

example : (testLTE 3 4 5) = some () := by native_decide
example : (testLTE 3 5 5) = some () := by native_decide
example : (testLTE 3 5 4) = none := by native_decide
example : (testLTE 3 2 1) = none := by native_decide


def testBinSum (a b expected : FBitVec p) : Option Unit := do
  FBitVec.assert_eq (FBitVec.binSum a b) expected

example : (testBinSum [1,0,0] [1,0,0] [0,1,0,0]) = some () := by native_decide
example : (testBinSum [0,0,1] [0,0,1] [0,0,0,1]) = some () := by native_decide
example : (testBinSum [1,1,1] [1,0,0] [0,0,0,1]) = some () := by native_decide

instance : Coe UInt32 (F32 p) where
  coe n := Clap.num2bitsLsbPure 32 n.toNat

instance (n:ℕ) : OfNat (F32 p) n where
  ofNat := Clap.num2bitsLsbPure 32 n

example :
  letI a : UInt32 := 2^32 - 1
  (F32.add (a : F32 p) (1 : F32 p)) = ((UInt32.add a 1) : F32 p) := by native_decide

end Test
