import Clap.Primes
import Clap.Spec

namespace Clap.Lang

export Clap.Spec.Compiler (
  accept
  eq0
  share
  isZero
  num2bits
  fpMul
  bits2numV)

variable {p : ℕ}

abbrev F p := ZMod p
abbrev FB p := F p

namespace F

instance : Inhabited (F p) where
  default := 42

def assert_range (w : ℕ) (e : F p) : Option Unit := do
  let _ <- num2bits w e ; ()

def assert_eq (a b : F p) : Option Unit := do
  eq0 (a - b)

def eq (a b : F p) : Option (FB p) :=
  isZero (a - b)

def dotProduct {w : ℕ} (a b : Vector (F p) w) : F p :=
  (a.zipWith (· * ·) b).foldl (· + ·) 0

/-- Gated assertion: asserts `constraint == 0` only when `guard == 1` -/
def guardedEq0 (guard : FB p) (constraint : F p) : Option Unit :=
  eq0 (guard * constraint)

/-- Gated equality: asserts `a == b` only when `guard == 1` -/
def guardedAssertEq (guard : FB p) (a b : F p) : Option Unit :=
  guardedEq0 guard (a - b)

end F

namespace FB

def true : FB p := 1

def false : FB p := 0

instance : Inhabited (FB p) where
  default := false

def eq (a b : FB p) : Option (FB p) :=
  F.eq a b

def assertBool (f: FB p) : Option Unit :=
  eq0 (f * (1 - f))

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

def assert (a : FB p) : Option Unit := do
  eq0 (not a)

def assert_eq (a b : FB p) : Option Unit := do
  F.assert_eq a b

end FB

namespace F

/-
requires:
- a and b ∈ [0,2^w-1]
- w+1 < p

case a < b
then a-b ∈ [-(2^w-1),-1]
then a-b+2^w ∈ [1,2^w-1]
which fits in w bits, so when converted to a (w+1)-bit number, its MSB is 0

case a ≥ b
then a-b ∈ [0,2^w-1]
then a-b+2^w ∈ [2^w,2^(w+1)-1]
which does not fit in w bits, so when converted to a (w+1)-bit number, its MSB is 1
-/
def lessThan (w : ℕ) (a b : F p) : Option (FB p) := do
  let d := a - b + 2^w
  let d ← num2bits (w + 1) d
  return FB.not d[w]!

def lessEqThan (w : ℕ) (a b : F p) : Option (FB p) :=
  lessThan w a (b + 1)

def greaterThan (w : ℕ) (a b : F p) : Option (FB p) :=
  lessThan w b a

def greaterEqThan (w : ℕ) (a b : F p) : Option (FB p) :=
  lessThan w b (a + 1)

end F

/-- LSB first, like the output of num2bits -/
abbrev FBitVec (p w : ℕ) := Vector (FB p) w

namespace FBitVec

def default (w:ℕ) : FBitVec p w := Vector.replicate w FB.false

def ofF (w:ℕ) (e:F p) : Option (FBitVec p w) :=
  num2bits w e

abbrev toF {w} (v:FBitVec p w) : F p := bits2numV v

-- if arguments are both n-bit long, result is n+1 bits
def binSum {w} (a b : FBitVec p w) : Option (FBitVec p (w+1)) :=
  let sum : F p := a.toF + b.toF
  num2bits (w + 1) sum

def assert_eq {w} (a b : FBitVec p w) : Option Unit :=
  (a.zip b).foldlM (fun () (a,b) ↦ FB.assert_eq a b) ()

def eq {w} (a b : FBitVec p w) : Option (FB p) :=
  (a.zip b).foldlM (fun acc (a,b) => do FB.and acc (←FB.eq a b)) FB.true

def lessThan {w} (a b : FBitVec p w) : Option (FB p) :=
  (a.zip b).foldlM (fun acc (aᵢ, bᵢ) ↦ do
    let eqᵢ ← FB.eq aᵢ bᵢ
    (eqᵢ &&& acc) ||| ((FB.not eqᵢ) &&& (FB.not aᵢ))
  ) FB.false

def greaterThan {w} (a b : FBitVec p w) : Option (FB p) :=
  lessThan b a

end FBitVec

abbrev F8 (p:ℕ) [Fact (Primes.fits p 8)] := FBitVec p 8

namespace F8

variable [Fact (Primes.fits p 8)]

def ofF (x:F p) : Option (F8 p) := do
  FBitVec.ofF 8 x

def ofUInt8 (u:UInt8) : Option (F8 p) :=
  num2bits 8 (u.toNat)

def zero : F8 p := FBitVec.default 8

def eq (a b : F8 p) : Option (FB p) := FBitVec.eq a b

def assert_eq (a b : F8 p) := FBitVec.assert_eq a b

end F8


abbrev F32 (p:ℕ) [Fact (Primes.fits p 32)] := FBitVec p 32

namespace F32

variable [Fact (Primes.fits p 32)]

def default : F32 p := FBitVec.default 32

instance : Inhabited (F32 p) where
  default

def ofF (x:F p) : Option (F32 p) := do
  FBitVec.ofF 32 x

def ofF8 [Fact (Primes.fits p 8)] (u8 : F8 p) : F32 p :=
  u8 ++ (Vector.replicate 24 (0:FB p))

def add (a b : F32 p) : Option (F32 p) := do
  have h : Option (FBitVec p (min 32 (32 + 1))) = Option (F32 p) := by grind
  h ▸ Vector.take (← FBitVec.binSum a b) 32

def assert_eq (a b : F32 p) := FBitVec.assert_eq a b

end F32

abbrev F64 (p:ℕ) [Fact (Primes.fits p 64)] := FBitVec p 64

namespace F64

variable [Fact (Primes.fits p 64)]

def ofF (x:F p) : Option (F64 p) :=
  FBitVec.ofF 64 x

end F64

def FByteArray (p w : ℕ) [Fact (Primes.fits p 8)] := Vector (F8 p) w

namespace FByteArray

end FByteArray

end Clap.Lang

namespace Test

abbrev p := Primes.goldilocks

open Clap.Lang

example : F.lessThan 1 (0 : F p) 1 == some 1 := by native_decide
example : F.lessThan 1 (0 : F p) 0 == some 0 := by native_decide
example : F.lessThan 2 (1 : F p) 2 == some 1 := by native_decide
example : F.lessThan 2 (2 : F p) 1 == some 0 := by native_decide
example : F.lessThan 8 (42 : F p) (2^8 - 1) == some 1 := by native_decide
example : F.lessThan 8 (2^8 - 1) (42 : F p) == some 0 := by native_decide

example : F.lessEqThan 2 (2 : F p) 2 == some 1 := by native_decide
example : F.lessEqThan 2 (1 : F p) 2 == some 1 := by native_decide
example : F.lessEqThan 2 (3 : F p) 2 == some 0 := by native_decide

example : F.greaterThan 2 (3 : F p) 2 == some 1 := by native_decide
example : F.greaterThan 2 (2 : F p) 2 == some 0 := by native_decide

example : F.greaterEqThan 2 (3 : F p) 2 == some 1 := by native_decide
example : F.greaterEqThan 2 (2 : F p) 2 == some 1 := by native_decide
example : F.greaterEqThan 2 (2 : F p) 3 == some 0 := by native_decide


def testBinSum (a b : FBitVec p 3) (expected : FBitVec p 4) : Option Unit := do
  FBitVec.assert_eq (← FBitVec.binSum a b) expected

example : (testBinSum #v[1,0,0] #v[1,0,0] #v[0,1,0,0]) = some () := by native_decide
example : (testBinSum #v[0,0,1] #v[0,0,1] #v[0,0,0,1]) = some () := by native_decide
example : (testBinSum #v[1,1,1] #v[1,0,0] #v[0,0,0,1]) = some () := by native_decide

instance : Coe UInt32 (F32 p) where
  coe n := Clap.num2bitsLsbPureV 32 n.toNat

instance (n:ℕ) : OfNat (F32 p) n where
  ofNat := Clap.num2bitsLsbPureV 32 n

example :
  letI a : UInt32 := 2^32 - 1
  (F32.add (a : F32 p) (1 : F32 p)) = ((UInt32.add a 1) : F32 p) := by native_decide

def F8.ofF! {p:ℕ} [Fact (Nat.Prime p)] [Fact (Primes.fits p 8)] : F p → F8 p := Clap.num2bitsLsbPureV 8

example : FBitVec.lessThan (p := p) (F8.ofF! 0) (F8.ofF! 1) == some 1 := by native_decide
example : FBitVec.lessThan (p := p) (F8.ofF! 1) (F8.ofF! 0) == some 0 := by native_decide
example : FBitVec.lessThan (p := p) (F8.ofF! 5) (F8.ofF! 5) == some 0 := by native_decide
example : FBitVec.lessThan (p := p) (F8.ofF! 42) (F8.ofF! 255) == some 1 := by native_decide
example : FBitVec.lessThan (p := p) (F8.ofF! 255) (F8.ofF! 42) == some 0 := by native_decide
example : FBitVec.greaterThan (p := p) (F8.ofF! 1) (F8.ofF! 0) == some 1 := by native_decide
example : FBitVec.greaterThan (p := p) (F8.ofF! 0) (F8.ofF! 1) == some 0 := by native_decide
example : FBitVec.greaterThan (p := p) (F8.ofF! 5) (F8.ofF! 5) == some 0 := by native_decide

end Test
