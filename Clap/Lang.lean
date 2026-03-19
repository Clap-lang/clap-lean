import Clap.Primes
import Clap.Spec

namespace Clap.Lang

class Core (p : ℕ) : Type _ where
  F           : Type
  [instF      : Field F]
  accept      : Unit
  eq0         : F → Option Unit
  share       : F → F
  isZero      : F → F
  num2bits    : ℕ → F → Option (List F)
  bits2num    : List F → F

  [onlyForDebugF  : ToString F  ]

attribute [reducible] Core.F Core.instF Core.accept Core.eq0 Core.share Core.isZero Core.num2bits Core.bits2num Core.onlyForDebugF
attribute [instance] Core.instF Core.onlyForDebugF

variable {p : ℕ} [Core p]

open Core

abbrev FB := F

namespace F

instance : Inhabited (F p) where
  default := 42

def assert_range (w : ℕ) (e : F p) : Option Unit := do
  let _ <- num2bits w e ; ()

def assert_eq (a b : F p) : Option Unit := do
  eq0 (a - b)

def eq (a b : F p) : FB p :=
  isZero (a - b)

def dotProduct {w : ℕ} (a b : Vector (F p) w) : F p :=
  (a.zipWith (· * ·) b).foldl (· + ·) 0

end F

namespace FB

def true : FB p := 1

def false : FB p := 0

instance : Inhabited (FB p) where
  default := false

def eq (a b : FB p) : FB p :=
  F.eq a b

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
abbrev FBitVec (p:ℕ) [Core p] := List (FB p)

namespace FBitVec

def default (l:ℕ) : FBitVec p := List.replicate l FB.false

def ofF (w:ℕ) (e:F p) : Option (FBitVec p) :=
  num2bits w e

abbrev toF (v:FBitVec p) : F p := Core.bits2num v

-- if arguments are both n-bit long, result is n+1 bits
def binSum (a b : FBitVec p) : Option (FBitVec p) :=
  let sum : F p := a.toF + b.toF
  num2bits (a.length + 1) sum

def assert_eq (a b : FBitVec p) : Option Unit :=
  match a,b with
  | [],[] => some ()
  | ha::tla,hb::tlb => do
      FB.assert_eq ha hb
      assert_eq tla tlb
  | _,_ => none

def lessThan (a b : FBitVec p) : FB p :=
  (a.zip b).foldl (fun acc (aᵢ, bᵢ) ↦
    let eqᵢ := FB.eq aᵢ bᵢ
    (eqᵢ &&& acc) ||| ((FB.not eqᵢ) &&& (FB.not aᵢ))
  ) FB.false

def greaterThan (a b : FBitVec p) : FB p :=
  lessThan b a

end FBitVec

abbrev F8 (p:ℕ) [Fact (Primes.fits p 8)] [Core p] := FBitVec p

namespace F8

variable [Fact (Primes.fits p 8)]

def ofF (x:F p) : Option (F8 p) := do
  FBitVec.ofF 8 x

def ofUInt8 (u:UInt8) : Option (F8 p) :=
  num2bits 8 (u.toNat)

def zero : F8 p := FBitVec.default 8

def eq (a b : F8 p) : FB p :=
  List.foldl (fun acc (a,b) => FB.and acc (FB.eq a b)) FB.true (a.zip b)

def assert_eq (a b : F8 p) := FBitVec.assert_eq a b

end F8


abbrev F32 (p:ℕ) [Fact (Primes.fits p 32)] [Core p] := FBitVec p

namespace F32

variable [Fact (Primes.fits p 32)]

def default : F32 p := FBitVec.default 32

instance : Inhabited (F32 p) where
  default

def ofF (x:F p) : Option (F32 p) := do
  FBitVec.ofF 32 x

def ofF8 [Fact (Primes.fits p 8)] (u8 : F8 p) : F32 p :=
  u8 ++ (List.replicate 24 (0:FB p))

def ofUInt32 (u:UInt32) : Option (F32 p) :=
  num2bits 32 (u.toNat)

def add (a b : F32 p) : Option (F32 p) := do
  List.take 32 (← FBitVec.binSum a b)

def assert_eq (a b : F32 p) := FBitVec.assert_eq a b

end F32

abbrev F64 (p:ℕ) [Fact (Primes.fits p 64)] [Core p] := FBitVec p

namespace F64

variable [Fact (Primes.fits p 64)]

def ofF (x:F p) : Option (F64 p) := do
  FBitVec.ofF 64 x

end F64

namespace ZMod

open Clap.Spec

instance onlyForDebugF {p:ℕ} : ToString (ZMod p) where
  toString f := f.val

/-
  This instance should be avaible only when proving or testing a
  circuit, never while writing it. The risk is that a circuit which
  breaks the abstraction of Core won't be compilable.
-/
scoped instance instCoreZMod {p:ℕ} [Fact (Nat.Prime p)] : Core p where
  F := ZMod p
  accept := Compiler.accept
  eq0 := Compiler.eq0
  share := Compiler.share
  isZero := Compiler.isZero
  num2bits := Compiler.num2bits
  bits2num := Compiler.bits2num
  onlyForDebugF

def F8.ofF! {p:ℕ} [Fact (Nat.Prime p)] [Fact (Primes.fits p 8)] : F p → F8 p := Clap.num2bitsLsbPure 8

end ZMod

end Clap.Lang

namespace Test

abbrev p := Primes.goldilocks

open Clap.Lang Core ZMod

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


def testBinSum (a b expected : FBitVec p) : Option Unit := do
  FBitVec.assert_eq (← FBitVec.binSum a b) expected

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

example : FBitVec.lessThan (p := p) (F8.ofF! 0) (F8.ofF! 1) == 1 := by native_decide
example : FBitVec.lessThan (p := p) (F8.ofF! 1) (F8.ofF! 0) == 0 := by native_decide
example : FBitVec.lessThan (p := p) (F8.ofF! 5) (F8.ofF! 5) == 0 := by native_decide
example : FBitVec.lessThan (p := p) (F8.ofF! 42) (F8.ofF! 255) == 1 := by native_decide
example : FBitVec.lessThan (p := p) (F8.ofF! 255) (F8.ofF! 42) == 0 := by native_decide
example : FBitVec.greaterThan (p := p) (F8.ofF! 1) (F8.ofF! 0) == 1 := by native_decide
example : FBitVec.greaterThan (p := p) (F8.ofF! 0) (F8.ofF! 1) == 0 := by native_decide
example : FBitVec.greaterThan (p := p) (F8.ofF! 5) (F8.ofF! 5) == 0 := by native_decide

end Test
