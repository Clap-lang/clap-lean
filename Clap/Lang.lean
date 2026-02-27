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
  num2bits    : ℕ → F → Option (List FB)
  bits2num    : List FB → F

  [onlyForDebugF  : ToString F  ]
  [onlyForDebugFB : ToString FB ]

attribute [instance] Core.instF Core.instFChar Core.instFB Core.instFBChar Core.onlyForDebugF Core.onlyForDebugFB

variable {p : ℕ} [Core p]

open Core

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

def assert (a : FB p) : Option Unit := do
  eq0 (convert (not a))

def assert_eq (a b : FB p) : Option Unit := do
  F.assert_eq (convert a) (convert b)

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
  let d := a - b + const (2^w)
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

def ofF (w:ℕ) (e:F p) : FBitVec p :=
  Option.getD (num2bits w e) (default w)

def ofF! (w:ℕ) (e:F p) : Option (FBitVec p) :=
  num2bits w e

abbrev toF (v:FBitVec p) : F p := Core.bits2num v

-- if arguments are both n-bit long, result is n+1 bits
def binSum (a b : FBitVec p) : FBitVec p := Option.getD (do
  let sum : F p := a.toF + b.toF
  num2bits (a.length + 1) sum)
  (FBitVec.default (a.length + 1))

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

def ofF (x:F p) : (F8 p) :=
  FBitVec.ofF 8 x

def ofF! (x:F p) : Option (F8 p) :=
  FBitVec.ofF! 8 x

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

def ofF (x:F p) : (F32 p) :=
  FBitVec.ofF 32 x

def ofF8 [Fact (Primes.fits p 8)] (u8 : F8 p) : F32 p :=
  u8 ++ (List.replicate 24 (0:FB p))

def ofUInt32 (u:UInt32) : Option (F32 p) :=
  num2bits 32 (u.toNat)

def add (a b : F32 p) : (F32 p) :=
  List.take 32 (FBitVec.binSum a b)

instance : HAdd (F32 p) (F32 p) (F32 p) where
  hAdd := add

def assert_eq (a b : F32 p) := FBitVec.assert_eq a b

end F32

abbrev F64 (p:ℕ) [Fact (Primes.fits p 64)] [Core p] := FBitVec p

namespace F64

variable [Fact (Primes.fits p 64)]

def ofF! (x:F p) : Option (F64 p) :=
  FBitVec.ofF! 64 x

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

example : F.lessThan (p := p) 1 0 1 == some 1 := by native_decide
example : F.lessThan (p := p) 1 0 0 == some 0 := by native_decide
example : F.lessThan (p := p) 2 1 2 == some 1 := by native_decide
example : F.lessThan (p := p) 2 2 1 == some 0 := by native_decide
example : F.lessThan (p := p) 8 42 (2^8 - 1) == some 1 := by native_decide
example : F.lessThan (p := p) 8 (2^8 - 1) 42 == some 0 := by native_decide

example : F.lessEqThan (p := p) 2 2 2 == some 1 := by native_decide
example : F.lessEqThan (p := p) 2 1 2 == some 1 := by native_decide
example : F.lessEqThan (p := p) 2 3 2 == some 0 := by native_decide

example : F.greaterThan (p := p) 2 3 2 == some 1 := by native_decide
example : F.greaterThan (p := p) 2 2 2 == some 0 := by native_decide

example : F.greaterEqThan (p := p) 2 3 2 == some 1 := by native_decide
example : F.greaterEqThan (p := p) 2 2 2 == some 1 := by native_decide
example : F.greaterEqThan (p := p) 2 2 3 == some 0 := by native_decide


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
