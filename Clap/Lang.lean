import Clap.Primes
import Clap.Spec

namespace Clap.Lang

variable {p : ℕ}

export Clap.Spec.Compiler (accept eq0 share isZero num2bits bits2num)

open Clap.Spec.Compiler

abbrev F p := ZMod p

namespace F

instance : Inhabited (F p) where
  default := 42

def assert_range (w : ℕ) (e : F p) : Option Unit := do
  let _ <- num2bits w e ; ()

-- def assert_eq (a b : F p) : Option Unit := do
--   eq0 (a - b)

def eq (a b : F p) : F p :=
  isZero (a - b)

def dotProduct {w : ℕ} (a b : Vector (F p) w) : F p :=
  (a.zipWith (· * ·) b).foldl (· + ·) 0

end F

namespace F.FB

def valid (a: F p) : Prop :=
  a = 0 ∨ a = 1

-- returns true also for f non boolean
def F.toBool (f:F p) : Bool :=
  if f.val = 0 then false else true

abbrev true : F p := 1

abbrev false : F p := 0

instance : Inhabited (F p) where
  default := false

def eq (a b : F p) : F p :=
  F.eq a b

def and (a b : F p) : F p := a * b

instance : HAnd (F p) (F p) (F p) where
  hAnd := and

def F.ofBool (b:Bool) : F p :=
  if b then true else false

lemma and_spec (a b : F p)
  (ha : FB.valid a)
  (hb : FB.valid b) :
  letI o := F.ofBool (F.toBool a && F.toBool b)
  (FB.and a b = o) ∧ (FB.valid o) := by
  aesop (add simp [F.ofBool,F.toBool,valid,and])

lemma and_spec' (a b : F p)
  (ha : FB.valid a)
  (hb : FB.valid b) :
  letI o := FB.and a b
  ((F.toBool a && F.toBool b) = F.toBool o) ∧ (FB.valid o)
  := by
  aesop (add simp [F.toBool,FB.valid,FB.and])

def or (a b : F p) : F p := a + b - a * b

lemma or_spec (a b : F p)
  (ha : FB.valid a)
  (hb : FB.valid b) :
  letI o := F.ofBool (F.toBool a || F.toBool b)
  (FB.or a b = o) ∧ (FB.valid o) := by
  aesop (add simp [F.ofBool,F.toBool,FB.valid,or])

instance : HOr (F p) (F p) (F p) where
  hOr := or

def not (a : F p) : F p := 1 - a

def xor (a b : F p) : F p := a + b - 2 * a * b

instance : HXor (F p) (F p) (F p) where
  hXor := xor

-- def assert (a : F p) : Option Unit := do
--   eq0 (not a)

-- def assert_eq (a b : F p) : Option Unit := do
--   F.assert_eq a b

end F.FB

def FB (p:ℕ) : Type := { f : F p // F.FB.valid f }

namespace FB
attribute [local aesop safe cases] FB

attribute [local aesop simp] sub_eq_zero eq0 F.FB.F.ofBool F.FB.F.toBool F.FB.valid

-- returns true also for f non boolean
def toBool (f:FB p) : Bool :=
  if f.val = 0 then false else true

def true : FB p := ⟨1, by aesop⟩
def false : FB p := ⟨0, by aesop⟩

def ofBool (b:Bool) : FB p :=
  if b then true else false

def ofBool_toBool (a : FB p) : (ofBool $ toBool a) = a := sorry
def toBool_ofBool (a : Bool) : (toBool $ ofBool (p:=p) a) = a := sorry

attribute [local aesop simp] toBool ofBool

def and (a b : FB p) : FB p :=
  ⟨a.val * b.val, by aesop⟩

instance : AndOp (FB p) where and
instance : HAnd (FB p) (FB p) (FB p) where hAnd := and

-- lemma assertFB_valid (a:F p) :
--   assertFB a = some () ↔ F.FB.valid a := sorry

variable [Fact (Nat.Prime p)]

lemma bla (a:F p) : a * (1-a) = 0 ↔ F.FB.valid a := by
  aesop (add simp [F.FB.valid,mul_eq_zero,sub_eq_zero])

def ofF (a : F p) : Option (FB p) := do
  let h ← eq0 (a * (1-a))
  pure ⟨a, by
    rw [bla] at h
    apply PLift.down h⟩

def and_spec (a b : FB p) :
  and a b = (ofBool (toBool a && toBool b)) := by
  have ha := a.prop
  have hb := b.prop
  aesop (add simp [and])

def and_spec' (a b : FB p) :
  toBool (and a b) = (toBool a && toBool b) := by
  have ha := a.prop
  have hb := b.prop
  aesop (add simp [and])

def or (a b : FB p) : FB p :=
  ⟨a.val + b.val - a.val * b.val, by aesop⟩

instance : OrOp (FB p) where or
instance : HOr (FB p) (FB p) (FB p) where hOr := or

def or_spec (a b : FB p) :
  or a b = (ofBool (toBool a || toBool b)) := by
  have ha := a.prop
  have hb := b.prop
  aesop (add simp [or])

def not (a : FB p) : FB p :=
  ⟨1 - a.val, by aesop⟩

def not_spec (a : FB p) :
  not a = ofBool (Bool.not (toBool a)) := by
  aesop (add simp [not,F.FB.valid])
  unfold F.FB.valid at *
  aesop

end FB

variable [Fact (Nat.Prime p)]

-- Aesop does not go through &&& ||| syntax
-- def test_spec (a b : Bool) : Bool := a && b || (not (a || b))
-- def test_exp (a b : FB p) : FB p := a &&& b ||| (FB.not (a ||| b))

def test_spec (a b : Bool) : Bool := a && (b || a)
def test_exp (a b : FB p) : FB p := FB.and a (FB.or b a)

def test_equiv (a b : FB p) :
  test_exp a b = FB.ofBool (test_spec (FB.toBool a) (FB.toBool b)) := by
  aesop (add simp [test_exp,test_spec,FB.and_spec,FB.or_spec,FB.not_spec,FB.toBool_ofBool,FB.ofBool_toBool])

def test_equiv' (a b : Bool) :
  FB.toBool (p:=p) (test_exp (FB.ofBool a) (FB.ofBool b)) = test_spec a b := by
  aesop (add simp [test_exp,test_spec,FB.and_spec,FB.or_spec,FB.not_spec,FB.toBool_ofBool,FB.ofBool_toBool])

def test_exp_o (a b : F p) : Option (FB p) := do
  let a ← FB.ofF a
  let b ← FB.ofF b
  FB.and a (FB.or b a)

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
def lessThan (w : ℕ) (a b : F p) : Option (F p) := do
  let d := a - b + 2^w
  let d ← num2bits (w + 1) d
  return FB.not d[w]!

def lessEqThan (w : ℕ) (a b : F p) : Option (F p) :=
  lessThan w a (b + 1)

def greaterThan (w : ℕ) (a b : F p) : Option (F p) :=
  lessThan w b a

def greaterEqThan (w : ℕ) (a b : F p) : Option (F p) :=
  lessThan w b (a + 1)

end F

/-- LSB first, like the output of num2bits -/
abbrev FBitVec (p:ℕ) := List (F p)

namespace FBitVec

def default (l:ℕ) : FBitVec p := List.replicate l F.FB.false

def ofF (w:ℕ) (e:F p) : Option (FBitVec p) :=
  num2bits w e

abbrev toF (v:FBitVec p) : F p := bits2num v

-- if arguments are both n-bit long, result is n+1 bits
def binSum (a b : FBitVec p) : Option (FBitVec p) :=
  let sum : F p := a.toF + b.toF
  num2bits (a.length + 1) sum

def assert_eq (a b : FBitVec p) : Option Unit :=
  match a,b with
  | [],[] => some ()
  | ha::tla,hb::tlb => do
      F.FB.assert_eq ha hb
      assert_eq tla tlb
  | _,_ => none

def lessThan (a b : FBitVec p) : F p :=
  (a.zip b).foldl (fun acc (aᵢ, bᵢ) ↦
    let eqᵢ := F.FB.eq aᵢ bᵢ
    (eqᵢ &&& acc) ||| ((F.FB.not eqᵢ) &&& (F.FB.not aᵢ))
  ) F.FB.false

def greaterThan (a b : FBitVec p) : F p :=
  lessThan b a

end FBitVec

abbrev F8 (p:ℕ) [Fact (Primes.fits p 8)] := FBitVec p

namespace F8

variable [Fact (Primes.fits p 8)]

def ofF (x:F p) : Option (F8 p) := do
  FBitVec.ofF 8 x

def ofUInt8 (u:UInt8) : Option (F8 p) :=
  num2bits 8 (u.toNat)

def zero : F8 p := FBitVec.default 8

def eq (a b : F8 p) : F p :=
  List.foldl (fun acc (a,b) => F.FB.and acc (F.FB.eq a b)) F.FB.true (a.zip b)

def assert_eq (a b : F8 p) := FBitVec.assert_eq a b

end F8


abbrev F32 (p:ℕ) [Fact (Primes.fits p 32)] := FBitVec p

namespace F32

variable [Fact (Primes.fits p 32)]

def default : F32 p := FBitVec.default 32

instance : Inhabited (F32 p) where
  default

def ofF (x:F p) : Option (F32 p) := do
  FBitVec.ofF 32 x

def ofF8 [Fact (Primes.fits p 8)] (u8 : F8 p) : F32 p :=
  u8 ++ (List.replicate 24 (0:F p))

def ofUInt32 (u:UInt32) : Option (F32 p) :=
  num2bits 32 (u.toNat)

def add (a b : F32 p) : Option (F32 p) := do
  List.take 32 (← FBitVec.binSum a b)

def assert_eq (a b : F32 p) := FBitVec.assert_eq a b

end F32

abbrev F64 (p:ℕ) [Fact (Primes.fits p 64)] := FBitVec p

namespace F64

variable [Fact (Primes.fits p 64)]

def ofF (x:F p) : Option (F64 p) := do
  FBitVec.ofF 64 x

end F64

instance onlyForDebugF {p:ℕ} : ToString (ZMod p) where
  toString f := f.val

def F8.ofF! {p:ℕ} [Fact (Nat.Prime p)] [Fact (Primes.fits p 8)] : F p → F8 p := Clap.num2bitsLsbPure 8

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
