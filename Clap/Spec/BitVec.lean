import Clap.Spec
import Clap.Lang
import Clap.Spec.F
import Clap.Spec.FB

open Clap.Lang Clap.Spec Core

/-- LSB first, like the output of num2bits -/
abbrev FBitVec (p : ℕ) [Core p] := List (FB p)

namespace FBitVec

variable {p : ℕ} [Core p]

def default (l : ℕ) : FBitVec p := List.replicate l 0

abbrev zero (l : ℕ) : FBitVec p := default l

def ofF (w : ℕ) (e : F p) : FBitVec p :=
  Option.getD (num2bits w e) (default w)

def ofF! (w : ℕ) (e : F p) : Option (FBitVec p) :=
  num2bits w e

abbrev toF (v : FBitVec p) : F p := Core.bits2num v

-- if arguments are both n-bit long, result is n+1 bits
def binSum (a b : FBitVec p) : FBitVec p := Option.getD (do
  let sum : F p := a.toF + b.toF
  num2bits (a.length + 1) sum)
  (FBitVec.default (a.length + 1))

def assertEq (a b : FBitVec p) : Option Unit :=
  for (a,b) in a.zip b do
    FB.assertEq a b

end FBitVec

abbrev F8 (p:ℕ) [Fact (Primes.fits p 8)] [Core p] := FBitVec p

namespace F8

variable {p : ℕ} [Core p] [Fact (Primes.fits p 8)]

def zero : F8 p := FBitVec.zero 8

instance : Inhabited (F8 p) := ⟨zero⟩

def ofF (x : F p) : (F8 p) :=
  FBitVec.ofF 8 x

def ofF! (x : F p) : Option (F8 p) :=
  FBitVec.ofF! 8 x

def ofUInt8 (u : UInt8) : Option (F8 p) :=
  num2bits 8 (u.toNat)

def eq (a b : F8 p) : Option (FB p) :=
  (a.zip b).foldlM (fun acc (a,b) ↦ (FB.and acc) <$> (FB.eq a b)) FB.true

def assertEq (a b : F8 p) := FBitVec.assertEq a b

end F8

abbrev F32 (p : ℕ) [Fact (Primes.fits p 32)] [Core p] := FBitVec p

namespace F32

variable {p : ℕ} [Core p] [Fact (Primes.fits p 8)] [Fact (Primes.fits p 32)]

def zero : F32 p := FBitVec.zero 32

instance : Inhabited (F32 p) := ⟨zero⟩

def ofF (x : F p) : F32 p :=
  FBitVec.ofF 32 x

def ofF8 (u8 : F8 p) : F32 p :=
  u8 ++ (List.replicate 24 (0 : FB p))

def ofUInt32 (u : UInt32) : Option (F32 p) :=
  num2bits 32 (u.toNat)

def add (a b : F32 p) : F32 p :=
  List.take 32 (FBitVec.binSum a b)

def assert_eq (a b : F32 p) := FBitVec.assertEq a b

instance : Add (F32 p) := ⟨add⟩

end F32
