import Clap.Lang

namespace StringExample

open Clap.Lang

variable {p : ℕ} [Fact (Nat.Prime p)] [Core p] [Fact (Primes.fits p 8)]

open Core

def countZeros {maxLen : ℕ} (fs : Vector (F p) maxLen) : Option (F p) := do
  Vector.foldlM (fun (len:F p) f => do
    let b <- F.eq f (const 0)
    some (len + convert b)
  ) (const 0) fs

/--
  Zero-padded vector of bytes of length `len`.
  `len` can at most be `maxLen`.
-/
structure MyString (maxLen : ℕ) where
  chars : Vector (F8 p) maxLen
  len : F p

/--
  Takes an arbitrary vector of field elements and returns a MyString.
  Fails if the input contains an element that is not a byte.
-/
def MyString.ofVec {maxLen : ℕ} (fs : Vector (F p) maxLen) : Option (MyString (p:=p) maxLen) := do
  let zeros <- countZeros fs
  let len := maxLen - zeros
  let chars <- Vector.mapM F8.ofF! fs
  some {chars,len}

end StringExample

namespace TestStringExample

open StringExample
open Clap.Lang

abbrev p := Primes.goldilocks
abbrev F := ZMod p

instance : Coe ℕ F where
  coe n := Core.const (n:ZMod p)

def test {maxLen} (fs : Vector F maxLen) : Option F := do
  let s <- MyString.ofVec (p:=p) (Vector.map Core.const fs)
  s.len

#guard test #v[255,15,0] = some 2
#guard test #v[256,15,0] = none

end TestStringExample
