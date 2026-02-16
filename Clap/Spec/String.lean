import Clap.Lang
import Clap.Spec
import Clap.Spec.F
import Clap.Spec.BitVec

namespace Clap.Spec.String

open Clap.Lang

variable {p : ℕ} [abstractCore : Core p] [Fact (Primes.fits p 8)]

open Core

/--
info: abstractCore
-/
#guard_msgs in
#synth Core p

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

end Clap.Spec.String

namespace TestStringExample

open Clap.Lang Core ZMod
open Clap.Spec.String

abbrev p := Primes.babybear

def test {maxLen} (fs : Vector (F p) maxLen) : Option (F p) := do
  let s <- MyString.ofVec fs
  s.len

#guard test #v[255,15,0] = some 2
#guard test #v[256,15,0] = none

end TestStringExample
