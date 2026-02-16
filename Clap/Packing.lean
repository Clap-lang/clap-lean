import Clap.Lang

namespace Packing

open Clap.Lang

variable {p : ℕ} [Core p]
open Core

def assertIs64BitLimbs [Fact (Primes.fits p 64)] {numLimbs : ℕ}
  (a : Vector (F p) numLimbs) :
  Option Unit
:= do
  _ ← a.mapM F64.ofF!
  pure ()

def assertIsBytes [Fact (Primes.fits p 8)] {numBytes : ℕ}
  (a : Vector (F p) numBytes) :
  Option Unit
:= do
  _ ← a.mapM F8.ofF!
  pure ()

end Packing

namespace TestPacking

open Packing
open Clap.Lang Core ZMod

abbrev p := Primes.bn254

example : assertIs64BitLimbs (p := p) (#v[1, 2, 3, 4]) = .some () := by native_decide
example : assertIs64BitLimbs (p := p) (#v[1, 2, 3, 2^64-1]) = .some () := by native_decide
example : assertIs64BitLimbs (p := p) (#v[2^64]) = .none := by native_decide
example : assertIs64BitLimbs (p := p) (#v[1, 2, 2^64 + 5]) = .none := by native_decide

example : assertIsBytes (p := p) (#v[1, 2, 3, 4]) = .some () := by native_decide
example : assertIsBytes (p := p) (#v[1, 2, 3, 2^8-1]) = .some () := by native_decide
example : assertIsBytes (p := p) (#v[2^8]) = .none := by native_decide
example : assertIsBytes (p := p) (#v[1, 2, 2^8  + 5]) = .none := by native_decide

end TestPacking
