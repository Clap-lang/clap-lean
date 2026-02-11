import Clap.SpecUint

namespace StringExample

open Clap.Lang

variable {p : ℕ} [Fact (Nat.Prime p)] [Core p] [Fact (Primes.fits p 8)]

open Core

structure MyString (maxLen : ℕ) where
  chars : Vector (F8 p) maxLen
  len : F (p:=p)

def assertString {maxLen : ℕ} (s : MyString (p:=p) maxLen) : Option Unit := do
  for i in [0:maxLen] do
    let b <- F8.eq s.chars[i]! F8.zero
    -- not(i<len) <-> len<=i
    let expected <- F.lessThanEq maxLen (s.len) (const (i:ZMod p))
    FB.assert_eq b expected

end StringExample

namespace TestStringExample

open StringExample
open Clap.Lang

abbrev p := Primes.goldilocks
abbrev F' := ZMod p

def test {maxLen} (chars : Vector UInt8 maxLen) (len : ℕ) := do
  let chars <- Vector.mapM F8.ofUInt8 chars
  assertString (p:=p) { chars, len }

#guard (test #v[0x11,0x15,0x00] 2 ) = some ()
#guard (test #v[0x11,0x15,0x00] 3 ) = none

end TestStringExample
