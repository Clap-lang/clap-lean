import Clap.Lang

namespace Base64Len

open Clap.Lang Core

variable {p : ℕ} [Core p]

def base64UrlDecodedLength (w : ℕ) (m : F p) : Option (F p) := do
  let _ ← num2bits w m                   -- range-check m < 2^w
  let three : F p := share (m + m + m)
  let bits ← num2bits (w + 2) three      -- decompose 3m, proves < 2^(w+2)
  return bits2num (bits.drop 2)          -- drop 2 LSBs = floor(3m/4)\

def base64UrlLookup (i : F p) : Option (F p) := do
  -- check if i ∈ ['A', 'Z']
  let ge_A ← F.greaterEqThan 8 i 65
  let le_Z ← F.lessEqThan 8 i 90
  let range_AZ := FB.and ge_A le_Z
  let sum_AZ := convert range_AZ * (i - 65)

  -- check if i ∈ ['a', 'z']
  let ge_a ← F.greaterEqThan 8 i 97
  let le_z ← F.lessEqThan 8 i 122
  let range_az := FB.and ge_a le_z
  let sum_az := sum_AZ + convert range_az * (i - 71)

  -- check if i ∈ ['0', '9']
  let ge_a ← F.greaterEqThan 8 i 48
  let le_z ← F.lessEqThan 8 i 57
  let range_09 := FB.and ge_a le_z
  let sum_09 := sum_az + convert range_09 * (i + 4)

  -- check if i is '-'
  let eq_minus := isZero (i - 45)
  let sum_minus := sum_09 + convert eq_minus * 62;

  -- check if i is '_'
  let eq_underscore := isZero (i - 95)
  let sum_underscore := sum_minus + convert eq_underscore * 63;

  -- check if i is '='
  let eq_eqsign := isZero (i - 61)

  -- check if i is zero
  let zero_padding := isZero i

  -- exactly one case has to be true
  [range_AZ, range_az, range_09, eq_minus, eq_underscore, eq_eqsign, zero_padding]
    |> List.map convert
    |> List.sum
    |> (· - 1)
    |> eq0

  pure sum_underscore

end Base64Len

namespace TestBase64Len

open Clap.Lang Core ZMod
open Base64Len

abbrev p := Primes.goldilocks

example : base64UrlLookup (p := p) 'A'.toNat == some 0 := by native_decide
example : base64UrlLookup (p := p) 'Z'.toNat == some 25 := by native_decide
example : base64UrlLookup (p := p) 'a'.toNat == some 26 := by native_decide
example : base64UrlLookup (p := p) 'z'.toNat == some 51 := by native_decide
example : base64UrlLookup (p := p) '0'.toNat == some 52 := by native_decide
example : base64UrlLookup (p := p) '9'.toNat == some 61 := by native_decide
example : base64UrlLookup (p := p) '-'.toNat == some 62 := by native_decide
example : base64UrlLookup (p := p) '_'.toNat == some 63 := by native_decide
example : base64UrlLookup (p := p) '='.toNat == some 0 := by native_decide
example : base64UrlLookup (p := p) 0 == some 0 := by native_decide
example : base64UrlLookup (p := p) 64 == none := by native_decide

example : base64UrlDecodedLength (p := p) 8 0  = some 0  := by native_decide
example : base64UrlDecodedLength (p := p) 8 2  = some ((3 * 2 / 4) : Nat)  := by native_decide
example : base64UrlDecodedLength (p := p) 8 3  = some ((3 * 3 / 4) : Nat)  := by native_decide
example : base64UrlDecodedLength (p := p) 8 4  = some ((3 * 4 / 4) : Nat)  := by native_decide
example : base64UrlDecodedLength (p := p) 8 6  = some ((3 * 6 / 4) : Nat)  := by native_decide
example : base64UrlDecodedLength (p := p) 8 7  = some ((3 * 7 / 4) : Nat)  := by native_decide
example : base64UrlDecodedLength (p := p) 8 8  = some ((3 * 8 / 4) : Nat)  := by native_decide
example : base64UrlDecodedLength (p := p) 8 10 = some ((3 * 10 / 4) : Nat)  := by native_decide
example : base64UrlDecodedLength (p := p) 8 11 = some ((3 * 11 / 4) : Nat)  := by native_decide
example : base64UrlDecodedLength (p := p) 8 12 = some ((3 * 12 / 4) : Nat)  := by native_decide
example : base64UrlDecodedLength (p := p) 8 16 = some ((3 * 16 / 4) : Nat) := by native_decide
example : base64UrlDecodedLength (p := p) 8 20 = some ((3 * 20 / 4) : Nat) := by native_decide
example : base64UrlDecodedLength (p := p) 10 0 = some ((3 * 0 / 4) : Nat) := by native_decide
example : base64UrlDecodedLength (p := p) 10 4 = some ((3 * 4 / 4) : Nat) := by native_decide
example : base64UrlDecodedLength (p := p) 10 8 = some ((3 * 8 / 4) : Nat) := by native_decide
example : base64UrlDecodedLength (p := p) 10 2 = some ((3 * 2 / 4) : Nat) := by native_decide
example : base64UrlDecodedLength (p := p) 10 3 = some ((3 * 3 / 4) : Nat) := by native_decide
example : base64UrlDecodedLength (p := p) 10 5 = some ((3 * 5 / 4) : Nat) := by native_decide
example : base64UrlDecodedLength (p := p) 10 100 = some ((3 * 100 / 4) : Nat) := by native_decide
example : base64UrlDecodedLength (p := p) 10 1024 = none := by native_decide

end TestBase64Len
