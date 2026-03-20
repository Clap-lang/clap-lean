import Clap.Lang

namespace Base64Len

open Clap.Lang Core

variable {p : ℕ} [Core p]

instance : Coe Char (F p) where
  coe c := c.toNat

def base64UrlDecodedLength (w : ℕ) (m : F p) : Option (F p) := do
  let _ ← num2bits w m                   -- range-check m < 2^w
  let three : F p := share (m + m + m)
  let bits ← num2bits (w + 2) three      -- decompose 3m, proves < 2^(w+2)
  return bits2num (bits.drop 2)          -- drop 2 LSBs = floor(3m/4)\

def base64UrlLookup (i : F p) : Option (F p) := do
  -- check if i ∈ ['A', 'Z']
  let ge_A ← F.greaterEqThan 8 i 'A'
  let le_Z ← F.lessEqThan 8 i 'Z'
  let range_AZ := ge_A &&& le_Z
  let sum_AZ := range_AZ * (i - 65)

  -- check if i ∈ ['a', 'z']
  let ge_a ← F.greaterEqThan 8 i 'a'
  let le_z ← F.lessEqThan 8 i 'z'
  let range_az := ge_a &&& le_z
  let sum_az := sum_AZ + range_az * (i - 71)

  -- check if i ∈ ['0', '9']
  let ge_a ← F.greaterEqThan 8 i '0'
  let le_z ← F.lessEqThan 8 i '9'
  let range_09 := ge_a &&& le_z
  let sum_09 := sum_az + range_09 * (i + 4)

  -- check if i is '-'
  let eq_minus := F.eq i '-'
  let sum_minus := sum_09 + eq_minus * 62;

  -- check if i is '_'
  let eq_underscore := F.eq i '_'
  let sum_underscore := sum_minus + eq_underscore * 63;

  -- check if i is '='
  let eq_eqsign := F.eq i '='

  -- check if i is zero
  let zero_padding := isZero i

  -- exactly one case has to be true
  [range_AZ, range_az, range_09, eq_minus, eq_underscore, eq_eqsign, zero_padding]
    |> List.sum
    |> (· - 1)
    |> eq0

  pure sum_underscore

def base64UrlDecode₀ (n : ℕ) (input : Array (F p)) : Option (Array (F p)) := do
  if h : n > 0 then
    let seq4Times6Bits ← input.take 4 |>.mapM (num2bits 6)
    let seq3Times8Bits := seq4Times6Bits.reverse.toList.flatten.toChunks 8
    let out := seq3Times8Bits.reverse.map bits2num
    return Array.append ⟨out.take n⟩ (←base64UrlDecode₀ (n - 3) (input.drop 4))
  else
    return .empty

def base64UrlDecode (n : ℕ) (input : Array (F p)) : Option (Array (F p)) := do
  let a ← input.mapM base64UrlLookup
  base64UrlDecode₀ n a

end Base64Len

namespace TestBase64Len

open Clap.Lang Core ZMod
open Base64Len

abbrev p := Primes.goldilocks

private def testBase64UrlDecode (n : ℕ) (s : String) : Option String := do
  let input := s.toList.map Char.toNat |>.map (fun n ↦ (ofNat(n) : ZMod p))
  let output ← base64UrlDecode (p := p) n input.toArray
  return String.ofList <| output.toList.map (fun z => Char.ofNat z.val)

example : testBase64UrlDecode 13 "T3JpZ2luYWwgdGV4dA==" == "Original text" := by
  native_decide
example : testBase64UrlDecode  8 "T3JpZ2luYWwgdGV4dA==" == "Original" := by
  native_decide
example : testBase64UrlDecode  0 "T3JpZ2luYWwgdGV4dA==" == "" := by
  native_decide
example : testBase64UrlDecode  3 "YWJj" == "abc" := by
  native_decide
example : testBase64UrlDecode  5 "YWJjZGU=" == "abcde" := by
  native_decide

example : base64UrlLookup (p := p) 'A' == some 0 := by native_decide
example : base64UrlLookup (p := p) 'T' == some 19 := by native_decide
example : base64UrlLookup (p := p) 'Z' == some 25 := by native_decide
example : base64UrlLookup (p := p) 'a' == some 26 := by native_decide
example : base64UrlLookup (p := p) 'z' == some 51 := by native_decide
example : base64UrlLookup (p := p) '0' == some 52 := by native_decide
example : base64UrlLookup (p := p) '9' == some 61 := by native_decide
example : base64UrlLookup (p := p) '-' == some 62 := by native_decide
example : base64UrlLookup (p := p) '_' == some 63 := by native_decide
example : base64UrlLookup (p := p) '=' == some 0 := by native_decide
example : base64UrlLookup (p := p) 0   == some 0 := by native_decide
example : base64UrlLookup (p := p) 64  == none := by native_decide

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
