import Clap.Lang

namespace Base64Len

open Clap.Lang

variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (Primes.fits p 8)]

instance : Coe Char (F p) where
  coe c := c.toNat

/-- From keyless
  Returns the length of the decoded data, given a base64url (unpadded) encoded length `m`.
  @param   MAX_ENCODED_LEN the maximum length of a base64url output, in bytes
  @input   m               the length of the encoded base64url data, in bytes
  @output  decoded_len     the length of the corresponding decoded data, in bytes
  @notes
  explanation why decoded length = \floor{3 * encoded length / 4}
    encoding works as follows:
  suppose plaintext is length \ell
  every 24 bits chunk (3 bytes) is encoded into 32 bits (4 base64url characters)
    specifically, each 6-bit subchunk is mapped to a base64url character
  last chunk could be 1 or 2 bytes though
    case 1: \ell mod 3 = 1
    if it's 1 byte (8 bits), then pad it with 4 zero bits to get 12 bits
    now, encode these 12 bits to 2 base64url characters
      normally, would add another 2 padding characters (i.e., ==), but not for JWTs
    case 2: \ell mod 3 = 2
    if it's 2 bytes (16 bits), then pad it with 2 zero bits to get 18 bits
    now, encode these 18 bits to 3 base64url characters
      normally, would add another 1 padding characters (i.e., =), but not for JWTs
    decoding works as follows:
  suppose encoded length is m
  suppose plaintext is length \ell
  from the algorithm above,
  if m mod 4 = 0, then the input was evenly divisible into 3 byte chunks
    so \ell = 3 * m / 4
  if m mod 4 = 2, then we are in case 1 above, where \ell mod 3 = 1
    so \ell = \floor{3 * m / 4}
      e.g., \ell = 1 => m = 2 => \floor{3 * 2 / 4} = \floor{6/4} = \floor{3/2} = 1
      e.g., \ell = 3 + 1 => m = 4 + 2 => \floor{3 * 6 / 4} = \floor{9/2} = 4
      e.g., \ell = k*3 + 1 => m = k*4 + 2 => \floor{3 * (k*4 + 2) / 4} =
                                           = 3*k + \floor{6/4} = 3*k + 1
  if m mod 4 = 3, then we are in case 2 above, where \ell mod 3 = 2
     e.g., \ell = 2 => m = 3 => \floor{3 * 3 / 4} = \floor{9/4} = 2
     e.g., \ell = 3 + 2 => m = 4 + 3 => \floor{3 * 7 / 4} = \floor{21/4} = 5
     e.g., \ell = k*3 + 2 => m = k*4 + 3 => \floor{3 * (k*4 + 3) / 4} =
                                          = 3*k + \floor{9/4} = 3*k + 2
-/
def base64UrlDecodedLength (w : ℕ) (m : F p) : Option (F p) := do
  let _ ← num2bits w m                   -- range-check m < 2^w
  let three : F p ← share (m + m + m)
  let bits ← num2bits (w + 2) three      -- decompose 3m, proves < 2^(w+2)
  return bits2numV (bits.drop 2)          -- drop 2 LSBs = floor(3m/4)\

/-- From keyless
  Given an 8-bit base64 character, returns its 6-bit decoding.
  Handles the '=' base64 padding character, even though it is not needed for JWTs.
  @input   in   the 8-bit base64 alphabet character
  @output  out  the 6-bit decoded bits corresponding to `in`
  @notes  From
  http://0x80.pl/notesen/2016-01-17-sse-base64-decoding.html#vector-lookup-base
  but modified to support base64url instead.
-/
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
  let eq_minus ← F.eq i '-'
  let sum_minus := sum_09 + eq_minus * 62;

  -- check if i is '_'
  let eq_underscore ← F.eq i '_'
  let sum_underscore := sum_minus + eq_underscore * 63;

  -- check if i is '='
  let eq_eqsign ← F.eq i '='

  -- check if i is zero
  let zero_padding ← isZero i

  -- exactly one case has to be true
  [range_AZ, range_az, range_09, eq_minus, eq_underscore, eq_eqsign, zero_padding]
    |> List.sum
    |> (· - 1)
    |> eq0

  pure sum_underscore

def base64UrlDecode₀ {w} (h:3 ∣ w) (input : Vector (F p) (w*4/3)) : Option (Vector (F p) w) := do
  let tmp : Vector (FBitVec p 6) _ ← input.mapM (num2bits 6)
  let tmp : Vector (FBitVec p 6) _ := tmp.map Vector.reverse
  let tmp : FBitVec p ((w*4/3)*6) := tmp.flatten
  let tmp : Vector (FBitVec p 8) w :=
    have h : (w*4/3)*6 = w * 8 := by
      have h1 : w * 4 / 3 * 6 = w * 8 / 6 * 6 := by grind
      have h2 : w * 8 / 6 * 6 = w * 8 := by grind
      aesop (add safe [h1,h2,Nat.div_mul_cancel])
    toChunks 8 (h ▸ tmp)
  some (tmp.map (fun b ↦ bits2numV b.reverse))

/-
  This function works a bit backward.
  If we know the length of the expected decoded output, then we know the length of the encoded input and also its padding.
  However base64UrlDecodedLength does not support padding base64 `=`
-/
def base64UrlDecode {w} (h:3 ∣ w) (input : FString p (w*4/3)) : Option (FString p w) := do
  let lookedup ← input.data.mapM base64UrlLookup
  let payload ← base64UrlDecode₀ h lookedup
  let len ← base64UrlDecodedLength w input.len
  return ⟨payload, len⟩

end Base64Len

namespace TestBase64Len

open Clap.Lang
open Base64Len

abbrev p := Primes.goldilocks

private def testBase64UrlDecode (input expected : String) (h: 3 ∣ expected.length) : Option (FB p) := do
  let n_input := expected.length * 4 / 3
  let fsinput : FString p n_input := FString.ofString input
  let output : FString p expected.length ← base64UrlDecode (p := p) h fsinput
  output.isPaddedOf expected

example : testBase64UrlDecode "T3JpZ2luYWwgdGV4"     "Original tex" (by decide) = some FB.true := by native_decide
example : testBase64UrlDecode "T3JpZ2luYWwg"         "Original "    (by decide) = some FB.true := by native_decide
example : testBase64UrlDecode "T3JpZ2luYWwgdGV4dA==" ""             (by decide) = some FB.true := by native_decide
example : testBase64UrlDecode "YWJj"     "abc"    (by decide) = some FB.true := by native_decide
example : testBase64UrlDecode "YWJjZGVm" "abcdef" (by decide) = some FB.true := by native_decide

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
