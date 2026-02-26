import Clap.Lang

namespace Base64Len

open Clap.Lang Core

variable {p : ℕ} [Core p]

def base64UrlDecodedLength (w : ℕ) (m : F p) : Option (F p) := do
  let _ ← num2bits w m                   -- range-check m < 2^w
  let three : F p := share (m + m + m)
  let bits ← num2bits (w + 2) three      -- decompose 3m, proves < 2^(w+2)
  return bits2num (bits.drop 2)          -- drop 2 LSBs = floor(3m/4)\

end Base64Len

namespace TestBase64Len

open Clap.Lang Core ZMod
open Base64Len

abbrev p := Primes.goldilocks

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
