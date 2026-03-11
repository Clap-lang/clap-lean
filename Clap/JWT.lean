import Clap.Lang

namespace JWT

open Clap.Lang Core

variable {p : ℕ} [Core p]

private def stringBodiesRev₀ (input : List (F p)) : List (FB p) × FB p × FB p :=
  input.foldl
    ( fun (acc, openedQuotes, escaped) c ↦
        let isNonEscQuotationMark := isQuotationMark c * FB.not escaped
        let acc' := openedQuotes * FB.not isNonEscQuotationMark :: acc
        let openedQuotes' := FB.xor openedQuotes isNonEscQuotationMark
        let escaped' := isBackslash c * FB.not escaped
        (acc', openedQuotes', escaped')
    )
    ([], default, default)
 where
  isQuotationMark (c : F p) : FB p := F.eq c 34
  isBackslash (c : F p) : FB p := F.eq c 92

def stringBodies (input : List (F p)) : List (FB p) :=
  (stringBodiesRev₀ input).1.reverse

end JWT

namespace TestJWT

open JWT

open Clap.Lang Core ZMod

abbrev p := Primes.bn254

private def parseCharsASCII (s : List Char) : List (ZMod p) :=
  s.map (fun n ↦ (ofNat(n.toNat) : ZMod p))

/-
  { a "a\"a" } →
  000001111000
-/
private def str₀ :=
  parseCharsASCII ['{', ' ', 'a', ' ', '"', 'a', '\\', '"', 'a', '"', ' ', '}']
example : stringBodies (p := p) str₀ == [0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0] := by
  native_decide

/-
  "i\i""i" →
  01110010
-/
private def str₁ := parseCharsASCII ['"', 'i', '\\', 'i', '"', '"', 'i', '"']
example : stringBodies (p := p) str₁ == [0, 1, 1, 1, 0, 0, 1, 0] := by
  native_decide

/-
  "i\"\\\"i" →
  0111111110
-/
private def str₂ :=
  parseCharsASCII ['"', 'i', '\\', '"', '\\', '\\', '\\',  '"', 'i', '"']
example : stringBodies (p := p) str₂ == [0, 1, 1, 1, 1, 1, 1, 1, 1, 0] := by
  native_decide

/-
  """""" →
  000000
-/
private def str₃ := parseCharsASCII ['"', '"', '"', '"', '"', '"']
example : stringBodies (p := p) str₃ == [0, 0, 0, 0, 0, 0] := by native_decide

/-
  \"\""i"\"\" →
  00000100000
-/
private def str₄ :=
  parseCharsASCII ['\\', '"', '\\', '"','"', 'i', '"', '\\', '"', '\\', '"']
example : stringBodies (p := p) str₄ == [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by
  native_decide

/-
  \\"\\" →
  000110
-/
private def str₅ := parseCharsASCII ['\\', '\\', '"', '\\', '\\', '"']
example : stringBodies (p := p) str₅ == [0, 0, 0, 1, 1, 0] := by native_decide


end TestJWT
