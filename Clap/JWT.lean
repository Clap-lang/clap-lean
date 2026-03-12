import Clap.Lang
import Clap.Array

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

def bracketsMap (input : List (F p)) : List (FB p) :=
  input.map (fun c ↦ isOpenBracket c - isClosedBracket c)
 where
  /-- Returns true if the character is '{' -/
  isOpenBracket (c : F p) : FB p := F.eq c 123
  /-- Returns true if the character is '}' -/
  isClosedBracket (c : F p) : FB p := F.eq c 125

private def bracketsDepthMapRev₀ (input : List (F p)) : List (F p) × F p :=
  input.foldl
    ( fun (acc, depth) i ↦
        -- The value is the depth from the previous position, except when i = (-1)
        let i' := depth - F.eq i (-1)
        -- Update the depth
        let depth' := depth + i
        (i' :: acc, depth')
    )
    ([], 0)

def bracketsDepthMap (input : List (F p)) : List (F p) :=
  (bracketsDepthMapRev₀ input).1.reverse.map minusOne
 where
  --  The outermost open and closed bracket are both ignored.
  minusOne (a : F p) : F p := a - 1 + isZero a

def hadamardProduct (lhs rhs : List (F p)) : List (F p) :=
  lhs.zipWith (· * ·) rhs

def escalarProduct (i₁ i₂ : List (F p)) : F p :=
  let p := hadamardProduct i₁ i₂
  p.sum

/-
  `bracketsDepthMap` must be an output of `bracketsDepthMap`.
-/
def enforceNotNested (len : ℕ)
  (startIndex fieldLen : F p)
  (bracketsDepthMap : List (F p)) :
  Option Unit
:= do
  let endIndex := startIndex + fieldLen
  let bracketsSelector ← FArray.arraySelector len startIndex endIndex
  let bracketsSelector := bracketsSelector.toList
  let o := escalarProduct bracketsDepthMap bracketsSelector
  eq0 o

private def email : List (F p) := [101, 109, 97, 105, 108] -- «email»
private def requiredEvName : List (F p) :=
    -- «email_verified»
    [101, 109, 97, 105, 108, 95, 118, 101, 114, 105, 102, 105, 101, 100]
private def requiredEvValLen4 : List (F p) := [116, 114, 117, 101] -- «true»
private def requiredEvValLen6 : List (F p) :=
  -- «"true"»
  [34, 116, 114, 117, 101, 34]

def emailVerifiedCheck
  (uidNameLen : F p)
  (uidName : List (F p))
  (evName : List (F p))
  (evValueLen : F p)
  (evValue : List (F p))
  : Option (FB p)
:= do
  let uidIsEmail :=
    F.eq uidNameLen 5 * (uidName.zipWith F.eq email).foldl (· * ·) 1
  conditionallyAssert uidIsEmail <|
    (evName.zipWith F.eq requiredEvName).foldl (· * ·) 1
  let evValLenIs4 := F.eq evValueLen 4
  let evValLenIs6 := F.eq evValueLen 6
  let evValLenOk := FB.or evValLenIs4 evValLenIs6
  conditionallyAssert uidIsEmail evValLenOk

  let checkEvValBool := evValLenIs4 * uidIsEmail
  conditionallyAssert checkEvValBool <|
    (evValue.zipWith F.eq requiredEvValLen4).foldl (· * ·) 1

  let checkEvValString := evValLenIs6 * uidIsEmail
  conditionallyAssert checkEvValString <|
    (evValue.zipWith F.eq requiredEvValLen6).foldl (· * ·) 1
  return uidIsEmail
 where
  conditionallyAssert (antecedent consequent : FB p) : Option Unit :=
    -- a → c ≡ ¬(a ∧ ¬c)
    eq0 (antecedent * FB.not consequent)

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

private def br :=
  parseCharsASCII
    ['{', 'h', 'e', '{', 'l', 'l', 'o', '{', '}', 'w', 'o', 'r', 'l', 'd', '!', '}', '}']
example :
  bracketsMap (p := p) br == [1, 0, 0, 1, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, -1, -1]
:= by
  native_decide

private def plusMinusOneBr₁ : List (F p) :=
  [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, -1]
example :
  bracketsDepthMap plusMinusOneBr₁ ==
    [0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0]
:= by
  native_decide

private def plusMinusOneBr₂ : List (F p) :=
  [1,1,1,1,1,-1,-1,-1,-1,-1]

example : bracketsDepthMap plusMinusOneBr₂ == [0, 0, 1, 2, 3, 3, 2, 1, 0, 0] := by
  native_decide

example :
  enforceNotNested (p := p) 10 0 2 [0, 0, 1, 2, 3, 3, 2, 1, 0, 0] == .some ()
:= by
  native_decide

example : enforceNotNested
  (p := p) 10 8 10 [0, 0, 1, 2, 3, 3, 2, 1, 0, 0] == .some ()
:= by
  native_decide

example :
  enforceNotNested (p := p) 10 2 4 [0, 0, 1, 2, 3, 3, 2, 1, 0, 0] == .none
:=
  by native_decide

example : -- uid is «email»; «email_verified» is «true»
  emailVerifiedCheck (p := p) 5 email requiredEvName 4 requiredEvValLen4  == .some 1
:= by
  native_decide

example : -- uid is «email»; «email_verified» is «"true"»
  emailVerifiedCheck (p := p) 5 email requiredEvName 6 requiredEvValLen6 == .some 1
:= by
  native_decide

example : -- uid is «email», but there is no «email_verified»
  emailVerifiedCheck (p := p) 5 email [1,2,3] 6 requiredEvValLen6 == .none
:= by
  native_decide

example : -- uid is «email», but «email_verified» is neither «true» nor «"true"»
  emailVerifiedCheck (p := p) 5 email requiredEvName 3 [4, 5, 6] == .none
:= by
  native_decide

example : -- uid is not «email»
  emailVerifiedCheck (p := p) 0 [] requiredEvName 6 requiredEvValLen6 == .some 0
:= by native_decide

example : -- uid is not «email», the rest doesn't matter
  emailVerifiedCheck (p := p) 0 [] [1, 2, 3] 3 [4, 5, 6] == .some 0
:= by native_decide

end TestJWT
