import Mathlib.Tactic.Cases

import Clap.Lang
import Clap.Array
import Clap.FString
import Clap.HashToField

namespace JWT

open Clap.Lang Primes

open ZMod

variable {p : ℕ} [Fact (Nat.Prime p)] [DecidableEq (F p)]

open FB

def isEscape (l : List (F p)) (i : Fin l.length) : Bool :=
  match _ : i.val with
  | 0 => l[i] = '\\'
  | i' + 1 => l[i] = '\\' ∧ ¬ isEscape l ⟨i', by lia⟩

def isQuotation (l : List (F p)) (i : Fin l.length) : Bool :=
  match _ : i.val with
  | 0 => l[i] = '"'
  | i' + 1 => l[i] = '"' ∧ ¬ isEscape l ⟨i', by lia⟩

def oddNrQuotesUntil (l : List (F p)) (i : Fin l.length) : Bool :=
  Odd {j | j ≤ i ∧ isQuotation l j}.toFinset.card

def isInQuotes (l : List (F p)) (i : Fin l.length) : Bool :=
  ¬isQuotation l i ∧ oddNrQuotesUntil l i

def stringBody' (openedQuotes : FB p) (escaped : FB p) : List (FB p) → List (FB p)
| [] => []
| c :: cs =>
  let isNonEscQuotationMark := FB.and ((F.eq c '\"').get!) (FB.not escaped)
  let openedQuotes' := FB.xor openedQuotes isNonEscQuotationMark
  let escaped' := FB.and (F.eq c '\\').get! (FB.not escaped)
  openedQuotes * FB.not isNonEscQuotationMark :: stringBody' openedQuotes' escaped' cs

def stringBody : List (FB p) → List (FB p) := stringBody' 0 0

/--
  Given an array of ASCII characters `arr`, returns an array `brackets` with
  a 1 in the position of each open bracket `{`, a -1 in the position of each closed bracket `}`
  and 0 everywhere else.
  See an example below. The real string is `arr` but we re-display it with "fake" spaces in `align_arr`
  to more easily showcase which character in `arr` corresponds to the `-1` in `brackets`.
  arr:       {he{llo{}world!}}
  align_arr: {he{llo{ }world! } }
  brackets:  10010001-1000000-1-1
  where `arr` is represented by its ASCII encoding, i.e. `{` = 123
-/
def bracketsMap (input : List (F p)) : Option (List (FB p)) := do
  input.mapM (fun c ↦ do
    let eqOpen ← F.eq c '{'
    let eqClose ←F.eq c '}'
    some (eqOpen - eqClose))

private def bracketsDepthMapRev₀ (input : List (F p)) : Option (List (F p) × F p) := do
  input.foldlM
    ( fun (acc, depth) i ↦ do
        -- The value is the depth from the previous position, except when i = (-1)
        let i' := depth - (←F.eq i (-1))
        -- Update the depth
        let depth' := depth + i
        (i' :: acc, depth')
    )
    ([], 0)

/--
  Given an input array `arr` of length `LEN` containing `1`s corresponding to open
  brackets `{`, `-1`s corresponding to closed brackets `}`, and 0s everywhere else, outputs an array
  containing a positive integer in each index between nested brackets which indicates the depth
  of the brackets nesting at that index, and 0 everywhere else. The outermost open and
  closed bracket are both ignored. The open and closed brackets are not considered to be inside
  their bracketed area. It is assumed that the input will contain an equal
  number of closed and open brackets, and that a closed bracket will not appear while there are no unclosed open brackets
  The basic algorithm is:
  1. Compute an intermediate array where each index is a running sum of all previous indices in the input
  2. Subtract 1 from each index in the result of step 1 to get a new array. This corresponds to ignoring the single pair of outermost brackets in the running sum from step 1
  3. For each negative value in the result of step 2, change that value to 0
  4. For each value greater than 1 compared to the previous value in the result of step 3, decrement that value by 1. This is to fix an off-by-1 error with step 1 in computing nested brackets depth, so that each depth excludes its open bracket. I.e.
  step 4 in:  001112233332100
  step 4 out: 000111223332100
  Example input/output for the entire subcircuit, plus intermediate values
  To preserve alignment, we use * to represent -1:
  str:           a{aaa{a{aaa}aa}aaaa}
  arr:           01000101000*00*0000*
  prelim_out1:   01111223333222111110   full depth map incorrectly including open brackets inside bracket depth counts
  prelim_out2:   *000011222211100000*   removes outermost brackets from depth map
  prelim_out3:   00000112222111000000   replaces negative values with 0s
  out:           00000011222111000000   correctly represents open brackets as being outside of bracket nesting
  out: 0000001122 11 0000 0
-/
def bracketsDepthMap (input : List (F p)) : Option (List (F p)) := do
  (←bracketsDepthMapRev₀ input).1.reverse.mapM minusOne
 where
  --  The outermost open and closed bracket are both ignored.
  minusOne (a : F p) : Option (F p) := do a - 1 + (←isZero a)

def hadamardProduct (lhs rhs : List (F p)) : List (F p) :=
  lhs.zipWith (· * ·) rhs

def escalarProduct (i₁ i₂ : List (F p)) : F p :=
  let p := hadamardProduct i₁ i₂
  p.sum

/--
  Given an input `brackets_depth_map`, which must be an output of `BracketsDepthMap` and
  corresponds to the nested brackets depth of the original JWT, and a `start_index` and `field_len`
  corresponding to the first index and length of a full field in the JWT, fails if the given field
  contains any indices inside nested brackets in the original JWT, and succeeds otherwise
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

def FList.eq : List (F p) → List (F p) → Option (FB p)
| x :: xs, y :: ys => return (←F.eq x y) * (←FList.eq xs ys)
| [], [] => return 1
| _, _ => return 0

private def email : List (F p) := "email".toList -- «email»
private def requiredEvName : List (F p) := "email_verified".toList -- «email_verified»
private def requiredEvValLen4 : List (F p) := "true".toList -- «true»
private def requiredEvValLen6 : List (F p) := "\"true\"".toList -- «"true"»

/--
  Enforce that if uid name is "email", the email verified field is either true or "true"
-/
def emailVerifiedCheck
  (uidName : List (F p))
  (evName : List (F p))
  (evValue : List (F p))
  : Option (FB p)
:= do
  let uidIsEmail ← FList.eq uidName email
  conditionallyAssert uidIsEmail (←FList.eq evName requiredEvName)
  conditionallyAssert uidIsEmail
    (((←FList.eq evValue requiredEvValLen4) ||| (←FList.eq evValue requiredEvValLen6)) : FB p)
  return uidIsEmail
 where
  conditionallyAssert (antecedent consequent : FB p) : Option Unit :=
    -- a → c ≡ ¬(a ∧ ¬c)
    eq0 (antecedent * FB.not consequent)

open Primes HashToField FString FArray in
/--
  Asserts structural correctness of a JWT key-value pair field.
  Marked as private, see not secure warning below.

  Given `field` of the form `"name":value,` (or ending with `}`), this enforces:
  - `name_len < colon_index`           (colon comes after name)
  - `colon_index < value_index`        (value starts after colon)
  - `field_len > name_len + value_len` (field is long enough)
  - `field[0] == '"'`                  (name starts with quote)
  - `name` is a substring of `field` starting at index 1
  - `field[name_len + 1] == '"'`       (name ends with quote)
  - `field[colon_index] == ':'`
  - `value` is a substring of `field` starting at `value_index`
  - `field[field_len - 1] == ',' or '}'`

  Specialised to `Primes.bn254` because `assertIsSubstringFS` uses Poseidon.

  WARNING: this function is NOT secure on its own; it must be called from
  `parseJWTFieldWithQuotedValue` or `parseJWTFieldWithUnquotedValue`.

  The `skipChecks` parameter models CIRCOM's `skip_checks` signal: when `1`, semantic
  assertions (name matching, character equality, etc.) are bypassed. CIRCOM implements
  this by collecting all checks into booleans and asserting `checks_pass OR skip_checks === 1`.
  We model this equivalently by gating each semantic constraint with `perform = NOT(skipChecks)`:
  `perform * constraint === 0`.

  Sub-template constraints (Num2Bits, one-hot encoding, byte validation) are enforced
  unconditionally via monadic `←` binds, matching CIRCOM where sub-templates always
  apply their internal constraints. With `skipChecks = 1`, the prover must still provide
  well-formed inputs (valid byte values, in-range indices). Default is `0` (checks enabled).
-/
private def parseJWTFieldSharedLogic
    {maxKVPairLen maxNameLen maxValueLen : ℕ}
    (h_name  : maxNameLen  ≤ maxKVPairLen)
    (h_value : maxValueLen ≤ maxKVPairLen)
    (field       : FString bn254 maxKVPairLen)
    (name        : FString bn254 maxNameLen)
    (value       : FString bn254 maxValueLen)
    (colon_index : F bn254)
    (value_index : F bn254)
    (skipChecks  : FB bn254 := 0)
    : Option Unit := do
  let perform : FB bn254 := FB.not skipChecks
  -- Check 0: name_len < colon_index
  -- w = 20 bits suffices for comparisons: 2^20 = 1_048_576 > any realistic JWT field length.
  -- Hardcoded in https://github.com/aptos-labs/keyless-zk-proofs/blob/main/circuit/templates/helpers/jwt/ParseJWTFieldSharedLogic.circom
  let w := 20
  F.guardedEq0 perform (FB.not (← F.lessThan w name.len colon_index))
  -- Check 1: colon_index < value_index
  F.guardedEq0 perform (FB.not (← F.lessThan w colon_index value_index))
  -- Check 2: field_len > name_len + value_len
  F.guardedEq0 perform (FB.not (← F.greaterThan w field.len (name.len + value.len)))
  -- Pre-compute hash of field for Fiat-Shamir substring checks
  let fieldHash ← hashBytesToField field
  -- Check 3: field[0] == '"' (ASCII 34)
  let firstChar ← selectArrayValue field.data 0
  F.guardedAssertEq perform firstChar '\"'
  -- Check 4: name is a substring of field starting at index 1
  let nameOk ← isSubstringFS h_name field fieldHash name 1
  F.guardedEq0 perform (FB.not nameOk)
  -- Check 5: field[name_len + 1] == '"' (ASCII 34)
  let nameClosingQuote ← selectArrayValue field.data (name.len + 1)
  F.guardedAssertEq perform nameClosingQuote '\"'
  -- Check 6: field[colon_index] == ':' (ASCII 58)
  let colonChar ← selectArrayValue field.data colon_index
  F.guardedAssertEq perform colonChar ':'
  -- Check 7: value is a substring of field starting at value_index
  let valueOk ← isSubstringFS h_value field fieldHash value value_index
  F.guardedEq0 perform (FB.not valueOk)
  -- Check 8: field[field_len - 1] == ',' (44) or '}' (125)
  let lastChar ← selectArrayValue field.data (field.len - 1)
  -- Enforce (lastChar - 44) * (lastChar - 125) == 0
  F.guardedEq0 perform ((lastChar - (',' : F _)) &&& (lastChar - ('}' : F _)))

open Primes HashToField FString FArray in
/--
  Asserts structural correctness of a JWT key-value pair field with an **unquoted** value.
  Wraps `parseJWTFieldSharedLogic` with two additional checks:

  1. **Whitespace zones**: every character in the three gaps
     - `[name_len + 2, colon_index)` (between closing name-quote and colon)
     - `[colon_index + 1, value_index)` (between colon and value)
     - `[value_index + value_len, field_len - 1)` (after value, before the final `,`/`}`)
     must be a whitespace character (ASCII 9–13 or 32).

  2. **Value purity**: no character within `[value_index, value_index + value_len)` may be
     `,` (44), `}` (125), or `"` (34).

  Specialised to `Primes.bn254` because `assertIsSubstringFS` uses Poseidon.
  See `skipChecks` note of `parseJWTFieldSharedLogic`.
-/
def parseJWTFieldWithUnquotedValue
    {maxKVPairLen maxNameLen maxValueLen : ℕ}
    (h_name  : maxNameLen  ≤ maxKVPairLen)
    (h_value : maxValueLen ≤ maxKVPairLen)
    (field       : FString bn254 maxKVPairLen)
    (name        : FString bn254 maxNameLen)
    (value       : FString bn254 maxValueLen)
    (colon_index : F bn254)
    (value_index : F bn254)
    (skipChecks  : FB bn254 := 0)
    : Option Unit := do
  -- Delegate shared structural checks
  parseJWTFieldSharedLogic h_name h_value field name value colon_index value_index skipChecks
  let perform : FB bn254 := FB.not skipChecks
  -- Check 1: whitespace in three zones
  -- Zone A: [name_len + 2, colon_index)  — between closing name-quote and colon
  -- Zone B: [colon_index + 1, value_index)  — between colon and value (no quote around value)
  -- Zone C: [value_index + value_len, field_len - 1)  — after value, before terminator
  let zoneA ← arraySelectorComplex maxKVPairLen (name.len + 2) colon_index
  let zoneB ← arraySelectorComplex maxKVPairLen (colon_index + 1) value_index
  let zoneC ← arraySelectorComplex maxKVPairLen (value_index + value.len) (field.len - 1)
  -- Merge zones: inZone[i] = zoneA[i] ∨ zoneB[i] ∨ zoneC[i]
  let inZone := (zoneA.zipWith FB.or zoneB).zipWith FB.or zoneC
  -- For each position in a whitespace zone, the character must be whitespace
  (inZone.zip field.data).toList.forM fun (z, c) ↦ do
    let ws ← F8.isWhitespace c
    F.guardedEq0 perform (z &&& FB.not ws)
  -- Check 2: value must not contain ',', '}', or '"'
  -- valueSelector: 1s at [value_index, value_index + value_len)
  let valueSel ← arraySelector maxKVPairLen value_index (value_index + value.len)
  (valueSel.zip field.data).toList.forM fun (sel, c) ↦ do
    let isForbidden := (←F.eq c ',') ||| (←F.eq c '}') ||| (←F.eq c '\"')
    -- If in value range, character must not be forbidden
    F.guardedEq0 perform (sel &&& isForbidden)

open Primes HashToField FString FArray in
/--
  Asserts structural correctness of a JWT key-value pair field with a **quoted** value.
  Wraps `parseJWTFieldSharedLogic` with three additional checks:

  1. **Quote checks**: `field[value_index - 1] == '"'` and `field[value_index + value_len] == '"'`.

  2. **Whitespace zones**: every character in the three gaps
     - `[name_len + 2, colon_index)` (between closing name-quote and colon)
     - `[colon_index + 1, value_index - 1)` (between colon and opening value-quote)
     - `[value_index + value_len + 1, field_len - 1)` (after closing value-quote, before terminator)
     must be a whitespace character (ASCII 9–13 or 32).

  3. **String bodies**: `field_string_bodies[i]` must be 1 exactly at the name and value
     positions, and 0 everywhere else.  This ensures that the name and value are the only
     parts of the field that lie inside JSON string bodies.

  Specialised to `Primes.bn254` because `assertIsSubstringFS` uses Poseidon.
  See `skipChecks` note of `parseJWTFieldSharedLogic`.
-/
def parseJWTFieldWithQuotedValue
    {maxKVPairLen maxNameLen maxValueLen : ℕ}
    (h_name  : maxNameLen  ≤ maxKVPairLen)
    (h_value : maxValueLen ≤ maxKVPairLen)
    (field              : FString bn254 maxKVPairLen)
    (name               : FString bn254 maxNameLen)
    (value              : FString bn254 maxValueLen)
    (field_string_bodies : Vector (FB bn254) maxKVPairLen)
    (colon_index        : F bn254)
    (value_index        : F bn254)
    (skipChecks         : FB bn254 := 0)
    : Option Unit := do
  -- Delegate shared structural checks
  parseJWTFieldSharedLogic h_name h_value field name value colon_index value_index skipChecks
  let perform : FB bn254 := FB.not skipChecks
  -- Check 0: field[value_index - 1] == '"' (opening quote around value)
  let valueFirstQuote ← selectArrayValue field.data (value_index - 1)
  F.guardedAssertEq perform valueFirstQuote 34
  -- Check 1: field[value_index + value_len] == '"' (closing quote around value)
  let valueSecondQuote ← selectArrayValue field.data (value_index + value.len)
  F.guardedAssertEq perform valueSecondQuote 34
  -- Check 2: whitespace zones + string bodies
  -- Zone A: [name_len + 2, colon_index)  — between closing name-quote and colon
  -- Zone B: [colon_index + 1, value_index - 1)  — between colon and opening value-quote
  -- Zone C: [value_index + value_len + 1, field_len - 1)  — after closing value-quote, before terminator
  let zoneA ← arraySelectorComplex maxKVPairLen (name.len + 2) colon_index
  let zoneB ← arraySelectorComplex maxKVPairLen (colon_index + 1) (value_index - 1)
  let zoneC ← arraySelectorComplex maxKVPairLen (value_index + value.len + 1) (field.len - 1)
  let inZone := (zoneA.zipWith FB.or zoneB).zipWith FB.or zoneC
  -- Name selector: [1, name_len + 1) — name content inside its quotes
  let nameSel ← arraySelector maxKVPairLen 1 (name.len + 1)
  -- Value selector: [value_index, value_index + value_len) — value content inside its quotes
  let valueSel ← arraySelector maxKVPairLen value_index (value_index + value.len)
  let nameOrValue := nameSel.zipWith FB.or valueSel
  -- For each position: whitespace zone chars must be whitespace,
  -- and string bodies must match name/value selectors exactly
  (inZone.zip (nameOrValue.zip (field_string_bodies.zip field.data))).toList.forM fun (z, nv, sb, c) ↦ do
    -- Whitespace check: if in a whitespace zone, the character must be whitespace
    let ws ← F8.isWhitespace c
    F.guardedEq0 perform (z &&& FB.not ws)
    -- String bodies forward: name/value positions must be inside string bodies
    F.guardedEq0 perform (nv &&& FB.not sb)
    -- String bodies reverse: non-name/value positions must NOT be inside string bodies
    F.guardedEq0 perform (FB.not nv &&& sb)

open Primes HashToField FString FArray in
/--
  Asserts structural correctness of the `email_verified` JWT field, which may have
  its value either quoted (`"true"`) or unquoted (`true`).

  Wraps `parseJWTFieldSharedLogic` with additional checks:

  1. **Char before value**: must be `"` (quote), whitespace, or the colon itself
     (i.e. `value_index - 1 == colon_index`).

  2. **Char after value**: must be `"` (quote), whitespace, or the field delimiter
     (i.e. `value_index + value_len == field_len - 1`).

  3. **No mismatched quotes**: it is not the case that one side has a quote and
     the other has whitespace (both quoted or both unquoted).

  4. **Whitespace zones**: every character in the three gaps
     - `[name_len + 2, colon_index)` (between closing name-quote and colon)
     - `[colon_index + 1, value_index - 1)` (between colon and char before value)
     - `[value_index + value_len + 1, field_len - 1)` (after char after value, before terminator)
     must be a whitespace character.

  Specialised to `Primes.bn254` because `assertIsSubstringFS` uses Poseidon.
-/
def parseEmailVerifiedField
    {maxKVPairLen maxNameLen maxValueLen : ℕ}
    (h_name  : maxNameLen  ≤ maxKVPairLen)
    (h_value : maxValueLen ≤ maxKVPairLen)
    (field      : FString bn254 maxKVPairLen)
    (name       : FString bn254 maxNameLen)
    (value      : FString bn254 maxValueLen)
    (colonIndex : F bn254)
    (valueIndex : F bn254)
    : Option Unit := do
  -- Delegate shared structural checks
  parseJWTFieldSharedLogic h_name h_value field name value colonIndex valueIndex
  -- Char before value
  let charBeforeValue ← selectArrayValue field.data (valueIndex - 1)
  let beforeIsQuote      : FB bn254 ← F.eq charBeforeValue '\"'
  let beforeIsWhitespace : FB bn254 ← F8.isWhitespace charBeforeValue
  let beforeIsWsOrQuote := FB.or beforeIsQuote beforeIsWhitespace
  -- Check: char before value is quote/whitespace, OR it is the colon (valueIndex - 1 == colonIndex)
  eq0 ((1 - beforeIsWsOrQuote) &&& (valueIndex - 1 - colonIndex))
  -- Char after value
  let charAfterValue ← selectArrayValue field.data (valueIndex + value.len)
  let afterIsQuote      : FB bn254 ← F.eq charAfterValue '\"'
  let afterIsWhitespace : FB bn254 ← F8.isWhitespace charAfterValue
  let afterIsWsOrQuote := FB.or afterIsQuote afterIsWhitespace
  -- Check: char after value is quote/whitespace, OR it is the field delimiter (fieldLen - 1 == valueIndex + valueLen)
  eq0 ((1 - afterIsWsOrQuote) &&& (field.len - 1 - valueIndex - value.len))
  -- No mismatched quotes: ¬(before=quote ∧ after=whitespace) ∧ ¬(before=whitespace ∧ after=quote)
  let mismatch1 := beforeIsQuote &&& afterIsWhitespace
  let mismatch2 := beforeIsWhitespace &&& afterIsQuote
  eq0 (mismatch1 + mismatch2)
  -- Whitespace zones
  -- Zone A: [nameLen + 2, colonIndex)  — between closing name-quote and colon
  -- Zone B: [colonIndex + 1, valueIndex - 1)  — between colon and char before value (could be quote)
  -- Zone C: [valueIndex + valueLen + 1, fieldLen - 1)  — after char after value, before terminator
  let zoneA ← arraySelectorComplex maxKVPairLen (name.len + 2) colonIndex
  let zoneB ← arraySelectorComplex maxKVPairLen (colonIndex + 1) (valueIndex - 1)
  let zoneC ← arraySelectorComplex maxKVPairLen (valueIndex + value.len + 1) (field.len - 1)
  let inZone := (zoneA.zipWith FB.or zoneB).zipWith FB.or zoneC
  -- For each position in a whitespace zone, the character must be whitespace
  (inZone.zip field.data).toList.forM fun (z, c) ↦ do
    let ws ← F8.isWhitespace c
    eq0 (z &&& FB.not ws)

end JWT

namespace TestJWT

open JWT

open Clap.Lang FString FArray HashToField Primes

abbrev p := Primes.bn254

instance : Coe Char (F p) := charToFp

attribute [local simp] Clap.Spec.Compiler.isZero F.eq FB.not FB.or FB.and

lemma isZero_isSome {a : F p} : (isZero a).isSome := by
  simp [Clap.Spec.Compiler.isZero]
  split <;> trivial

def isZeroPure (a : F p) : F p := (isZero a).get isZero_isSome

lemma isZero_pure : ∀ (a : F p), isZero a = some (isZeroPure a) := by
  simp [Clap.Spec.Compiler.isZero, isZeroPure]

def F.eqPure (a b : F p) : FB p := isZeroPure (a - b)

lemma F.eqPure_pure (a b : F p) : F.eq a b = some (F.eqPure a b) := by
  simp [eqPure, isZeroPure]

def bracketsMap' (input : List (F p)) : List (FB p) := do
  input.map (fun c ↦ F.eqPure c '{' - F.eqPure c '}')

lemma bracketsMap_isSome {l : List (F p)} : (bracketsMap l).isSome := by
  induction l with
  | nil => simp [bracketsMap]
  | cons h t ih =>
    simp [Option.isSome_iff_exists] at ih ⊢
    rcases ih with ⟨a, ih'⟩
    by_cases h₁ : h = '{'
    · subst h₁
      use 1 :: a
      unfold bracketsMap at ih' ⊢
      rw [List.mapM_cons, ih']
      simp
      trivial
    · by_cases h₂ : h = '}'
      · subst h₂
        use (-1) :: a
        unfold bracketsMap at ih' ⊢
        rw [List.mapM_cons, ih']
        simp
        trivial
      · use 0 :: a
        unfold bracketsMap at ih' ⊢
        rw [List.mapM_cons, ih']
        simp at h₁ h₂ ⊢
        split; case _ contra => simp [sub_eq_zero] at contra; contradiction
        simp
        split; case _ contra => simp [sub_eq_zero] at contra; contradiction
        simp

def bracketsMapGet (l : List (F p)) : List (F p) :=
  (bracketsMap l).get bracketsMap_isSome

lemma bracketsMap_pure {l : List (F p)} : bracketsMap' l = bracketsMapGet l := by
  induction l
  case nil => simp [bracketsMap', bracketsMapGet, bracketsMap]
  case cons h t ih =>
    simp [bracketsMap', bracketsMapGet, bracketsMap] at ⊢ ih
    simp [ih]
    by_cases h₁ : h = '{'
    · subst h₁
      simp [F.eqPure, isZeroPure]
      norm_num
    · by_cases h₂ : h = '}'
      · subst h₂
        simp [F.eqPure, isZeroPure]
        norm_num
      · split; case _ contra => simp [sub_eq_zero] at contra; contradiction
        simp [F.eqPure, isZeroPure]
        split; case _ contra => simp [sub_eq_zero] at contra; contradiction
        simp

lemma bracketsMapPure_pure :
  ∀ (l : List (F p)), bracketsMap l = some (bracketsMapGet l)
:= by
  simp [bracketsMapGet]

lemma bracketsMapGet_len (l : List (F p)) :
  (bracketsMapGet l).length = l.length
:= by
  rw [←bracketsMap_pure]
  simp [bracketsMap']

-- `stringBody` theorems and spec proof.

@[simp]
lemma MyStringBody_length' {o e : FB p} {cs : List (FB p)} : (stringBody' o e cs).length = cs.length := by
  revert o e
  induction cs with
  | nil =>
    simp [stringBody']
  | cons l ls ih =>
    simp [stringBody', ih]

@[simp]
lemma MyStringBody_length {cs : List (FB p)} : (stringBody cs).length = cs.length := by
  erw [@MyStringBody_length']


-- ==================== F.eq helpers ====================

-- TODO: should be somewhere

lemma F_eq_get_eq {a b : F p} (h : a = b) : (F.eq a b).get! = (1 : FB p) := by
  subst h; show (isZero (a - a)).get! = 1; simp [sub_self]

lemma F_eq_get_ne {a b : F p} (h : a ≠ b) : (F.eq a b).get! = (0 : FB p) := by
  have h_isZero : Clap.Spec.Compiler.isZero (a - b) = some 0 := by
    simp [Clap.Spec.Compiler.isZero]; exact sub_ne_zero_of_ne h
  show (Clap.Spec.Compiler.isZero (a - b)).get! = 0; rw [h_isZero]; rfl

lemma F_eq_get_01 (a b : F p) : (F.eq a b).get! = 0 ∨ (F.eq a b).get! = 1 := by
  by_cases h : a = b
  · right; exact F_eq_get_eq h
  · left; exact F_eq_get_ne h

/-
==================== Spec function helpers ====================
isQuotation in terms of the character and isEscape at previous position
-/
lemma isQuotation_zero (l : List (F p)) (h : 0 < l.length) :
    isQuotation l ⟨0, h⟩ = decide (l[(⟨0, h⟩ : Fin l.length)] = '"') := by
  grind +locals

lemma isQuotation_succ (l : List (F p)) (n : ℕ) (h : n + 1 < l.length) :
    isQuotation l ⟨n + 1, h⟩ = (decide (l[(⟨n + 1, h⟩ : Fin l.length)] = '"') && ! isEscape l ⟨n, by omega⟩) := by
  simp only [isQuotation, Fin.getElem_fin, ↓Char.isValue, Char.reduceToNat, Nat.cast_ofNat,
    Bool.not_eq_true, Bool.decide_and, Bool.decide_eq_false]
  rfl

@[simp]
lemma isEscape_zero (l : List (F p)) (h : 0 < l.length) :
    isEscape l ⟨0, h⟩ = decide (l[(⟨0, h⟩ : Fin l.length)] = '\\') := by
  simp +decide [ isEscape ]

lemma isEscape_succ (l : List (F p)) (n : ℕ) (h : n + 1 < l.length) :
    isEscape l ⟨n + 1, h⟩ = (decide (l[(⟨n + 1, h⟩ : Fin l.length)] = '\\') && ! isEscape l ⟨n, by omega⟩) := by
  conv =>
      lhs
      unfold isEscape
  simp only [Fin.getElem_fin, ↓Char.isValue, Char.reduceToNat, Nat.cast_ofNat, Bool.not_eq_true,
      Bool.decide_and, Bool.decide_eq_false]
  rfl

/-
oddNrQuotesUntil recurrence
-/
lemma oddNrQuotesUntil_zero (l : List (F p)) (h : 0 < l.length) :
    oddNrQuotesUntil l ⟨0, h⟩ = isQuotation l ⟨0, h⟩ := by
  -- The set {j | j ≤ ⟨0, h⟩ ∧ isQuotation l j} is either {⟨0,h⟩} (if isQuotation l ⟨0,h⟩) or ∅ (otherwise). Its cardinality is either 1 (odd) or 0 (not odd). This matches isQuotation l ⟨0,h⟩.
  have h_set : {j : Fin l.length | j ≤ ⟨0, h⟩ ∧ isQuotation l j} = if isQuotation l ⟨0, h⟩ then {⟨0, h⟩} else ∅ := by
    ext j
    simp [Fin.le_def];
    cases j ; aesop;
  unfold oddNrQuotesUntil; split_ifs at * <;> simp_all +decide [ Set.ext_iff ] ;
  rw [ show ( { x : Fin l.length | x ≤ ⟨ 0, h ⟩ ∧ isQuotation l x = Bool.true } : Finset ( Fin l.length ) ) = ∅ by ext x; aesop ] ; norm_num

lemma oddNrQuotesUntil_succ (l : List (F p)) (n : ℕ) (h : n + 1 < l.length) :
    oddNrQuotesUntil l ⟨n + 1, h⟩ = xor (oddNrQuotesUntil l ⟨n, by omega⟩) (isQuotation l ⟨n + 1, h⟩) := by
  -- By definition of `oddNrQuotesUntil`, we can split the set into two parts: those less than or equal to `n` and those equal to `n + 1`.
  have h_split : {j : Fin l.length | j ≤ ⟨n + 1, h⟩ ∧ isQuotation l j} = {j : Fin l.length | j ≤ ⟨n, by omega⟩ ∧ isQuotation l j} ∪ (if isQuotation l ⟨n + 1, h⟩ then {⟨n + 1, h⟩} else ∅) := by
    ext j
    grind
  split_ifs at h_split <;> simp_all
  · unfold oddNrQuotesUntil; simp [*] ;
    grind;
  · unfold oddNrQuotesUntil; simp [h_split] ;

-- ==================== Bit helpers ====================
def isBit (x : FB p) : Prop := x = 0 ∨ x = 1

lemma escaped_step
    (cs : List (FB p)) (n : ℕ) (hn : n < cs.length)
    (escaped : FB p) (hesc_bit : isBit escaped)
    (hesc : (escaped = 1) ↔ (n > 0 ∧ isEscape cs ⟨n - 1, by omega⟩ = true)) :
    let c := cs[n]
    let escaped' := FB.and (F.eq c '\\').get! (FB.not escaped)
    isBit escaped' ∧
    ((escaped' = 1) ↔ isEscape cs ⟨n, hn⟩ = true) := by
  cases n <;> simp_all [ isEscape_succ ];
  · cases hesc_bit <;> simp_all;
    cases F_eq_get_01 cs[0] 92 <;> simp_all [ isBit ];
    · exact fun h => by simp_all;
    · exact Classical.not_not.1 fun h => by have := F_eq_get_ne h; aesop;
  · cases hesc_bit <;> simp_all [ isBit ];
    grind

lemma nonEscQuotMark_iff_isQuotation
    (cs : List (FB p)) (n : ℕ) (hn : n < cs.length)
    (escaped : FB p) (hesc_bit : isBit escaped)
    (hesc : (escaped = 1) ↔ (n > 0 ∧ isEscape cs ⟨n - 1, by omega⟩ = true)) :
    let c := cs[n]
    let isNonEscQuotationMark := FB.and ((F.eq c '"').get!) (FB.not escaped)
    isBit isNonEscQuotationMark ∧
    ((isNonEscQuotationMark = 1) ↔ isQuotation cs ⟨n, hn⟩ = true) := by
  rcases n <;> simp_all +decide [ isQuotation_succ, isQuotation_zero ]
  · grind +locals
  · cases hesc_bit <;> simp_all +decide [ isBit ]
    cases F_eq_get_01 ( cs[‹_› + 1] ) 34 <;> simp_all
    · exact fun h => by simp_all
    · exact Classical.not_not.1 fun h => by have := F_eq_get_ne h; aesop

lemma openedQuotes_step
    (cs : List (FB p)) (n : ℕ) (hn : n < cs.length)
    (openedQuotes : FB p) (hoq_bit : isBit openedQuotes)
    (hoq : (openedQuotes = 1) ↔ (n > 0 ∧ oddNrQuotesUntil cs ⟨n - 1, by omega⟩ = true))
    (isNonEscQuotationMark : FB p) (hbit_q : isBit isNonEscQuotationMark)
    (hq : (isNonEscQuotationMark = 1) ↔ isQuotation cs ⟨n, hn⟩ = true) :
    let openedQuotes' := FB.xor openedQuotes isNonEscQuotationMark
    isBit openedQuotes' ∧
    ((openedQuotes' = 1) ↔ oddNrQuotesUntil cs ⟨n, hn⟩ = true) := by
  unfold isBit at *;
  rcases n <;> simp_all +decide [ FB.xor ];
  · rw [ oddNrQuotesUntil_zero ];
  · cases hoq_bit <;> cases hbit_q <;> simp_all +decide [ oddNrQuotesUntil_succ ]

lemma output_step
    (cs : List (FB p)) (n : ℕ) (hn : n < cs.length)
    (openedQuotes : FB p) (hoq_bit : isBit openedQuotes)
    (hoq : (openedQuotes = 1) ↔ (n > 0 ∧ oddNrQuotesUntil cs ⟨n - 1, by omega⟩ = true))
    (isNonEscQuotationMark : FB p) (hbit_q : isBit isNonEscQuotationMark)
    (hq : (isNonEscQuotationMark = 1) ↔ isQuotation cs ⟨n, hn⟩ = true) :
    let output := openedQuotes * FB.not isNonEscQuotationMark
    (output = 1 ∧ isInQuotes cs ⟨n, hn⟩ = true) ∨
    (output = 0 ∧ isInQuotes cs ⟨n, hn⟩ = false) := by
  rcases hoq_bit with ( rfl | rfl ) <;> rcases hbit_q with ( rfl | rfl ) <;> simp +decide [ * ];
  · rcases n with ( _ | n ) <;> simp_all +decide [ isInQuotes ];
    · rw [ oddNrQuotesUntil_zero ] ; aesop;
    · rw [ oddNrQuotesUntil_succ ] ; aesop;
  · unfold isInQuotes; aesop;
  · unfold isInQuotes; simp +decide [ hq ] ;
    rcases n with ( _ | n ) <;> simp +decide at *;
    exact ⟨ hq, by rw [ oddNrQuotesUntil_succ ] ; aesop ⟩;
  · unfold isInQuotes; aesop;

lemma myStringBody'_aux
    (cs : List (FB p)) (n : ℕ) (cs₁ : List (FB p))
    (hcs₁ : cs₁ = cs.drop n) (hpos : 0 < cs.length) (hn : n ≤ cs.length)
    (openedQuotes escaped : FB p)
    (hoq_bit : isBit openedQuotes) (hesc_bit : isBit escaped)
    (hoq : (openedQuotes = 1) ↔ (n > 0 ∧ oddNrQuotesUntil cs ⟨n - 1, by omega⟩ = true))
    (hesc : (escaped = 1) ↔ (n > 0 ∧ isEscape cs ⟨n - 1, by omega⟩ = true)) :
    ∀ i : Fin cs₁.length,
      ((stringBody' openedQuotes escaped cs₁)[i] = 1 ∧
        isInQuotes cs ⟨n + i.1, by have := i.2; subst hcs₁; simp at this; omega⟩ = true) ∨
      ((stringBody' openedQuotes escaped cs₁)[i] = 0 ∧
        isInQuotes cs ⟨n + i.1, by have := i.2; subst hcs₁; simp at this; omega⟩ = false) := by
  -- We proceed by induction on `cs₁`.
  induction' cs₁ with c cs₁ ih generalizing n cs openedQuotes escaped;
  · grind;
  · rintro ⟨i, hi⟩
    have n_lt_cs_len : n < cs.length := by
      apply List.length_lt_of_drop_ne_nil
      simp [←hcs₁]
    have c_eq_cs_n : c = cs[(⟨n, n_lt_cs_len⟩ : Fin cs.length)] := by
      have := hcs₁.symm ▸ List.take_append_drop n cs
      rw! [←this]
      simp [n_lt_cs_len, min_eq_left_of_lt]
    rcases i with ( _ | i ) <;> simp [ stringBody' ] at hi ⊢;
    · have : (if c - 34 = 0 then some 1 else some 0).get! * (1 - escaped) = 1 ↔ isQuotation cs ⟨n, by grind⟩ = true := by
        unfold isQuotation
        simp [←c_eq_cs_n]
        split
        · simp
          have : c = 34 := by grind
          split <;> simp at hesc <;> simp [this]
          · simpa [isBit, hesc] using hesc_bit
          · rcases hesc_bit with h | h <;> grind
        · grind
      have h := @output_step cs n (by grind) openedQuotes hoq_bit hoq ((if c - 34 = 0 then some 1 else some 0).get! * (1 - escaped)) (by grind +locals) this
      simp only [FB.not, mul_eq_zero] at h
      exact h
    · convert ih cs ( n + 1 ) _ _ _ _ _ _ _ _ _ ⟨ i, hi ⟩ using 1;
      congr! 1;
      all_goals norm_num [ add_comm, add_left_comm, add_assoc ];
      grind +suggestions;
      exact hpos;
      exact lt_of_le_of_ne hn ( by rintro rfl; simp_all +decide );
      · have := nonEscQuotMark_iff_isQuotation cs n ( by
          grind ) escaped hesc_bit hesc
        generalize_proofs at *;
        have := openedQuotes_step cs n ( by
          linarith ) openedQuotes hoq_bit hoq ( ( F.eq cs[n] 34 ).get!.and escaped.not ) this.1 this.2
        generalize_proofs at *;
        replace hcs₁ := congr_arg List.head? hcs₁ ; aesop ( simp_config := { singlePass := true } ) ;
      · rcases hesc_bit with h | h <;> rw [h] <;> split <;> simp [isBit]
      · convert ( openedQuotes_step cs n ( by
          grind ) openedQuotes hoq_bit hoq ( ( F.eq c 34 ).get!.and escaped.not ) ( by
          grind +suggestions ) ( by
          convert nonEscQuotMark_iff_isQuotation cs n ( by
            grind ) escaped hesc_bit hesc |>.2 using 1
          generalize_proofs at *;
          replace hcs₁ := congr_arg List.head? hcs₁ ;
          aesop ( simp_config := { singlePass := true } ) ; ) ) |>.2 using 1;
        split <;> simp [FB.xor] <;> grind
      · convert escaped_step cs n ( by
          grind ) escaped hesc_bit hesc |>.2 using 1
        generalize_proofs at *;
        replace hcs₁ := congr_arg List.head? hcs₁ ; aesop ( simp_config := { singlePass := true } ) ;

lemma myStringBody'_spec (cs cs₀ cs₁: List (FB p)) (h : cs = cs₀ ++ cs₁) :
  ∀ i : Fin cs₁.length,
    let openedQuotes : FB p :=
      if h' : cs₀.length ≠ 0
      then if oddNrQuotesUntil cs ⟨cs₀.length - 1, by grind⟩ then 1 else 0
      else 0
    let escaped : FB p :=
      if h' : cs₀.length ≠ 0
      then if isEscape cs ⟨cs₀.length - 1, by grind⟩ then 1 else 0
      else 0
    (
      (stringBody' openedQuotes escaped cs₁)[i] = 1 ∧
      isInQuotes cs ⟨cs₀.length + i.1, by simp [h]⟩
    ) ∨
    (
      (stringBody' openedQuotes escaped cs₁)[i] = 0 ∧
      ¬ isInQuotes cs ⟨cs₀.length + i.1, by simp [h]⟩
    ) := by
  by_cases hcs₀ : cs₀.length = 0 <;> simp_all;
  · rcases cs₁ <;> simp_all +decide [ Fin.forall_fin_succ ];
    have := myStringBody'_aux ( ‹_› :: ‹_› ) 0 ( ‹_› :: ‹_› ) rfl ( by simp +decide ) ( by simp +decide ) 0 0 ; simp_all +decide [ Fin.forall_fin_succ ] ;
    simp_all +decide [ isBit ];
    exact this.1 |> fun h => by aesop;
  · convert myStringBody'_aux cs ( List.length cs₀ ) cs₁ _ _ _ _ _ _ _ _ _ using 1;
    all_goals norm_num [ h, List.length_append, List.drop_append ];
    · exact Or.inl ( List.length_pos_iff.mpr hcs₀ );
    · split_ifs <;> simp +decide [ isBit ];
    · split_ifs <;> simp +decide [ isBit ];
    · exact fun _ => List.length_pos_iff.mpr hcs₀;
    · exact fun _ => Nat.pos_of_ne_zero ‹_›

lemma myStringBody_spec (cs : List (FB p)) :
  ∀ i : Fin cs.length,
    (
      (stringBody cs)[i] = 1 ∧
      isInQuotes cs i
    ) ∨
    (
      (stringBody cs)[i] = 0 ∧
      ¬ isInQuotes cs i
    ) := by
  simpa using myStringBody'_spec cs [] cs (List.nil_append _)

example {l : List (F p)} :
  ∀ i : Fin l.length,
    l[i] = '{' ↔ (bracketsMapGet l)[i]'(by simp [bracketsMapGet_len]) = 1
:= by
  intro i
  conv => right; left; arg 1; rw [←bracketsMap_pure]
  simp [bracketsMap', F.eqPure, isZeroPure]
  constructor <;> intro h
  · simp [h]
    trivial
  · grind

example {l : List (F p)} :
  ∀ i : Fin l.length,
    l[i] = '}' ↔ (bracketsMapGet l)[i]'(by simp [bracketsMapGet_len]) = -1
:= by
  intro i
  conv => right; left; arg 1; rw [←bracketsMap_pure]
  simp [bracketsMap', F.eqPure, isZeroPure]
  constructor <;> intro h
  · simp [h]
    trivial
  · grind

example {l : List (F p)} :
  ∀ i : Fin l.length,
    (∃ val : F p, l[i] = val ∧ val ≠ '{' ∧ val ≠ '}')
      ↔ (bracketsMapGet l)[i]'(by simp [bracketsMapGet_len]) = 0
:= by
  intro i
  conv => right; left; arg 1; rw [←bracketsMap_pure]
  simp [bracketsMap', F.eqPure, isZeroPure]
  constructor
  · grind
  · intro h_zero
    constructor <;>
      intro <;>
      simp_all <;>
      split at h_zero <;>
      simp_all [Option.get] <;>
      contradiction

-- def bracketsMapGet (l : List (F p)) : List (F p) :=
--   (bracketsMap l).get bracketsMap_isSome


lemma F.eqPure_iff : ∀ (a b : F p), F.eqPure a b ≠ 0 ↔ a = b := by
  intro a b
  simp [F.eqPure, isZeroPure, sub_eq_zero]
  grind

def FList.eqPure : List (F p) → List (F p) → FB p
| x :: xs, y :: ys => F.eqPure x y * FList.eqPure xs ys
| [], [] => 1
| _, _ => 0

lemma FList.eq_pure (a b : List (F p)) : FList.eq a b = some (FList.eqPure a b) := by
  revert b
  induction a with
  | nil =>
    intro b
    unfold FList.eq eqPure
    simp
    split <;> try trivial
    split <;> trivial
  | cons h₁ t₁ ih =>
    intro b
    unfold FList.eq eqPure
    rcases b with (_ | ⟨h₂, t₂⟩)
    · trivial
    · split <;> try trivial
      case h_1 _ _ _ eq₁ eq₂ =>
        cases eq₁; cases eq₂
        rw [F.eqPure_pure, ih]
        simp
      case _ contra _ =>
        specialize contra h₁ t₁ h₂ t₂ rfl rfl
        contradiction

example {a b : List (F p)} : a = b ↔ FList.eqPure a b ≠ 0 := by
  constructor
  · intro a_eq_b
    subst a_eq_b
    induction a with
    | nil => simp [FList.eqPure]
    | cons _ _ ih => simp [FList.eqPure, F.eqPure, ih, isZeroPure]
  · revert b
    induction a with
    | nil =>
      intro b h
      unfold FList.eqPure at h
      grind
    | cons x xs ih =>
      intro b h
      rcases b with (_ | ⟨y, ys⟩)
      · simp [FList.eqPure] at h
      · simp [FList.eqPure] at h
        have h_ne_zero : F.eqPure x y * FList.eqPure xs ys ≠ 0 := by simp [h]
        rw [mul_ne_zero_iff] at h_ne_zero
        rcases h_ne_zero with ⟨x_ne_y, xs_ne_ys⟩
        simp
        constructor
        · exact (F.eqPure_iff x y).1 x_ne_y
        · exact ih xs_ne_ys

lemma FList.eqPure_reflexive : ∀ l : List (F p), FList.eqPure l l = 1 := by
  intro l
  induction l with
  | nil => simp [FList.eqPure]
  | cons h t ih =>
    simp [FList.eqPure, F.eqPure, ih, isZeroPure]

lemma FList.neq : ∀ l₁ l₂ : List (F p), l₁ ≠ l₂ → FList.eqPure l₁ l₂ = 0 := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ neq
    cases l₂ <;> trivial
  | cons h t ih =>
    intro l₂ neq
    unfold FList.eqPure
    rcases l₂ with (_ | ⟨h', t'⟩)
    · simp
    · simp
      simp at neq
      by_cases heq : h = h'
      · right; exact ih t' (neq heq)
      · left; simp [F.eqPure, isZeroPure, sub_eq_zero, *]

lemma FList.eqPure_iff {a b : List (F p)} : a = b ↔ FList.eqPure a b ≠ 0 := by
  constructor
  · rintro rfl
    simp [FList.eqPure_reflexive a]
  · by_cases a_eq_b : a = b
    · intro _; exact a_eq_b
    · simp [FList.neq a b a_eq_b]

def emailVerifiedCheck'
  (uidName : List (F p))
  (evName : List (F p))
  (evValue : List (F p))
  : Option (FB p)
:= do
  let uidIsEmail := FList.eqPure uidName email
  conditionallyAssert uidIsEmail (FList.eqPure evName requiredEvName)
  let c : FB p :=
    FB.or
      (FList.eqPure evValue requiredEvValLen4)
      (FList.eqPure evValue requiredEvValLen6)
  conditionallyAssert uidIsEmail c
  return uidIsEmail
 where
  conditionallyAssert (antecedent consequent : FB p) : Option Unit :=
    -- a → c ≡ ¬(a ∧ ¬c)
    eq0 (antecedent * FB.not consequent)

lemma emailVerifiedCheck_eq {uidName evName evValue : List (F p)} :
  emailVerifiedCheck uidName evName evValue =
    emailVerifiedCheck' uidName evName evValue
:= by
    simp
      [ emailVerifiedCheck,
        emailVerifiedCheck.conditionallyAssert,
        Clap.Spec.Compiler.eq0,
        HOr.hOr
      ]
    simp [FList.eq_pure]
    unfold emailVerifiedCheck' emailVerifiedCheck'.conditionallyAssert
    simp [Clap.Spec.Compiler.eq0]

example {uidName evName evValue : List (F p)} :
  uidName = email →
  evName = requiredEvName →
  evValue = requiredEvValLen4 ∨ evValue = requiredEvValLen6 →
  emailVerifiedCheck uidName evName evValue = .some 1
:= by
  rw [emailVerifiedCheck_eq]
  rintro rfl rfl (rfl | rfl) <;>
    simp
      [ emailVerifiedCheck',
        emailVerifiedCheck'.conditionallyAssert,
        FList.eqPure_reflexive,
        FB.not,
        Clap.Spec.Compiler.eq0,
      ]

example {uidName evName evValue : List (F p)} :
  uidName ≠ email →
  emailVerifiedCheck uidName evName evValue = .some 0
:= by
  rw [emailVerifiedCheck_eq]
  intro neq
  simp
    [ emailVerifiedCheck',
      emailVerifiedCheck'.conditionallyAssert,
      Clap.Spec.Compiler.eq0,
    ]
  rw [FList.neq _ _ neq]
  simp

example {uidName evName evValue : List (F p)} :
  uidName = email →
  evName ≠ requiredEvName →
  emailVerifiedCheck uidName evName evValue = .none
:= by
  rw [emailVerifiedCheck_eq]
  rintro rfl neq
  simp
    [ emailVerifiedCheck',
      emailVerifiedCheck'.conditionallyAssert,
      FList.eqPure_reflexive,
      Clap.Spec.Compiler.eq0,
    ]
  intro contra
  rw [FList.neq _ _ neq] at contra
  contradiction

example {uidName evName evValue : List (F p)} :
  uidName = email →
  evValue ≠ requiredEvValLen4 ∧ evValue ≠ requiredEvValLen6 →
  emailVerifiedCheck uidName evName evValue = .none
:= by
  rw [emailVerifiedCheck_eq]
  rintro rfl ⟨ne₁, ne₂⟩
  simp
    [ emailVerifiedCheck',
      emailVerifiedCheck'.conditionallyAssert,
      Clap.Spec.Compiler.eq0,
      FList.eqPure_reflexive,
      FB.not
    ]
  rw [FList.neq _ _ ne₁, FList.neq _ _ ne₂]
  intro _ _
  contradiction

private def parseCharsASCII (s : String) : List (F p) :=
  s.chars.map (fun n ↦ (n.toNat : ZMod p)) |>.toList
private def parseBitString (s : String) : List (FB p) :=
  s.chars.filter (fun c ↦ c != ' ') |>.map (fun c ↦ if c = '0' then 0 else 1) |>.toList

/- from the Circom docstring
  { asdfsdf "as\"df" }
  00000000000111111000 -/
example :
  let inp      := parseCharsASCII "{ asdfsdf \"as\\\"df\" }"
  let expected := parseBitString  "0000000000 011 1 111 000"
  stringBody (p := p) inp == expected := by native_decide

/-
  { a "a\"a" } →
  000001111000
-/
example :
  let inp      := parseCharsASCII "{ a \"a\\\"a\" }"
  let expected := parseBitString  "0000 01 1 11 000"
  stringBody (p := p) inp == expected := by native_decide

/-
  "i\i""i" →
  01110010
-/
example :
  let inp      := parseCharsASCII "\"i\\i\"\"i\""
  let expected := parseBitString  " 01 11 0 01 0"
  stringBody (p := p) inp == expected := by native_decide

/-
  "i\"\\\"i" →
  0111111110
-/
example :
  let inp      := parseCharsASCII "\"i\\\"\\\\\\\"i\""
  let expected := parseBitString  " 01 1 1 1 1 1 11 0"
  stringBody (p := p) inp == expected := by native_decide

/-
  """""" →
  000000
-/
example :
  let inp      := parseCharsASCII "\"\"\"\"\"\""
  let expected := parseBitString  " 0 0 0 0 0 0"
  stringBody (p := p) inp == expected := by native_decide

/-
  \"\""i"\"\" →
  00000100000
-/
example :
  let inp      := parseCharsASCII "\\\"\\\"\"i\"\\\"\\\""
  let expected := parseBitString  " 0 0 0 0 01 0 0 0 0 0"
  stringBody (p := p) inp == expected := by native_decide

/-
  \\"\\" →
  000110
-/
example :
  let inp      := parseCharsASCII "\\\\\"\\\\\""
  let expected := parseBitString  " 0 0 0 1 1 0"
  stringBody (p := p) inp == expected := by native_decide

private def br :=
  parseCharsASCII "{he{llo{}world!}}"
example :
  bracketsMap (p := p) br == some [1, 0, 0, 1, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, -1, -1]
:= by
  native_decide

private def plusMinusOneBr₁ : List (F p) :=
  [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, -1]
example :
  bracketsDepthMap plusMinusOneBr₁ == some
    [0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0]
:= by
  native_decide

private def plusMinusOneBr₂ : List (F p) :=
  [1,1,1,1,1,-1,-1,-1,-1,-1]

example : bracketsDepthMap plusMinusOneBr₂ == some [0, 0, 1, 2, 3, 3, 2, 1, 0, 0] := by
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
  emailVerifiedCheck (p := p) email requiredEvName requiredEvValLen4  == .some 1
:= by
  native_decide

example : -- uid is «email»; «email_verified» is «"true"»
  emailVerifiedCheck (p := p) email requiredEvName requiredEvValLen6 == .some 1
:= by
  native_decide

example : -- uid is «email», but there is no «email_verified»
  emailVerifiedCheck (p := p) email [1,2,3] requiredEvValLen6 == .none
:= by
  native_decide

example : -- uid is «email», but «email_verified» is neither «true» nor «"true"»
  emailVerifiedCheck (p := p) email requiredEvName [4, 5, 6] == .none
:= by
  native_decide

example : -- uid is not «email»
  emailVerifiedCheck (p := p) [] requiredEvName requiredEvValLen6 == .some 0
:= by native_decide

example : -- uid is not «email», the rest doesn't matter
  emailVerifiedCheck (p := p) [] [1, 2, 3] [4, 5, 6] == .some 0
:= by native_decide

-- parseJWTFieldSharedLogic tests

/-- Build an `FString p maxLen` from a Lean `String`, zero-padding to `maxLen`. -/
private def strToFS (maxLen : ℕ) (s : String) (h : s.length ≤ maxLen := by decide) : FString p maxLen :=
  let ascii := s.toList.map (fun c ↦ (c.toNat:F p))
  let padded := ascii ++ List.replicate (maxLen - ascii.length) 0
  ⟨⟨padded.toArray, by simp [padded, ascii, String.length_toList]; omega⟩, (s.length : ZMod p)⟩

-- valid field "a":b,  (name="a", value="b", ending with ',')
example : (do
  let field := strToFS 6 "\"a\":b,"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 3 4
  ) = some () := by native_decide

-- valid field "a":b}  (ending with '}')
example : (do
  let field := strToFS 6 "\"a\":b}"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 3 4
  ) = some () := by native_decide

-- valid field with longer name "sub":12,
example : (do
  let field := strToFS 9 "\"sub\":12,"
  let name  := strToFS 3 "sub"
  let value := strToFS 2 "12"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 5 6
  ) = some () := by native_decide

-- valid field with whitespace-padded value "alg": RS256 (whitespace before R),
example : (do
  let field := strToFS 14 "\"alg\": RS256,"
  let name  := strToFS 4 "alg"
  let value := strToFS 7 " RS256" -- _RS256
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 5 6
  ) = some () := by native_decide

-- valid field with value_index gap "email":"ab@c",
example : (do
  let field := strToFS 16 "\"email\":\"ab@c\","
  let name  := strToFS 6 "email"
  let value := strToFS 5 "ab@c"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 7 9
  ) = some () := by native_decide

-- valid field ending with '}' and multi-char name/value "iat":9876}
example : (do
  let field := strToFS 11 "\"iat\":9876}"
  let name  := strToFS 4 "iat"
  let value := strToFS 5 "9876"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 5 6
  ) = some () := by native_decide

-- fail — first char is not '"' (starts with 'a' instead)
example : (do
  let field := strToFS 6 "aa\":b,"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 3 4
  ) = none := by native_decide

-- fail — closing quote missing (field[name_len+1] is 'a' not '"')
example : (do
  let field := strToFS 6 "\"aa:b,"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 3 4
  ) = none := by native_decide

-- fail — colon_index position doesn't hold ':'  (position 3 is 'b')
example : (do
  let field := strToFS 6 "\"a\"bb,"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 3 4
  ) = none := by native_decide

-- fail — last char is neither ',' nor '}'
example : (do
  let field := strToFS 6 "\"a\":ba"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 3 4
  ) = none := by native_decide

-- fail — name_len not less than colon_index (colon_index=1, name_len=1 → not <)
example : (do
  let field := strToFS 6 "\"a\":b,"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 1 4
  ) = none := by native_decide

-- fail — colon_index not less than value_index (both = 3)
example : (do
  let field := strToFS 6 "\"a\":b,"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 3 3
  ) = none := by native_decide

-- fail — name substring mismatch (name='b' but field has 'a' at position 1)
example : (do
  let field := strToFS 6 "\"a\":b,"
  let name  := strToFS 1 "b"   -- 'b' doesn't match 'a' at index 1
  let value := strToFS 1 "b"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 3 4
  ) = none := by native_decide

-- skipChecks = 1 bypasses semantic checks (name mismatch) but sub-template constraints
-- (one-hot encoding, byte validation) still apply. Well-formed inputs succeed.
example : (do
  let field := strToFS 6 "\"a\":b,"
  let name  := strToFS 1 "b"   -- 'b' doesn't match 'a' at index 1
  let value := strToFS 1 "b"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 3 4 (skipChecks := 1)
  ) = some () := by native_decide

-- parseJWTFieldSharedLogic accepts inputs that the wrapper templates
-- (ParseJWTFieldWithUnquotedValue / ParseJWTFieldWithQuotedValue) would reject.

-- Security problem 1: non-whitespace garbage between closing name quote and colon.
-- "a"X:b,  — 'X' (ASCII 88) sits between the name and colon.
-- SharedLogic only checks field[colon_index]==':' but never verifies that positions
-- (name_len+2 .. colon_index-1) are whitespace.
example : (do
  let field := strToFS 7 "\"a\"X:b,"  -- position 3 is 'X', colon at 4
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 4 5
  ) = some () := by native_decide

-- "Exploit" 1 — Real JWT field: "role":user.
-- Garbage injection between closing name-quote and colon to smuggle a fake value.
-- The field bytes are "role"XXX:true, where XXX is arbitrary. All spot-checks pass.
-- A conforming JSON parser would reject "role"XXX:true, but the circuit
-- produces a valid proof that name = "role" maps to value = "true".
example : (do
  let field := strToFS 14 "\"role\"XX:true,"
  let name  := strToFS 5 "role"
  let value := strToFS 4 "true"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 8 9
  ) = some () := by native_decide

-- Security problem 2: unquoted value containing a delimiter (comma).
-- "a":b,,  — the value substring is "b," which embeds a comma.
-- SharedLogic only asserts the value is a substring at value_index and that the
-- last character is ',' or '}'; it never checks that the value itself is free of delimiters (',', '}', '"').
example : (do
  let field := strToFS 7 "\"a\":b,,"  -- value "b," at index 4, last char ','
  let name  := strToFS 1 "a"
  let value := strToFS 2 "b,"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 3 4
  ) = some () := by native_decide

-- "Exploit" 2 — Real JWT fragment: "iat":1,"admin":true}.
-- Sets value="1,\"admin\":true" spanning across the actual field boundary, and asks the circuit to verify name="iat".
-- SharedLogic accepts because the value is indeed a substring at value_index, field_len >  name_len + value_len,
-- and the last char is '}'. We can now present a proof that the JWT contains "iat" with a value that swallowed
-- the adjacent "admin":true field — proving the admin claim exists without it being separately validated.
example : (do
  let field := strToFS 24 "\"iat\":1,\"admin\":true}"
  let name  := strToFS 4 "iat"
  let value := strToFS 16 "1,\"admin\":true"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 5 6
  ) = some () := by native_decide

-- Exploit 3 — Value truncation Real JWT field: "exp":1999999999
-- Sets value="1" (just the first digit) and lets the remaining digits "999999999" fall into the unchecked gap before the comma.
-- SharedLogic accepts: value is a valid substring at value_index, and the last char is ','. We can prove exp = 1
-- instead of the real exp=1999999999
example : (do
  let field := strToFS 18 "\"exp\":1999999999,"
  let name  := strToFS 4 "exp"
  let value := strToFS 2 "1"            -- truncated from "1999999999"
  parseJWTFieldSharedLogic (by omega) (by omega) field name value 5 6
  ) = some () := by native_decide

-- parseJWTFieldWithUnquotedValue tests

-- valid: "a":b,   (minimal: single-char name and value, no whitespace gaps)
example : (do
  let field := strToFS 6 "\"a\":b,"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithUnquotedValue (by omega) (by omega) field name value 3 4
  ) = some () := by native_decide

-- valid: "a":b}   (ending with '}')
example : (do
  let field := strToFS 6 "\"a\":b}"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithUnquotedValue (by omega) (by omega) field name value 3 4
  ) = some () := by native_decide

-- valid: "sub":123,  (multi-char name and numeric value)
example : (do
  let field := strToFS 10 "\"sub\":123,"
  let name  := strToFS 3 "sub"
  let value := strToFS 3 "123"
  parseJWTFieldWithUnquotedValue (by omega) (by omega) field name value 5 6
  ) = some () := by native_decide

-- valid: "alg": RS256,  (single space between colon and value)
example : (do
  let field := strToFS 13 "\"alg\": RS256,"
  let name  := strToFS 3 "alg"
  let value := strToFS 5 "RS256"
  parseJWTFieldWithUnquotedValue (by omega) (by omega) field name value 5 7
  ) = some () := by native_decide

-- valid: "iat":9876}  (numeric value, ending with '}')
example : (do
  let field := strToFS 11 "\"iat\":9876}"
  let name  := strToFS 3 "iat"
  let value := strToFS 4 "9876"
  parseJWTFieldWithUnquotedValue (by omega) (by omega) field name value 5 6
  ) = some () := by native_decide

-- valid: "role": true ,  (spaces on both sides of value)
example : (do
  let field := strToFS 14 "\"role\": true ,"
  let name  := strToFS 4 "role"
  let value := strToFS 4 "true"
  parseJWTFieldWithUnquotedValue (by omega) (by omega) field name value 6 8
  ) = some () := by native_decide

-- Reject: single non-whitespace byte 'X' between name-quote and colon.
-- "a"X:b,  — position 3 is 'X' (ASCII 88), colon at 4.
example : (do
  let field := strToFS 7 "\"a\"X:b,"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithUnquotedValue (by omega) (by omega) field name value 4 5
  ) = none := by native_decide

-- Reject: Exploit 1 — "role"XX:true,
-- Mirrors the SharedLogic Exploit 1 example above.
-- Two garbage bytes between name-quote and colon; SharedLogic accepted this.
example : (do
  let field := strToFS 14 "\"role\"XX:true,"
  let name  := strToFS 4 "role"
  let value := strToFS 4 "true"
  parseJWTFieldWithUnquotedValue (by omega) (by omega) field name value 8 9
  ) = none := by native_decide

-- Reject: value contains ',' — "a":b,,
example : (do
  let field := strToFS 7 "\"a\":b,,"
  let name  := strToFS 1 "a"
  let value := strToFS 2 "b,"
  parseJWTFieldWithUnquotedValue (by omega) (by omega) field name value 3 4
  ) = none := by native_decide

-- Reject: Exploit 2 — "iat":1,"admin":true}
-- Value "1,\"admin\":true" spans the field boundary; contains both ',' and '"'.
example : (do
  let field := strToFS 24 "\"iat\":1,\"admin\":true}"
  let name  := strToFS 3 "iat"
  let value := strToFS 14 "1,\"admin\":true"
  parseJWTFieldWithUnquotedValue (by omega) (by omega) field name value 5 6
  ) = none := by native_decide

-- Reject: value contains '}' — "a":b},
-- A value ending with '}' would be a valid JSON terminator but not a valid unquoted value body.
example : (do
  let field := strToFS 7 "\"a\":b},"
  let name  := strToFS 1 "a"
  let value := strToFS 2 "b}"
  parseJWTFieldWithUnquotedValue (by omega) (by omega) field name value 3 4
  ) = none := by native_decide

-- Reject: value contains '"' — "a":"b",  (quoted value content presented as unquoted)
example : (do
  let field := strToFS 8 "\"a\":\"b\","
  let name  := strToFS 1 "a"
  let value := strToFS 3 "\"b\""
  parseJWTFieldWithUnquotedValue (by omega) (by omega) field name value 3 4
  ) = none := by native_decide

-- Reject: Exploit 3 — "exp":1999999999,
example : (do
  let field := strToFS 18 "\"exp\":1999999999,"
  let name  := strToFS 3 "exp"
  let value := strToFS 1 "1"
  parseJWTFieldWithUnquotedValue (by omega) (by omega) field name value 5 6
  ) = none := by native_decide

example : (do
  let field := strToFS 18 "\"exp\":1999999999,"
  let name  := strToFS 3 "exp"
  let value := strToFS 1 "1"
  parseJWTFieldWithUnquotedValue (by omega) (by omega) field name value 5 6 (skipChecks := 1)
  ) = some () := by native_decide

-- Reject: partial value with trailing non-whitespace — "nbf":16000 ,
-- value="160"; characters "00 " end with a space (whitespace) but "00" are digits, not whitespace.
example : (do
  let field := strToFS 13 "\"nbf\":16000 ,"
  let name  := strToFS 3 "nbf"
  let value := strToFS 3 "160"
  parseJWTFieldWithUnquotedValue (by omega) (by omega) field name value 5 6
  ) = none := by native_decide

example : (do
  let field := strToFS 13 "\"nbf\":16000 ,"
  let name  := strToFS 3 "nbf"
  let value := strToFS 3 "160"
  parseJWTFieldWithUnquotedValue (by omega) (by omega) field name value 5 6 (skipChecks := 1)
  ) = some () := by native_decide

-- skipChecks = 1 does NOT bypass sub-template constraints: out-of-range indices still fail,
-- matching CIRCOM where sub-template constraints (one-hot encoding) always apply.
example : (do
  let field := strToFS 6 "\"a\":b,"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithUnquotedValue (by omega) (by omega) field name value 100 200 (skipChecks := 1)
  ) = none := by native_decide

-- parseJWTFieldWithQuotedValue tests

-- valid: "a":"b",  (minimal quoted value)
-- field = "a":"b",  →  positions: 0=" 1=a 2=" 3=: 4=" 5=b 6=" 7=,
-- string_bodies:                    0   1   0   0   0   1   0   0
example : (do
  let field := strToFS 8 "\"a\":\"b\","
  let bodies : Vector (ZMod p) 8 := #v[0,1,0,0,0,1,0,0]
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 3 5
  ) = some () := by native_decide

-- valid: "a":"b"}  (ending with '}')
example : (do
  let field := strToFS 8 "\"a\":\"b\"}"
  let bodies : Vector (ZMod p) 8 := #v[0,1,0,0,0,1,0,0]
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 3 5
  ) = some () := by native_decide

-- valid: "sub":"abc",  (multi-char name and value)
-- field = "sub":"abc",  →  0=" 1=s 2=u 3=b 4=" 5=: 6=" 7=a 8=b 9=c 10=" 11=,
-- string_bodies:             0   1   1   1   0   0   0   1   1   1    0    0
example : (do
  let field := strToFS 12 "\"sub\":\"abc\","
  let bodies : Vector (ZMod p) 12 := #v[0,1,1,1,0,0,0,1,1,1,0,0]
  let name  := strToFS 3 "sub"
  let value := strToFS 3 "abc"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 5 7
  ) = some () := by native_decide

-- valid: "email":"ab@c",  (value with special char)
-- field = "email":"ab@c",  → 0=" 1=e 2=m 3=a 4=i 5=l 6=" 7=: 8=" 9=a 10=b 11=@ 12=c 13=" 14=, 15=\0
-- string_bodies:               0   1   1   1   1   1   0   0   0   1    1    1    1    0    0    0
example : (do
  let field := strToFS 16 "\"email\":\"ab@c\","
  let bodies : Vector (ZMod p) 16 := #v[0,1,1,1,1,1,0,0,0,1,1,1,1,0,0,0]
  let name  := strToFS 5 "email"
  let value := strToFS 4 "ab@c"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 7 9
  ) = some () := by native_decide

-- valid: "k": "v" ,  (spaces around quoted value and after)
-- field = "k": "v" ,  →  0=" 1=k 2=" 3=: 4=SP 5=" 6=v 7=" 8=SP 9=,
-- string_bodies:          0    1   0   0   0    0   1   0   0    0
example : (do
  let field := strToFS 10 "\"k\": \"v\" ,"
  let bodies : Vector (ZMod p) 10 := #v[0,1,0,0,0,0,1,0,0,0]
  let name  := strToFS 1 "k"
  let value := strToFS 1 "v"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 3 6
  ) = some () := by native_decide

-- valid: "k":"v"}  (ending with '}')
example : (do
  let field := strToFS 8 "\"k\":\"v\"}"
  let bodies : Vector (ZMod p) 8 := #v[0,1,0,0,0,1,0,0]
  let name  := strToFS 1 "k"
  let value := strToFS 1 "v"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 3 5
  ) = some () := by native_decide

-- Reject: opening value quote missing — "a":b",
-- field[value_index - 1] = field[3] = ':' ≠ '"'
example : (do
  let field := strToFS 7 "\"a\":b\","
  let bodies : Vector (ZMod p) 7 := #v[0,1,0,0,1,0,0]
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 3 4
  ) = none := by native_decide

-- Reject: closing value quote missing — "a":"b,
-- field[value_index + value_len] = field[5] = ',' ≠ '"'
example : (do
  let field := strToFS 7 "\"a\":\"b,"
  let bodies : Vector (ZMod p) 7 := #v[0,1,0,0,0,1,0]
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 3 5
  ) = none := by native_decide

-- Reject: non-whitespace between name-quote and colon — "a"X:"b",
-- string_bodies: 0 1 0 0 0 0 1 0 0
example : (do
  let field := strToFS 9 "\"a\"X:\"b\","
  let bodies : Vector (ZMod p) 9 := #v[0,1,0,0,0,0,1,0,0]
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 4 6
  ) = none := by native_decide

-- Reject: non-whitespace between colon and opening value quote — "a":X"b",
-- string_bodies: 0 1 0 0 0 0 1 0 0
example : (do
  let field := strToFS 9 "\"a\":X\"b\","
  let bodies : Vector (ZMod p) 9 := #v[0,1,0,0,0,0,1,0,0]
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 3 6
  ) = none := by native_decide

-- Reject: wrong string bodies — all zeros (should have 1s at name and value positions)
example : (do
  let field := strToFS 8 "\"a\":\"b\","
  let bodies : Vector (ZMod p) 8 := #v[0,0,0,0,0,0,0,0]
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 3 5
  ) = none := by native_decide

-- Reject: wrong string bodies — all ones
example : (do
  let field := strToFS 8 "\"a\":\"b\","
  let bodies : Vector (ZMod p) 8 := #v[1,1,1,1,1,1,1,1]
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 3 5
  ) = none := by native_decide

example : (do
  let field := strToFS 8 "\"a\":\"b\","
  let bodies : Vector (ZMod p) 8 := #v[1,1,1,1,1,1,1,1]
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 3 5 (skipChecks := 1)
  ) = some () := by native_decide

-- Reject: non-whitespace after closing value quote — "a":"b"X,
-- string_bodies: 0 1 0 0 0 1 0 0 0
example : (do
  let field := strToFS 9 "\"a\":\"b\"X,"
  let bodies : Vector (ZMod p) 9 := #v[0,1,0,0,0,1,0,0,0]
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 3 5
  ) = none := by native_decide

example : (do
  let field := strToFS 9 "\"a\":\"b\"X,"
  let bodies : Vector (ZMod p) 9 := #v[0,1,0,0,0,1,0,0,0]
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 3 5 (skipChecks := 1)
  ) = some () := by native_decide

example : (do
  let field := strToFS 9 "\"a\":\"b\"X,"
  let bodies : Vector (ZMod p) 9 := #v[0,1,0,0,0,1,0,0,0]
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 3 5 (skipChecks := 1)
  ) = some () := by native_decide

-- skipChecks = 1 does NOT bypass sub-template constraints: out-of-range indices still fail,
-- matching CIRCOM where sub-template constraints (one-hot encoding) always apply.
example : (do
  let field := strToFS 6 "\"a\":b,"
  let bodies : Vector (ZMod p) 6 := #v[0,0,0,0,0,0]
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 100 200 (skipChecks := 1)
  ) = none := by native_decide

-- valid: "k":"ab cd",  (whitespace inside quoted value)
-- field = "k":"ab cd",  →  0=" 1=k 2=" 3=: 4=" 5=a 6=b 7=SP 8=c 9=d 10=" 11=,
-- string_bodies:            0    1   0   0   0   1   1   1    1   1    0    0
example : (do
  let field := strToFS 12 "\"k\":\"ab cd\","
  let bodies : Vector (ZMod p) 12 := #v[0,1,0,0,0,1,1,1,1,1,0,0]
  let name  := strToFS 1 "k"
  let value := strToFS 5 "ab cd"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 3 5
  ) = some () := by native_decide

-- valid: "k":"a\"b",  (escaped quote inside quoted value)
-- field = "k":"a\"b",  →  0=" 1=k 2=" 3=: 4=" 5=a 6=\" 7=" 8=b 9=" 10=,
-- string_bodies:            0   1   0   0   0   1   1   1   1   0    0
-- The \" at positions 6-7 is an escaped quote, so stringBody stays open through it.
-- value = a\"b (4 chars), value_index=5, value_sel=[5,9)
example : (do
  let field := strToFS 11 "\"k\":\"a\\\"b\","
  let bodies : Vector (ZMod p) 11 := #v[0,1,0,0,0,1,1,1,1,0,0]
  let name  := strToFS 1 "k"
  let value := strToFS 4 "a\\\"b"
  parseJWTFieldWithQuotedValue (by omega) (by omega) field name value bodies 3 5
  ) = some () := by native_decide

-- parseEmailVerifiedField tests

-- valid: "a":b,  (unquoted value, colon immediately before value)
-- field = "a":b,  →  0=" 1=a 2=" 3=: 4=b 5=,
-- value_index=4, colon_index=3, char before value is ':', value_index-1 == colon_index
example : (do
  let field := strToFS 6 "\"a\":b,"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseEmailVerifiedField (by omega) (by omega) field name value 3 4
  ) = some () := by native_decide

-- valid: "a":"b",  (quoted value)
-- field = "a":"b",  →  0=" 1=a 2=" 3=: 4=" 5=b 6=" 7=,
-- value_index=5, colon_index=3, char before value is '"', char after value is '"'
example : (do
  let field := strToFS 8 "\"a\":\"b\","
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseEmailVerifiedField (by omega) (by omega) field name value 3 5
  ) = some () := by native_decide

-- valid: "a":b}  (unquoted value, ending with '}')
example : (do
  let field := strToFS 6 "\"a\":b}"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseEmailVerifiedField (by omega) (by omega) field name value 3 4
  ) = some () := by native_decide

-- valid: "a":"b"}  (quoted value, ending with '}')
example : (do
  let field := strToFS 8 "\"a\":\"b\"}"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseEmailVerifiedField (by omega) (by omega) field name value 3 5
  ) = some () := by native_decide

-- valid: "sub": true ,  (unquoted value with whitespace around it)
-- value_index=7, colon_index=5, char before value is ' ' (whitespace)
-- char after value at index 11 is ' ' (whitespace)
example : (do
  let field := strToFS 14 "\"sub\": true ,"
  let name  := strToFS 3 "sub"
  let value := strToFS 4 "true"
  parseEmailVerifiedField (by omega) (by omega) field name value 5 7
  ) = some () := by native_decide

-- valid: "sub": "true" ,  (quoted value with whitespace around quotes)
-- value_index=8, colon_index=5, char before value is '"', char after value is '"'
example : (do
  let field := strToFS 16 "\"sub\": \"true\" ,"
  let name  := strToFS 3 "sub"
  let value := strToFS 4 "true"
  parseEmailVerifiedField (by omega) (by omega) field name value 5 8
  ) = some () := by native_decide

-- valid: "ev":true,  (multi-char unquoted value, no gaps)
example : (do
  let field := strToFS 10 "\"ev\":true,"
  let name  := strToFS 2 "ev"
  let value := strToFS 4 "true"
  parseEmailVerifiedField (by omega) (by omega) field name value 4 5
  ) = some () := by native_decide

-- Reject: mismatched quotes — quote before, whitespace after — "a":"b ,
-- char before value is '"', char after value is ' ' → mismatched
example : (do
  let field := strToFS 8 "\"a\":\"b ,"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseEmailVerifiedField (by omega) (by omega) field name value 3 5
  ) = none := by native_decide

-- Reject: non-whitespace garbage between name-quote and colon — "a"X:b,
example : (do
  let field := strToFS 7 "\"a\"X:b,"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseEmailVerifiedField (by omega) (by omega) field name value 4 5
  ) = none := by native_decide

-- Reject: non-whitespace between colon and value (not quote/whitespace/colon) — "a":Xb,
-- char before value at index 4 is 'X', which is not quote, not whitespace, and value_index-1 ≠ colon_index
example : (do
  let field := strToFS 7 "\"a\":Xb,"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseEmailVerifiedField (by omega) (by omega) field name value 3 5
  ) = none := by native_decide

end TestJWT
