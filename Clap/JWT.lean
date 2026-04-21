import Clap.Lang
import Clap.Array
import Clap.FString
import Clap.HashToField

namespace JWT

open Clap.Lang Core Primes

variable {p : ℕ} [Core p] [Core bn254]

instance : Coe Char (F p) := charToFp

private def stringBodiesRev₀ (input : List (F p)) : Option (List (FB p) × FB p × FB p) :=
  input.foldlM go ([], default, default)
 where
  go : List (FB p) × FB p × FB p → F p → Option (List (FB p) × FB p × FB p) :=
    fun (acc, openedQuotes, escaped) c ↦ do
      let isNonEscQuotationMark := (←F.eq c '\"') &&& FB.not escaped
      let acc' := openedQuotes * FB.not isNonEscQuotationMark :: acc
      let openedQuotes' := FB.xor openedQuotes isNonEscQuotationMark
      let escaped' := (←F.eq c '\\') &&& FB.not escaped
      some (acc', openedQuotes', escaped')

-- private def stringBodiesRev₀ (input : List (F p)) : List (FB p) × FB p × FB p :=
--   input.foldl go
--     -- ( fun (acc, openedQuotes, escaped) c ↦
--     --     let isNonEscQuotationMark := F.eq c '\"' &&& FB.not escaped
--     --     let acc' := openedQuotes * FB.not isNonEscQuotationMark :: acc
--     --     let openedQuotes' := FB.xor openedQuotes isNonEscQuotationMark
--     --     let escaped' := F.eq c '\\' &&& FB.not escaped
--     --     (acc', openedQuotes', escaped')
--     -- )
--     ([], default, default)
--  where
--   go : List (FB p) × FB p × FB p → F p → List (FB p) × FB p × FB p :=
--     fun (acc, openedQuotes, escaped) c ↦
--       let isNonEscQuotationMark := F.eq c '\"' &&& FB.not escaped
--       let acc' := openedQuotes * FB.not isNonEscQuotationMark :: acc
--       let openedQuotes' := FB.xor openedQuotes isNonEscQuotationMark
--       let escaped' := F.eq c '\\' &&& FB.not escaped
--       (acc', openedQuotes', escaped')

-- private def stringBodiesRev₁ (input : List (F p)) : List (FB p) × FB p × FB p :=
--   input.foldl go
--     ([], default, default)
--  where
--   go : List (FB p) × FB p × FB p → F p → List (FB p) × FB p × FB p :=
--     fun (acc, openedQuotes, escaped) c ↦
--       let isNonEscQuotationMark := F.eq c '\"' &&& FB.not escaped
--       let acc' := acc ++ [openedQuotes * FB.not isNonEscQuotationMark]
--       let openedQuotes' := FB.xor openedQuotes isNonEscQuotationMark
--       let escaped' := F.eq c '\\' &&& FB.not escaped
--       (acc', openedQuotes', escaped')

omit [Core bn254] in
/-- From keyless:
  Given an array of ask characters representing a JSON object, output a binary array demarquing
  the spaces in between quotes, so that the indices in between quotes in `in` are given the value
  `1` in `out`, and are 0 otherwise. Escaped quotes are not considered quotes in this subcircuit
  input =  { asdfsdf "as\"df" }
  output = 00000000000111111000
-/
def stringBodies (input : List (F p)) : Option (List (FB p)) := do
  (←stringBodiesRev₀ input).1.reverse

/-
omit [Core bn254] in
@[simp] theorem stringBodies_length (input : List (F p)) :
    (stringBodies input).length = input.length := by
  simp only [stringBodies, List.length_reverse]
  show (stringBodiesRev₀ input).1.length = input.length
  simp only [stringBodiesRev₀]
  -- Generalize the accumulator
  suffices h : ∀ (s : List (FB p) × FB p × FB p),
      (input.foldl (fun x c ↦
        let isNonEscQuotationMark := F.eq c '\"' &&& FB.not x.2.2
        (x.2.1 * FB.not isNonEscQuotationMark :: x.1,
         FB.xor x.2.1 isNonEscQuotationMark,
         F.eq c '\\' &&& FB.not x.2.2)) s).1.length
      = input.length + s.1.length by simpa using h ([], default, default)
  induction input with
  | nil => simp
  | cons _ _ ih => intro s; simp only [List.foldl_cons, List.length_cons]; rw [ih]; simp; omega
-/
-- def stringBodies (input : List (F p)) : List (FB p) :=
--   (stringBodiesRev₁ input).1


-- def stringBodies' (input : List (F p)) : List (FB p) :=
  -- (stringBodiesRev₁ input.reverse).1.reverse
  -- (stringBodiesRev₀ input).1.reverse

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
  input.mapM (fun c ↦ do (←F.eq c '{') - (←F.eq c '}'))

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

-- def FList.eq (a b : List (F p)) : Option (FB p) :=
--   (a.zip b).foldlM (fun acc (a,b) ↦ do  acc * (←F.eq a b)) 1
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
    ((←FList.eq evValue requiredEvValLen4) ||| (←FList.eq evValue requiredEvValLen6))
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
  let fieldHash ← hashBytesToFieldWithLen (field.chars.map FBitVec.toF) field.len
  -- Check 3: field[0] == '"' (ASCII 34)
  let firstChar ← selectArrayValue (field.chars.map FBitVec.toF) 0
  F.guardedAssertEq perform firstChar '\"'
  -- Check 4: name is a substring of field starting at index 1
  let nameOk ← isSubstringFS h_name field fieldHash name 1
  F.guardedEq0 perform (FB.not nameOk)
  -- Check 5: field[name_len + 1] == '"' (ASCII 34)
  let nameClosingQuote ← selectArrayValue (field.chars.map FBitVec.toF) (name.len + 1)
  F.guardedAssertEq perform nameClosingQuote '\"'
  -- Check 6: field[colon_index] == ':' (ASCII 58)
  let colonChar ← selectArrayValue (field.chars.map FBitVec.toF) colon_index
  F.guardedAssertEq perform colonChar ':'
  -- Check 7: value is a substring of field starting at value_index
  let valueOk ← isSubstringFS h_value field fieldHash value value_index
  F.guardedEq0 perform (FB.not valueOk)
  -- Check 8: field[field_len - 1] == ',' (44) or '}' (125)
  let lastChar ← selectArrayValue (field.chars.map FBitVec.toF) (field.len - 1)
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
  let fieldChars := field.chars.map FBitVec.toF
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
  (inZone.zip field.chars).toList.forM fun (z, c) ↦ do
    let ws ← FChar.isWhitespace c
    F.guardedEq0 perform (z &&& FB.not ws)
  -- Check 2: value must not contain ',', '}', or '"'
  -- valueSelector: 1s at [value_index, value_index + value_len)
  let valueSel ← arraySelector maxKVPairLen value_index (value_index + value.len)
  (valueSel.zip fieldChars).toList.forM fun (sel, c) ↦ do
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
  let fieldChars := field.chars.map FBitVec.toF
  -- Check 0: field[value_index - 1] == '"' (opening quote around value)
  let valueFirstQuote ← selectArrayValue fieldChars (value_index - 1)
  F.guardedAssertEq perform valueFirstQuote 34
  -- Check 1: field[value_index + value_len] == '"' (closing quote around value)
  let valueSecondQuote ← selectArrayValue fieldChars (value_index + value.len)
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
  (inZone.zip (nameOrValue.zip (field_string_bodies.zip field.chars))).toList.forM fun (z, nv, sb, c) ↦ do
    -- Whitespace check: if in a whitespace zone, the character must be whitespace
    let ws ← FChar.isWhitespace c
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
  let fieldChars := field.chars.map FBitVec.toF
  -- Char before value
  let charBeforeValue ← selectArrayValue fieldChars (valueIndex - 1)
  let beforeIsQuote      : FB bn254 ← F.eq charBeforeValue '\"'
  let beforeIsWhitespace : FB bn254 ← FChar.isWhitespace (← F8.ofF charBeforeValue)
  let beforeIsWsOrQuote := FB.or beforeIsQuote beforeIsWhitespace
  -- Check: char before value is quote/whitespace, OR it is the colon (valueIndex - 1 == colonIndex)
  eq0 ((1 - beforeIsWsOrQuote) &&& (valueIndex - 1 - colonIndex))
  -- Char after value
  let charAfterValue ← selectArrayValue fieldChars (valueIndex + value.len)
  let afterIsQuote      : FB bn254 ← F.eq charAfterValue '\"'
  let afterIsWhitespace : FB bn254 ← FChar.isWhitespace (← F8.ofF charAfterValue)
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
  (inZone.zip field.chars).toList.forM fun (z, c) ↦ do
    let ws ← FChar.isWhitespace c
    eq0 (z &&& FB.not ws)

end JWT

namespace TestJWT

open JWT

open Clap.Lang Core ZMod FString FArray HashToField Primes

abbrev p := Primes.bn254

instance : Coe Char (F p) := charToFp

attribute [local simp] Clap.Spec.Compiler.isZero F.eq FB.not FB.or

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
-- stringBodies

def isEscape (l : List (F p)) (i : Fin l.length) : Bool :=
-- def isEscape (l : List (F p)) (i : Fin l.length) : Prop :=
  match _ : i.val with
  | 0 =>
    match l[i] with
    | '\\' => True
    | _ => False
  | i' + 1 =>
    match l[i] with
    | '\\' => ¬ isEscape l ⟨i', by lia⟩
    | _ => False

def isQuotation (l : List (F p)) (i : Fin l.length) : Bool :=
-- def isQuotation (l : List (F p)) (i : Fin l.length) : Prop :=
  match _ : i.val with
  | 0 =>
    match l[i] with
    | '"' => True
    | _ => False
  | i' + 1 =>
    match l[i] with
    | '"' => ¬ isEscape l ⟨i', by lia⟩
    | _ => False

def isInQuotes (l : List (F p)) (i : Fin l.length) : Bool :=
  ¬isQuotation l i ∧ Odd {j | j < i ∧ isQuotation l j}.toFinset.card
  -- (List.range i).map (fun j ↦ isQuotation l ⟨j, by lia⟩) = []
  -- sorry
  -- have _ : Std.Commutative (· ^^ ·) := ⟨Bool.xor_comm⟩

  -- (Finset.range i).fold fun (a b : Fin _) ↦ isQuotation l a ^^ isQuotation l b
  -- (Multiset.range i).map (fun j ↦ isQuotation l ⟨j, sorry⟩) = sorry
  -- .fold xor false = sorry
  -- Xor

private def stringBodiesRev₁ (input : List (F p)) : List (FB p) × FB p × FB p :=
  input.foldr go
    -- ( fun (acc, openedQuotes, escaped) c ↦
    --     let isNonEscQuotationMark := F.eq c '\"' &&& FB.not escaped
    --     let acc' := openedQuotes * FB.not isNonEscQuotationMark :: acc
    --     let openedQuotes' := FB.xor openedQuotes isNonEscQuotationMark
    --     let escaped' := F.eq c '\\' &&& FB.not escaped
    --     (acc', openedQuotes', escaped')
    -- )
    ([], default, default)
 where
  go : F p → List (FB p) × FB p × FB p → List (FB p) × FB p × FB p :=
    fun c (acc, openedQuotes, escaped) ↦
      let isNonEscQuotationMark := FB.and (F.eqPure c '\"') (FB.not escaped)
      let acc' := openedQuotes * FB.not isNonEscQuotationMark :: acc
      let openedQuotes' := FB.xor openedQuotes isNonEscQuotationMark
      let escaped' := FB.and (F.eqPure c '\\') (FB.not escaped)
      (acc', openedQuotes', escaped')

def stringBodiesR (input : List (F p)) : List (FB p) :=
  (stringBodiesRev₁ input.reverse).1.reverse
  -- (stringBodiesRev₀ input).1.reverse

#eval! isInQuotes ['"', '_', '"'] 0

private def stringBodiesGo : List (FB p) × FB p × FB p → F p → List (FB p) × FB p × FB p :=
  fun (acc, openedQuotes, escaped) c ↦
    let isNonEscQuotationMark := FB.and (F.eqPure c '\"') (FB.not escaped)
    let acc' := openedQuotes * FB.not isNonEscQuotationMark :: acc
    let openedQuotes' := FB.xor openedQuotes isNonEscQuotationMark
    let escaped' := FB.and (F.eqPure c '\\') (FB.not escaped)
    (acc', openedQuotes', escaped')

private def stringBodiesRev' (input : List (F p)) : List (FB p) × FB p × FB p :=
  input.foldl stringBodiesGo ([], default, default)

private def stringBodies' (input : List (F p)) : List (FB p) := do
  (stringBodiesRev' input).1.reverse

private lemma foldr_stringBodies₀_length : ∀ (l acc : List (F p)) (x y : F p),
  (List.foldr (fun y x => stringBodiesGo x y) (acc, x, y) l).1.length =
    (List.foldr (fun y x => stringBodiesGo x y) ([], default, default) l).1.length
      + acc.length
:= by
  intro l acc x y
  revert acc
  induction l with
  | nil => simp
  | cons h t ih =>
    intro acc
    simp [List.foldr, stringBodiesGo]
    simp [stringBodiesGo] at ih
    rw [ih]
    lia

private lemma foldr_stringBodies₁_length : ∀ (l acc : List (F p)) (x y : F p),
  (List.foldr stringBodiesRev₁.go (acc, x, y) l).1.length =
    (List.foldr stringBodiesRev₁.go ([], default, default) l).1.length + acc.length
:= by
  intro l acc x y
  revert acc
  induction l with
  | nil => simp
  | cons h t ih =>
    intro acc
    simp [List.foldr, stringBodiesRev₁.go]
    rw [ih]
    lia

-- private lemma foldl_stringBodies₀_acc : ∀ (l : List (F p)) init,
--   (List.foldl stringBodiesRev₀.go init l).1.take init.1.length = init.1
-- := by
--   intro l
--   induction l with
--   | nil => simp
--   | cons h t ih =>
--     intro acc
--     unfold List.foldl
--     simp [stringBodiesRev₀.go]

--     -- specialize ih (stringBodiesRev₀.go acc h)
--     -- rw [ih]
--     sorry

private lemma stringBodies₀_length (l : List (F p)) :
  (stringBodiesRev' l).1.length = l.length
:= by
  induction l with
  | nil => simp [stringBodiesRev']
  | cons h t ih =>
    simp_all [stringBodiesRev']
    rw [←List.foldr_reverse] at ih ⊢
    rw [stringBodiesGo]
    simp [FB.not, default, FB.and, FB.xor]
    rw [←List.foldr_reverse, ←ih, foldr_stringBodies₀_length]
    simp

private lemma stringBodies₁_length (l : List (F p)) :
  (stringBodiesRev₁ l).1.length = l.length
:= by
  induction l with
  | nil => simp [stringBodiesRev₁]
  | cons h t ih =>
    simp_all [stringBodiesRev₁]
    -- rw [←List.foldr_reverse] at ih ⊢
    rw [stringBodiesRev₁.go]
    simp [FB.not, default, FB.and]
    rw [←ih, foldr_stringBodies₁_length]
    simp

lemma stringBodies_length (l : List (F p)) : (stringBodies' l).length = l.length := by
  simp [stringBodies', stringBodies₀_length, stringBodies₁_length]

lemma stringBodiesR_length (l : List (F p)) : (stringBodiesR l).length = l.length := by
  simp [stringBodiesR, stringBodies₁_length]

example : ∀ (h : F p) (t : List (F p)) (i : Fin t.length),
  (stringBodies' (h :: t))[i]'(by simp [stringBodies_length]) = 1 ↔
    (h = '\"' ∧ (stringBodies' t)[i]'(by simp [stringBodies_length]) = 0
      ∨
      h ≠ '\"' ∧ (stringBodies' t)[i]'(by simp [stringBodies_length]) = 1
    )
:= by sorry

lemma quotes₂ : ∀ (t : List (F p)) (i : Fin (t.length + 1)) (i_pos : i.val > 0),
  (stringBodiesR ('\"' :: t))[i]'(by simp [stringBodiesR_length]; lia) = 1 ↔
    (stringBodiesR t)[i.val - 1]'(by simp [stringBodiesR_length]; lia) ≠ 1
:= by sorry

lemma quotes₃ : ∀ (h : F p) (t : List (F p)) (i : Fin (t.length + 1)) (i_pos : i.val > 0) (ne_q : h ≠ '\"'),
  (stringBodiesR (h :: t))[i]'(by simp [stringBodiesR_length]; lia) = 1 ↔
    (stringBodiesR t)[i.val - 1]'(by simp [stringBodiesR_length]; lia) = 1
:= by sorry

lemma quotes₁ (l : List (F p)) (i : Fin (l.length + 1)) (i_pos : i.val > 0) :
  isInQuotes ('\"' :: l) i = ¬ isInQuotes l ⟨i-1, by lia⟩
:= by
  induction l with
  | nil =>
    simp [isInQuotes]
    grind
  | cons h t ih =>
    simp [isInQuotes]
    -- aesop
    -- simp [Set.ncard_def, Set.encard, ENat.card]
    sorry

lemma quotes₀ (h : F p) (t : List (F p)) (i : Fin (t.length + 1)) (i_pos : i.val > 0) (ne_q : h ≠ '\"') :
  isInQuotes (h :: t) i = isInQuotes t ⟨i-1, by lia⟩
:= by
  sorry

example (l : List (F p)) (_ : ¬l.isEmpty): isInQuotes l ⟨0, by grind⟩ = false := by
  simp [isInQuotes, isQuotation]
  unfold_projs
  simp

lemma drop_len init (l : List (F p)) :
  (List.foldr stringBodiesRev₁.go init l).1.drop l.length = init.1
:= by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [stringBodiesRev₁.go, ih]

lemma stringBodies_zero (l : List (F p)) (nonempty : ¬l.isEmpty) :
  (stringBodiesR l)[0]'(by grind [stringBodiesR_length]) = 0
:= by
  unfold stringBodiesR
  rw [List.getElem_reverse]
  simp only [stringBodies₁_length, List.length_reverse, tsub_zero, getElem]
  have length_pred_add_zero : l.length - 1 = l.length - 1 + 0 := by rw [add_zero]
  conv => left; arg 2; arg 1; rw [length_pred_add_zero]
  simp only [List.get_eq_getElem]
  rw [←List.getElem_drop (h := by simp [stringBodies₁_length]; grind)]
  unfold stringBodiesRev₁
  rcases l with (_ | ⟨h, t⟩)
  · grind
  · simp only [List.length, Nat.add_sub_cancel_right]
    simp only
      [List.reverse_cons, List.foldr_append, List.foldr_cons, List.foldr_nil]
    conv => left; arg 1; rw [←List.length_reverse]
    conv => left; arg 1; rw [drop_len]
    unfold stringBodiesRev₁.go
    simp only [List.getElem_cons_zero, mul_eq_zero]
    left
    simp only [default]

theorem isInQuotes_iff (l : List (F p)) :
  ∀ i : Fin l.length,
    isInQuotes l i ↔ (stringBodiesR l)[i]'(by simp[stringBodiesR_length]) = 1
:= by
  intro i
  induction l with
  | nil =>
    simp at i
    cases i
    contradiction
  | cons h t ih =>
    simp at i
    by_cases h_quotes : h = '"'
    · by_cases i_pos : i > 0
      · subst h_quotes
        rw [quotes₁ t i i_pos]
        simp only [ih, Fin.getElem_fin, List.length_cons]
        have := quotes₂ t i i_pos
        simp at this
        rw [←this]
        simp
      · simp at i_pos
        subst i_pos
        simp [stringBodies_zero, isInQuotes]
        intro; use 0; simp; grind
    · by_cases i_pos : i > 0
      · rw [quotes₀ h t i i_pos h_quotes]
        simp only [ih, Fin.getElem_fin, List.length_cons]
        have := quotes₃ h t i i_pos h_quotes
        simp at this
        rw [←this]
      · simp at i_pos
        subst i_pos
        simp [stringBodies_zero, isInQuotes]
        intro; use 0; simp; grind

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
  stringBodies (p := p) inp == expected := by native_decide

/-
  { a "a\"a" } →
  000001111000
-/
example :
  let inp      := parseCharsASCII "{ a \"a\\\"a\" }"
  let expected := parseBitString  "0000 01 1 11 000"
  stringBodies (p := p) inp == expected := by native_decide

/-
  "i\i""i" →
  01110010
-/
example :
  let inp      := parseCharsASCII "\"i\\i\"\"i\""
  let expected := parseBitString  " 01 11 0 01 0"
  stringBodies (p := p) inp == expected := by native_decide

/-
  "i\"\\\"i" →
  0111111110
-/
example :
  let inp      := parseCharsASCII "\"i\\\"\\\\\\\"i\""
  let expected := parseBitString  " 01 1 1 1 1 1 11 0"
  stringBodies (p := p) inp == expected := by native_decide

/-
  """""" →
  000000
-/
example :
  let inp      := parseCharsASCII "\"\"\"\"\"\""
  let expected := parseBitString  " 0 0 0 0 0 0"
  stringBodies (p := p) inp == expected := by native_decide

/-
  \"\""i"\"\" →
  00000100000
-/
example :
  let inp      := parseCharsASCII "\\\"\\\"\"i\"\\\"\\\""
  let expected := parseBitString  " 0 0 0 0 01 0 0 0 0 0"
  stringBodies (p := p) inp == expected := by native_decide

/-
  \\"\\" →
  000110
-/
example :
  let inp      := parseCharsASCII "\\\\\"\\\\\""
  let expected := parseBitString  " 0 0 0 1 1 0"
  stringBodies (p := p) inp == expected := by native_decide

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
  let ascii := s.toList.map (fun c ↦ ch c.toNat)
  let padded := ascii ++ List.replicate (maxLen - ascii.length) (ch 0)
  ⟨⟨padded.toArray, by simp [padded, ascii, String.length_toList]; omega⟩, (s.length : ZMod p)⟩
where
  ch (n : ℕ) : FChar p := Clap.num2bitsLsbPure 8 n

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
-- The \" at positions 6-7 is an escaped quote, so stringBodies stays open through it.
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
