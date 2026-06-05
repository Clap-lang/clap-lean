import Clap.Lang
import Clap.Array
import Clap.FString
import Clap.HashToField

namespace JWT

open Clap.Lang Primes

variable {p : ℕ} [Fact (Nat.Prime p)]

instance : Coe Char (F p) where
  coe c := c.toNat

private def stringBodiesRev₀ (input : List (F p)) : Option (List (FB p) × FB p × FB p) :=
  input.foldlM
    ( fun (acc, openedQuotes, escaped) c ↦ do
        let isNonEscQuotationMark := (←F.eq c '\"') &&& FB.not escaped
        let acc' := openedQuotes * FB.not isNonEscQuotationMark :: acc
        let openedQuotes' := FB.xor openedQuotes isNonEscQuotationMark
        let escaped' := (←F.eq c '\\') &&& FB.not escaped
        some (acc', openedQuotes', escaped')
    )
    ([], default, default)

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

/--
  Enforce that if uid name is "email", the email verified field is either true or "true"
-/
def emailVerifiedCheck
  {MAX_UID_NAME_LEN MAX_EV_NAME_LEN MAX_EV_VALUE_LEN : ℕ}
  (uidName : FString p MAX_UID_NAME_LEN)
  (evName  : FString p MAX_EV_NAME_LEN)
  (evValue : FString p MAX_EV_VALUE_LEN)
  : Option (FB p)
:= do
  let uidIsEmail ← uidName.isPaddedOf "email"
  FB.conditionallyAssert uidIsEmail (←evName.isPaddedOf "email_verified")
  let evValueTrue := ((←evValue.isPaddedOf "true") ||| (←evValue.isPaddedOf "\"true\""))
  FB.conditionallyAssert uidIsEmail evValueTrue
  return uidIsEmail

namespace Spec.JWT

def emailVerifiedCheck (uidName evName evValue : String) : Option Bool := do
  let uidIsEmail := uidName = "email"
  Spec.FB.conditionallyAssert uidIsEmail (evName = "email_verified")
  Spec.FB.conditionallyAssert uidIsEmail (evValue = "true" || evValue = "\"true\"")
  return uidIsEmail

lemma evailVerifiedCheck_equiv {wa wb wc}
  (h : 2^8 < p)
  (a : FString p wa) (ha: Spec.FString.valid a)
  (b : FString p wb) (hb: Spec.FString.valid b)
  (c : FString p wc) (hc: Spec.FString.valid c) :
  _root_.JWT.emailVerifiedCheck a b c =
    Option.map FB.ofBool
    (emailVerifiedCheck (Spec.FString.toString a)
                        (Spec.FString.toString b)
                        (Spec.FString.toString c)) := by
  unfold _root_.JWT.emailVerifiedCheck emailVerifiedCheck
  rw [Spec.FString.isPaddedOf_equiv]
  rw [Spec.FString.isPaddedOf_equiv]
  simp
  rw [Spec.FB.conditionallyAssert_equiv]
  rw [Spec.FString.isPaddedOf_equiv]
  rw [Spec.FString.isPaddedOf_equiv]
  simp [Spec.FB.left_inv]
  rw [Spec.FB.conditionallyAssert_equiv]
  simp [Spec.FB.left_inv]
  rw [Spec.FB.or_equiv]
  simp [Spec.FB.left_inv]
  all_goals try apply Spec.FB.valid_ofBool
  rw [Spec.FB.or_equiv] ; apply Spec.FB.valid_ofBool
  all_goals try apply Spec.FB.valid_ofBool
  all_goals try assumption
  all_goals try (simp [String.length] ; omega)
  all_goals try decide

end Spec.JWT

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
  let nameOk ← FString.isSubstringFS h_name field fieldHash name 1
  F.guardedEq0 perform (FB.not nameOk)
  -- Check 5: field[name_len + 1] == '"' (ASCII 34)
  let nameClosingQuote ← selectArrayValue field.data (name.len + 1)
  F.guardedAssertEq perform nameClosingQuote '\"'
  -- Check 6: field[colon_index] == ':' (ASCII 58)
  let colonChar ← selectArrayValue field.data colon_index
  F.guardedAssertEq perform colonChar ':'
  -- Check 7: value is a substring of field starting at value_index
  let valueOk ← FString.isSubstringFS h_value field fieldHash value value_index
  F.guardedEq0 perform (FB.not valueOk)
  -- Check 8: field[field_len - 1] == ',' (44) or '}' (125)
  let lastChar ← selectArrayValue field.data (field.len - 1)
  -- Enforce (lastChar - 44) * (lastChar - 125) == 0
  F.guardedEq0 perform ((lastChar - (',' : F _)) &&& (lastChar - ('}' : F _)))

-- revised parseJWTFieldSharedLogic below
section
open HashToField FString FArray

/-- Check 0: `name_len < colon_index`. -/
def checkNameBeforeColon {wn : ℕ}
    (perform : FB bn254) (name : FString bn254 wn) (colonIndex : F bn254) : Option Unit := do
  F.guardedEq0 perform (FB.not (← F.lessThan 20 name.len colonIndex))

/-- Check 1: `colon_index < value_index`. -/
def checkColonBeforeValue
    (perform : FB bn254) (colonIndex valueIndex : F bn254) : Option Unit := do
  F.guardedEq0 perform (FB.not (← F.lessThan 20 colonIndex valueIndex))

/-- Check 2: `field_len > name_len + value_len`. -/
def checkFieldLongEnough {wf wn wv : ℕ}
    (perform : FB bn254) (field : FString bn254 wf) (name : FString bn254 wn)
    (value : FString bn254 wv) : Option Unit := do
  F.guardedEq0 perform (FB.not (← F.greaterThan 20 field.len (name.len + value.len)))

/-- Check 3: `field[0] == '"'`. -/
def checkOpensWithQuote {wf : ℕ}
    (perform : FB bn254) (field : FString bn254 wf) : Option Unit := do
  let firstChar ← selectArrayValue field.data 0
  F.guardedAssertEq perform firstChar '\"'

/-- Check 4: `name` is a substring of `field` starting at index 1. -/
def checkNameMatches {maxKVPairLen maxNameLen : ℕ}
    (perform : FB bn254) (h_name : maxNameLen ≤ maxKVPairLen)
    (field : FString bn254 maxKVPairLen) (fieldHash : F bn254)
    (name : FString bn254 maxNameLen) : Option Unit := do
  let nameOk ← FString.isSubstringFS h_name field fieldHash name 1
  F.guardedEq0 perform (FB.not nameOk)

/-- Check 5: `field[name_len + 1] == '"'`. -/
def checkNameClosingQuote {maxKVPairLen maxNameLen : ℕ}
    (perform : FB bn254) (field : FString bn254 maxKVPairLen)
    (name : FString bn254 maxNameLen) : Option Unit := do
  let nameClosingQuote ← selectArrayValue field.data (name.len + 1)
  F.guardedAssertEq perform nameClosingQuote '\"'

/-- Check 6: `field[colon_index] == ':'`. -/
def checkColonAt {wf : ℕ}
    (perform : FB bn254) (field : FString bn254 wf) (colonIndex : F bn254) : Option Unit := do
  let colonChar ← selectArrayValue field.data colonIndex
  F.guardedAssertEq perform colonChar ':'

/-- Check 7: `value` is a substring of `field` starting at `value_index`. -/
def checkValueMatches {maxKVPairLen maxValueLen : ℕ}
    (perform : FB bn254) (h_value : maxValueLen ≤ maxKVPairLen)
    (field : FString bn254 maxKVPairLen) (fieldHash : F bn254)
    (value : FString bn254 maxValueLen) (valueIndex : F bn254) : Option Unit := do
  let valueOk ← FString.isSubstringFS h_value field fieldHash value valueIndex
  F.guardedEq0 perform (FB.not valueOk)

/-- Check 8: `field[field_len - 1]` is `,` (44) or `}` (125). -/
def checkEndsWithDelimiter {wf : ℕ}
    (perform : FB bn254) (field : FString bn254 wf) : Option Unit := do
  let lastChar ← selectArrayValue field.data (field.len - 1)
  F.guardedEq0 perform ((lastChar - (',' : F _)) &&& (lastChar - ('}' : F _)))

/-- Refactored `parseJWTFieldSharedLogic` -/
private def parseJWTFieldSharedLogic'
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
  checkNameBeforeColon   perform name colon_index
  checkColonBeforeValue  perform colon_index value_index
  checkFieldLongEnough   perform field name value
  let fieldHash ← hashBytesToField field
  checkOpensWithQuote    perform field
  checkNameMatches       perform h_name field fieldHash name
  checkNameClosingQuote  perform field name
  checkColonAt           perform field colon_index
  checkValueMatches      perform h_value field fieldHash value value_index
  checkEndsWithDelimiter perform field

end

namespace Spec.JWT

/-! ### Specification of `parseJWTFieldSharedLogic`

The circuit enforces nine independent structural checks on a JWT key–value field of the
shape `[]name[]:[]value[](,|})` (where `[]` is arbitrary filler). Each check gets its own
definition below, `parseJWTFieldSharedLogic_spec` sequences them and every check gated by `perform = ¬skip`.

Note: `field` is decoded to its raw byte (`rawChars`, padding included) because the circuit addresses it positionally (`selectArrayValue`) and via
Fiat–Shamir substring matching (`isSubstringFS`), both of which can read past `field.len`. `name`/`value` are decoded to their "live" content (`liveChars`), ie, the only part the
substring checks consume.

Another NOTE: checks 4 and 7 are stated as pure substring-matching (the semantics of the Fiat–Shamir `isSubstringFS`). depends on an `isSubstringFS_equiv` some form of Fiat–Shamir soundness. -/

/-- Decode every byte of the buffer (including 0-padding) to a `Char`. -/
def rawChars {w : ℕ} (fs : FString bn254 w) : List Char :=
  fs.data.toList.map Spec.F8.toChar

/-- Decode the "live" region (first `len` bytes) of the buffer to a `Char` list. -/
def liveChars {w : ℕ} (fs : FString bn254 w) : List Char :=
  (rawChars fs).take fs.len.val

/-- Check 0: the name ends before the colon. -/
def nameBeforeColon (name : List Char) (colonIndex : ℕ) : Bool :=
  name.length < colonIndex

/-- Check 1: the colon comes before the value. -/
def colonBeforeValue (colonIndex valueIndex : ℕ) : Bool :=
  colonIndex < valueIndex

/-- Check 2: the field is long enough to hold the name, the colon and the value. -/
def fieldLongEnough (name value : List Char) (fieldLen : ℕ) : Bool :=
  name.length + value.length < fieldLen

/-- Check 3: the field opens with a double quote `"`. -/
def opensWithQuote (field : List Char) : Bool :=
  field[0]? == some '"'

/-- Check 4: `name` occurs in `field` right after the opening quote (index 1). -/
def nameMatches (field name : List Char) : Bool :=
  name.isPrefixOf (field.drop 1)

/-- Check 5: the name is closed by a quote `"` at index `name.length + 1`. -/
def nameClosingQuote (field name : List Char) : Bool :=
  field[name.length + 1]? == some '"'

/-- Check 6: the colon `:` sits at `colonIndex`. -/
def colonAt (field : List Char) (colonIndex : ℕ) : Bool :=
  field[colonIndex]? == some ':'

/-- Check 7: `value` occurs in `field` starting at `valueIndex`. -/
def valueMatches (field value : List Char) (valueIndex : ℕ) : Bool :=
  value.isPrefixOf (field.drop valueIndex)

/-- Check 8: the field's last live character is a `,` or `}` delimiter. -/
def endsWithDelimiter (field : List Char) (fieldLen : ℕ) : Bool :=
  field[fieldLen - 1]? == some ',' || field[fieldLen - 1]? == some '}'

def parseJWTFieldSharedLogic_spec
    (field name value : List Char)
    (fieldLen colonIndex valueIndex : ℕ)
    (skip : Bool) : Option Unit := do
  let perform := !skip
  Spec.FB.conditionallyAssert perform (nameBeforeColon name colonIndex)
  Spec.FB.conditionallyAssert perform (colonBeforeValue colonIndex valueIndex)
  Spec.FB.conditionallyAssert perform (fieldLongEnough name value fieldLen)
  Spec.FB.conditionallyAssert perform (opensWithQuote field)
  Spec.FB.conditionallyAssert perform (nameMatches field name)
  Spec.FB.conditionallyAssert perform (nameClosingQuote field name)
  Spec.FB.conditionallyAssert perform (colonAt field colonIndex)
  Spec.FB.conditionallyAssert perform (valueMatches field value valueIndex)
  Spec.FB.conditionallyAssert perform (endsWithDelimiter field fieldLen)

/-! #### Per-check lemmas
Each sub-circuit refines its corresponding `Spec.JWT` check, gated by `perform`
-/

lemma checkNameBeforeColon_equiv {wn : ℕ}
    (perform : FB bn254) (name : FString bn254 wn) (colonIndex : F bn254)
    (hperform : Spec.FB.valid perform) (hname : Spec.FString.valid name)
    (hname_w : name.len.val < 2 ^ 20) (hcolon_w : colonIndex.val < 2 ^ 20) :
    _root_.JWT.checkNameBeforeColon perform name colonIndex
      = Spec.FB.conditionallyAssert (Spec.FB.toBool perform) (nameBeforeColon (liveChars name) colonIndex.val) := by
  sorry

lemma checkColonBeforeValue_equiv
    (perform : FB bn254) (colonIndex valueIndex : F bn254)
    (hperform : Spec.FB.valid perform)
    (hcolon_w : colonIndex.val < 2 ^ 20) (hvalue_w : valueIndex.val < 2 ^ 20) :
    _root_.JWT.checkColonBeforeValue perform colonIndex valueIndex
      = Spec.FB.conditionallyAssert (Spec.FB.toBool perform) (colonBeforeValue colonIndex.val valueIndex.val) := by
  sorry

lemma checkFieldLongEnough_equiv {wf wn wv : ℕ}
    (perform : FB bn254) (field : FString bn254 wf) (name : FString bn254 wn) (value : FString bn254 wv)
    (hperform : Spec.FB.valid perform)
    (hname : Spec.FString.valid name) (hvalue : Spec.FString.valid value)
    (hfield_w : field.len.val < 2 ^ 20) (hlens_w : name.len.val + value.len.val < 2 ^ 20) :
    _root_.JWT.checkFieldLongEnough perform field name value
      = Spec.FB.conditionallyAssert (Spec.FB.toBool perform) (fieldLongEnough (liveChars name) (liveChars value) field.len.val) := by
  sorry

lemma checkOpensWithQuote_equiv {wf : ℕ}
    (perform : FB bn254) (field : FString bn254 wf)
    (hperform : Spec.FB.valid perform) (hfield : Spec.FString.valid field) (hwf : 0 < wf) :
    _root_.JWT.checkOpensWithQuote perform field
      = Spec.FB.conditionallyAssert (Spec.FB.toBool perform) (opensWithQuote (rawChars field)) := by
  sorry

lemma checkNameMatches_equiv {maxKVPairLen maxNameLen : ℕ}
    (perform : FB bn254) (h_name : maxNameLen ≤ maxKVPairLen)
    (field : FString bn254 maxKVPairLen) (fieldHash : F bn254) (name : FString bn254 maxNameLen)
    (hperform : Spec.FB.valid perform)
    (hname_fs : FString.isSubstringFS h_name field fieldHash name 1
      = some (FB.ofBool (nameMatches (rawChars field) (liveChars name)))) :
    _root_.JWT.checkNameMatches perform h_name field fieldHash name
      = Spec.FB.conditionallyAssert (Spec.FB.toBool perform) (nameMatches (rawChars field) (liveChars name)) := by
  sorry

lemma checkNameClosingQuote_equiv {maxKVPairLen maxNameLen : ℕ}
    (perform : FB bn254) (field : FString bn254 maxKVPairLen) (name : FString bn254 maxNameLen)
    (hperform : Spec.FB.valid perform) (hfield : Spec.FString.valid field) (hname : Spec.FString.valid name)
    (hidx_rng : name.len.val + 1 < maxKVPairLen) :
    _root_.JWT.checkNameClosingQuote perform field name
      = Spec.FB.conditionallyAssert (Spec.FB.toBool perform) (nameClosingQuote (rawChars field) (liveChars name)) := by
  sorry

lemma checkColonAt_equiv {wf : ℕ}
    (perform : FB bn254) (field : FString bn254 wf) (colonIndex : F bn254)
    (hperform : Spec.FB.valid perform) (hfield : Spec.FString.valid field)
    (hcolon_rng : colonIndex.val < wf) :
    _root_.JWT.checkColonAt perform field colonIndex
      = Spec.FB.conditionallyAssert (Spec.FB.toBool perform) (colonAt (rawChars field) colonIndex.val) := by
  sorry

lemma checkValueMatches_equiv {maxKVPairLen maxValueLen : ℕ}
    (perform : FB bn254) (h_value : maxValueLen ≤ maxKVPairLen)
    (field : FString bn254 maxKVPairLen) (fieldHash : F bn254)
    (value : FString bn254 maxValueLen) (valueIndex : F bn254)
    (hperform : Spec.FB.valid perform)
    (hvalue_fs : FString.isSubstringFS h_value field fieldHash value valueIndex
      = some (FB.ofBool (valueMatches (rawChars field) (liveChars value) valueIndex.val))) :
    _root_.JWT.checkValueMatches perform h_value field fieldHash value valueIndex
      = Spec.FB.conditionallyAssert (Spec.FB.toBool perform) (valueMatches (rawChars field) (liveChars value) valueIndex.val) := by
  sorry

lemma checkEndsWithDelimiter_equiv {wf : ℕ}
    (perform : FB bn254) (field : FString bn254 wf)
    (hperform : Spec.FB.valid perform) (hfield : Spec.FString.valid field) (hfield_pos : 0 < field.len.val) :
    _root_.JWT.checkEndsWithDelimiter perform field
      = Spec.FB.conditionallyAssert (Spec.FB.toBool perform) (endsWithDelimiter (rawChars field) field.len.val) := by
  sorry

/--
  we might need additional hypothesis here, specially `isSubstringFS`-related ones :
  * `hfield`/`hname`/`hvalue` — well-formed FStrings (bytes are bytes, `len < maxLen`, 0-padded)
  * `hskip`                   — `skipChecks` is a bit
  * `h*_pos`                  — non-empty substrings / non-empty field (selector & no-underflow)
  * `h*_rng`                  — one-hot-addressable indices in range
  * `h*_w`, `hmax_w`          — operands fit the circuit's hardcoded 20-bit comparators
-/
lemma parseJWTFieldSharedLogic_equiv
    {maxKVPairLen maxNameLen maxValueLen : ℕ}
    (h_name  : maxNameLen  ≤ maxKVPairLen)
    (h_value : maxValueLen ≤ maxKVPairLen)
    (field : FString bn254 maxKVPairLen)
    (name  : FString bn254 maxNameLen)
    (value : FString bn254 maxValueLen)
    (colonIndex valueIndex : F bn254)
    (skipChecks : FB bn254)
    (hfield : Spec.FString.valid field)
    (hname  : Spec.FString.valid name)
    (hvalue : Spec.FString.valid value)
    (hskip  : Spec.FB.valid skipChecks)
    (hname_pos  : 0 < name.len.val)
    (hvalue_pos : 0 < value.len.val)
    (hfield_pos : 0 < field.len.val)
    (hcolon_rng : colonIndex.val < maxKVPairLen)
    (hvalue_rng : valueIndex.val < maxKVPairLen)
    (h1_rng     : 1 < maxKVPairLen)
    (hmax_w     : maxKVPairLen ≤ 2 ^ 20)
    (hcolon_w   : colonIndex.val < 2 ^ 20)
    (hvalue_w   : valueIndex.val < 2 ^ 20) :
    _root_.JWT.parseJWTFieldSharedLogic' h_name h_value field name value colonIndex valueIndex skipChecks
      = parseJWTFieldSharedLogic_spec
          (rawChars field) (liveChars name) (liveChars value) field.len.val colonIndex.val valueIndex.val (Spec.FB.toBool skipChecks) := by
  sorry

/-- a no-op when `skip`, otherwise the conjunction of all nine checks. -/
def parseJWTFieldSharedLogic_high
    (field name value : List Char)
    (fieldLen colonIndex valueIndex : ℕ)
    (skip : Bool) : Option Unit :=
  if skip
      || (nameBeforeColon name colonIndex
       && colonBeforeValue colonIndex valueIndex
       && fieldLongEnough name value fieldLen
       && opensWithQuote field
       && nameMatches field name
       && nameClosingQuote field name
       && colonAt field colonIndex
       && valueMatches field value valueIndex
       && endsWithDelimiter field fieldLen)
  then some () else none

/-- The sequenced gated asserts collapse to the single boolean condition. -/
lemma parseJWTFieldSharedLogic_eq_high :
    parseJWTFieldSharedLogic_spec = parseJWTFieldSharedLogic_high := by
  sorry

end Spec.JWT

namespace Spec.Serialize.JWT

/-! ### Reconstruction specification of `parseJWTFieldSharedLogic`

A alternative to the spec in `Spec.JWT`. Instead of nine predicates, it
says the circuit succeeds iff the field can be reconstructed from its parsed pieces (Dom suggestion).

A JWT key–value field decomposes as

      "  name  "  ws2  :  ws3  value  ws4  ending          (ending ∈ {',', '}'})

At the shared-logic the gaps `ws2, ws3, ws4` are arbitrary. The insecurity of the circuit
-/

/-- Parsed pieces of one JWT field. `ws2`/`ws3`/`ws4` are the gaps after the name's closing quote,
    after the colon, and after the value -/
structure JWTField where
  name   : List Char
  ws2    : List Char
  ws3    : List Char
  value  : List Char
  ws4    : List Char
  ending : Char

/-- Re-serialize a field: `" name " ws2 : ws3 value ws4 ending`. -/
def serialize (f : JWTField) : List Char :=
  ('"' :: f.name) ++ ('"' :: f.ws2) ++ (':' :: f.ws3) ++ f.value ++ f.ws4 ++ [f.ending]

-- Sanity check: unquoted and quoted values share one `serialize`; the value-quotes fold into ws3/ws4.
example : serialize ⟨['a'], [], [], ['b'], [], ','⟩       = "\"a\":b,".toList    := by native_decide
example : serialize ⟨['a'], [], ['"'], ['b'], ['"'], ','⟩ = "\"a\":\"b\",".toList := by native_decide

/-- Live content (first `len` bytes, padding removed) of an FString, as a `Char` list. -/
def liveChars {w : ℕ} (fs : FString bn254 w) : List Char :=
  (fs.data.toList.take fs.len.val).map Spec.F8.toChar

/-- A no-op when `skip`; otherwise `field` re-serializes from some `f` with the given `name`/`value`, colon and
    value at the claimed indices, and `P f` (for quoted and unqoted versions). The shared
    logic uses `P = fun _ => True`; the quoted/unquoted tighten `P`. -/
def ReconstructsWith (P : JWTField → Prop) (field name value : List Char) (colonIndex valueIndex : ℕ) (skip : Bool) : Prop :=
  skip ∨ ∃ f : JWTField,
    field = serialize f ∧
    f.name = name ∧ f.value = value ∧
    (f.ending = ',' ∨ f.ending = '}') ∧
    colonIndex = name.length + 2 + f.ws2.length ∧
    valueIndex = colonIndex + 1 + f.ws3.length ∧
    P f

/-- Shared-logic reconstruction -/
def Reconstructs (field name value : List Char) (colonIndex valueIndex : ℕ) (skip : Bool) : Prop :=
  ReconstructsWith (fun _ => True) field name value colonIndex valueIndex skip

/--
  Refinement of the circuit `parseJWTFieldSharedLogic'`. -/
lemma parseJWTFieldSharedLogic_reconstructs_equiv
    {maxKVPairLen maxNameLen maxValueLen : ℕ}
    (h_name : maxNameLen ≤ maxKVPairLen) (h_value : maxValueLen ≤ maxKVPairLen)
    (field : FString bn254 maxKVPairLen) (name : FString bn254 maxNameLen) (value : FString bn254 maxValueLen)
    (colonIndex valueIndex : F bn254) (skipChecks : FB bn254)
    (hfield : Spec.FString.valid field) (hname : Spec.FString.valid name) (hvalue : Spec.FString.valid value)
    (hskip : Spec.FB.valid skipChecks)
    (hname_pos : 0 < name.len.val) (hvalue_pos : 0 < value.len.val) (hfield_pos : 0 < field.len.val)
    (hcolon_rng : colonIndex.val < maxKVPairLen) (hvalue_rng : valueIndex.val < maxKVPairLen)
    (h1_rng : 1 < maxKVPairLen) (hmax_w : maxKVPairLen ≤ 2 ^ 20)
    (hcolon_w : colonIndex.val < 2 ^ 20) (hvalue_w : valueIndex.val < 2 ^ 20)
    (hfit : valueIndex.val + value.len.val < field.len.val)
    -- probably more hypothesis needed
     :
    (_root_.JWT.parseJWTFieldSharedLogic' h_name h_value field name value colonIndex valueIndex skipChecks = some ())
      ↔ Reconstructs (liveChars field) (liveChars name) (liveChars value) colonIndex.val valueIndex.val (Spec.FB.toBool skipChecks) := by
  sorry

end Spec.Serialize.JWT

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

namespace Spec.Serialize.JWT

/-! #### `parseJWTFieldWithUnquotedValue` -/

/-- Unquoted-value constraints on the parsed pieces: the three gaps are all whitespace, and the
    value contains no JSON delimiter (`,`, `}`, `"`). -/
def isUnquotedField (f : JWTField) : Prop :=
  (∀ c ∈ f.ws2 ++ f.ws3 ++ f.ws4, Spec.F8.isWhitespace_spec c = true) ∧
  (∀ c ∈ f.value, c ≠ ',' ∧ c ≠ '}' ∧ c ≠ '"')

/-- Reconstruction spec for `parseJWTFieldWithUnquotedValue`: the SAME `serialize`, refined so the
    gaps are whitespace and the value is delimiter-free. -/
def ReconstructsUnquoted (field name value : List Char) (colonIndex valueIndex : ℕ) (skip : Bool) : Prop :=
  ReconstructsWith isUnquotedField field name value colonIndex valueIndex skip

lemma parseJWTFieldWithUnquotedValue_reconstructs_equiv
    {maxKVPairLen maxNameLen maxValueLen : ℕ}
    (h_name : maxNameLen ≤ maxKVPairLen) (h_value : maxValueLen ≤ maxKVPairLen)
    (field : FString bn254 maxKVPairLen) (name : FString bn254 maxNameLen) (value : FString bn254 maxValueLen)
    (colonIndex valueIndex : F bn254) (skipChecks : FB bn254)
    (hfield : Spec.FString.valid field) (hname : Spec.FString.valid name) (hvalue : Spec.FString.valid value)
    (hskip : Spec.FB.valid skipChecks)
    (hname_pos : 0 < name.len.val) (hvalue_pos : 0 < value.len.val) (hfield_pos : 0 < field.len.val)
    (hcolon_rng : colonIndex.val < maxKVPairLen) (hvalue_rng : valueIndex.val < maxKVPairLen)
    (h1_rng : 1 < maxKVPairLen) (hmax_w : maxKVPairLen ≤ 2 ^ 20)
    (hcolon_w : colonIndex.val < 2 ^ 20) (hvalue_w : valueIndex.val < 2 ^ 20)
    (hfit : valueIndex.val + value.len.val < field.len.val)
    -- probably more hypothesis here
    :
    (_root_.JWT.parseJWTFieldWithUnquotedValue h_name h_value field name value colonIndex valueIndex skipChecks = some ())
      ↔ ReconstructsUnquoted (liveChars field) (liveChars name) (liveChars value) colonIndex.val valueIndex.val (Spec.FB.toBool skipChecks) := by
  sorry

/-! #### `parseJWTFieldWithQuotedValue`

The value is wrapped in quotes: the opening quote `"` is the last char of `ws3`, the closing
quote `"` is the first char of `ws4` (so the circuit's `field[value_index-1] == '"'` and
`field[value_index+value_len] == '"'` checks are exactly the `ws3`/`ws4` boundary chars);
The gaps around those quotes are whitespace (zones A/B/C);
An auxiliary witness `field_string_bodies` must mark exactly the name and value-content
regions: i.e. name and value are the only JSON string bodies in the field.
The value itself is NOT delimiter-checked (unlike the unquoted case), it is a quoted string body. -/

/-- Decode a bit-vector to `List Bool` (all positions, padding included). -/
def bits {w : ℕ} (v : Vector (FB bn254) w) : List Bool :=
  v.toList.map Spec.FB.toBool

/-- Quoted-value constraints on the parsed pieces: `ws2` is whitespace; `ws3` is whitespace then the
    opening quote `"`; `ws4` is the closing quote `"` then whitespace. The value content is left
    unconstrained here, it is a quoted JSON string body, pinned instead by the string-bodies witness. -/
def isQuotedField (f : JWTField) : Prop :=
  (∀ c ∈ f.ws2, Spec.F8.isWhitespace_spec c = true) ∧
  (∃ w, f.ws3 = w ++ ['"'] ∧ ∀ c ∈ w, Spec.F8.isWhitespace_spec c = true) ∧
  (∃ w, f.ws4 = '"' :: w ∧ ∀ c ∈ w, Spec.F8.isWhitespace_spec c = true)

/-- The string-bodies witness marks exactly the name-content region `[1, 1+nameLen)` and the
    value-content region `[valueIndex, valueIndex+valueLen)`, and nothing else (padding included). -/
def stringBodiesMatch (sb : List Bool) (nameLen valueLen valueIndex : ℕ) : Prop :=
  sb = (List.range sb.length).map fun i => decide ((1 ≤ i ∧ i < 1 + nameLen) ∨ (valueIndex ≤ i ∧ i < valueIndex + valueLen))

def ReconstructsQuoted (field name value : List Char) (stringBodies : List Bool)
    (colonIndex valueIndex : ℕ) (skip : Bool) : Prop :=
  ReconstructsWith isQuotedField field name value colonIndex valueIndex skip
  ∧ (skip ∨ stringBodiesMatch stringBodies name.length value.length valueIndex)

lemma parseJWTFieldWithQuotedValue_reconstructs_equiv
    {maxKVPairLen maxNameLen maxValueLen : ℕ}
    (h_name : maxNameLen ≤ maxKVPairLen) (h_value : maxValueLen ≤ maxKVPairLen)
    (field : FString bn254 maxKVPairLen) (name : FString bn254 maxNameLen) (value : FString bn254 maxValueLen)
    (field_string_bodies : Vector (FB bn254) maxKVPairLen)
    (colonIndex valueIndex : F bn254) (skipChecks : FB bn254)
    (hfield : Spec.FString.valid field) (hname : Spec.FString.valid name) (hvalue : Spec.FString.valid value)
    (hsb : ∀ i : Fin maxKVPairLen, Spec.FB.valid field_string_bodies[i])
    (hskip : Spec.FB.valid skipChecks)
    (hname_pos : 0 < name.len.val) (hvalue_pos : 0 < value.len.val) (hfield_pos : 0 < field.len.val)
    (hvalueidx_pos : 0 < valueIndex.val)
    (hcolon_rng : colonIndex.val < maxKVPairLen) (hvalue_rng : valueIndex.val < maxKVPairLen)
    (h1_rng : 1 < maxKVPairLen) (hmax_w : maxKVPairLen ≤ 2 ^ 20)
    (hcolon_w : colonIndex.val < 2 ^ 20) (hvalue_w : valueIndex.val < 2 ^ 20)
    (hfit : valueIndex.val + value.len.val + 1 < field.len.val)
    -- probably more hypothesis here
    :
    (_root_.JWT.parseJWTFieldWithQuotedValue h_name h_value field name value field_string_bodies colonIndex valueIndex skipChecks = some ())
      ↔ ReconstructsQuoted (liveChars field) (liveChars name) (liveChars value) (bits field_string_bodies) colonIndex.val valueIndex.val (Spec.FB.toBool skipChecks) := by
  sorry

end Spec.Serialize.JWT

end JWT

namespace TestJWT

open JWT

open Clap.Lang FString FArray HashToField Primes

abbrev p := Primes.bn254

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

private def max_UID_name_len : ℕ := 6
private def max_EV_value_len : ℕ := 7
private def uidEmailFString : FString p max_UID_name_len := FString.ofString "email"
private def evTrue₁FString  : FString p max_EV_value_len := FString.ofString "true"
private def evTrue₂FString  : FString p max_EV_value_len := FString.ofString "\"true\""
private def evBadFString : FString p max_EV_value_len := { evTrue₂FString with len := 4 }

private def requiredEvName : FString p 14 := FString.ofString "email_verified"

example :
  enforceNotNested (p := p) 10 2 4 [0, 0, 1, 2, 3, 3, 2, 1, 0, 0] == .none
:=
  by native_decide

example : -- uid is «email»; «email_verified» is «true»
  emailVerifiedCheck (p := p)
    uidEmailFString
    requiredEvName
    evTrue₁FString
  == .some 1
:= by native_decide

example : -- uid is «email»; «email_verified» is «"true"»
  emailVerifiedCheck (p := p)
    uidEmailFString
    requiredEvName
    evTrue₂FString
  == .some 1
:= by native_decide

example : -- uid is «email», but there is no «email_verified»
  emailVerifiedCheck (p := p)
    uidEmailFString
    (FString.ofString (w:=3) "abc")
    evTrue₂FString
  == .none
:= by native_decide

example : -- uid is «email», but «email_verified» is neither «true» nor «"true"»
  emailVerifiedCheck (p := p)
    uidEmailFString
    requiredEvName
    evBadFString
  == .none
:= by native_decide

example : -- uid is not «email»
  emailVerifiedCheck (p := p)
    {uidEmailFString with len := 0}
    requiredEvName
    evTrue₂FString
  == .some 0
:= by native_decide

example : -- uid is not «email», the rest doesn't matter
  emailVerifiedCheck (p := p)
    {uidEmailFString with len := 0}
    (FString.ofString (w:=3) "abc")
    evBadFString
  == .some 0
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
