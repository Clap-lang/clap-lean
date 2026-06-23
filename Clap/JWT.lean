import Mathlib
import Clap.Lang
import Clap.Array
import Clap.FString
import Clap.HashToField

namespace JWT

open Clap.Lang Primes

variable {p : ℕ}

instance : Coe Char (F p) where
  coe c := c.toNat

def stringBodies₀ (openedQuotes : FB p) (escaped : FB p) :
  List (FB p) → List (FB p) → Option (List (FB p))
| revAcc, [] => revAcc
| revAcc, c :: cs => do
  let isNonEscQuotationMark := FB.and (←F.eq c '\"') (FB.not escaped)
  let openedQuotes' := FB.xor openedQuotes isNonEscQuotationMark
  let escaped' := FB.and (←F.eq c '\\') (FB.not escaped)
  stringBodies₀ openedQuotes' escaped' (openedQuotes * FB.not isNonEscQuotationMark :: revAcc) cs

lemma stringBodies₀_length : ∀ (openedQuotes escaped : FB p) revAcc l res,
  some res = stringBodies₀ openedQuotes escaped revAcc l →
  res.length = l.length + revAcc.length
:= by
  intro openedQuotes escaped revAcc l res h
  revert revAcc openedQuotes escaped res
  induction l with
  | nil => simp [stringBodies₀]
  | cons a as ih =>
    intro _ _ _ _ h
    simp [stringBodies₀, F.eq, F.isZero_def] at h
    split at h <;> grind

/-- From keyless:
  Given an array of ask characters representing a JSON object, output a binary array demarquing
  the spaces in between quotes, so that the indices in between quotes in `in` are given the value
  `1` in `out`, and are 0 otherwise. Escaped quotes are not considered quotes in this subcircuit
  input =  { asdfsdf "as\"df" }
  output = 00000000000111111000
-/
def stringBodies {w} (input : FString p w) : Option (PaddedVector FB p w) :=
  let (eq := h) r := stringBodies₀ 0 0 [] input.data.toArray.toList
  match r with
  | none => none
  | some res =>
    have : res.reverse.toArray.size = w := by
      have hlen := stringBodies₀_length (p := p) 0 0 []
      grind [stringBodies₀, stringBodies₀_length]
    let data : Vector (F p) w := ⟨res.reverse.toArray, this⟩
    .some {data, len := input.len}

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
def bracketsMap {LEN} (input : FString p LEN) : Option (PaddedVector FB p LEN) := do
  let v ←
    input.data.mapM fun c ↦ do
      let eqOpen ← F.eq c '{'
      let eqClose ←F.eq c '}'
      some (eqOpen - eqClose)
  some ⟨v, input.len⟩

/-- Tail recursive helper for `partialSums`. The result is in reverse order. -/
private def partialSums₀ : List (F p) → List (F p) → List (F p)
  | [], revAcc => revAcc
  | a :: as, sums => do
    match sums with
    | [] => partialSums₀ as [a]
    | sum :: sums =>
      let sum' := sum + a
      partialSums₀ as (sum' :: sum :: sums)

lemma partialSumsTR_length : ∀ (l sums revAcc : List (F p)),
  sums = partialSums₀ l revAcc → sums.length = l.length + revAcc.length
:= by
  intro l
  induction l with
  | nil => simp_all [partialSums₀]
  | cons a as ih =>
    intro sums h h
    simp [partialSums₀] at h
    split at h <;> grind

/--
`partialSum` is step 1 from `bracketsDepthMap`:
Compute an intermediate array where each index is a running sum of all previous indices in the input.
The result actually is in *reverse order*. This works well with `bracketsDepthMap`,
which takes input in reverse order.

Example as if the output was in normal order:
input  : 01000101000*00*0000*
output : 01111223333222111110
-/
private def partialSums {LEN : ℕ} (input : Vector (F p) LEN) : Vector (F p) LEN :=
  let (eq := h) revResult := partialSums₀ input.toList []
  have : revResult.toArray.size = LEN := by
    symm at h
    apply partialSumsTR_length at h
    grind
  ⟨revResult.toArray, this⟩

/--
Tail recursive helper for `removeOffset`.
The input is expected in *reverse order*.
-/
private def removeOffset₀ : List (F p) → List (F p) → Option (List (F p))
  | [], acc => return acc
  | [a], acc => return a :: acc
  | a₁ :: a₂ :: as, acc => do
    let isDec ← F.eq a₁ (a₂ + 1)
    removeOffset₀ (a₂ :: as) ((a₁ - isDec) :: acc)

lemma removeOffset_length : ∀ (revInput output acc : List (F p)),
  some output = removeOffset₀ revInput acc → output.length = revInput.length + acc.length
:= by
  intro l
  induction l using List.twoStepInduction with
  | nil => simp_all [removeOffset₀]
  | singleton a =>
    intro l' acc
    simp_all [removeOffset₀]
    grind
  | cons_cons a₁ a₂ as ih₁ ih₂ =>
    intro l' acc h
    simp_all [removeOffset₀]
    simp [F.eq, isZero] at h
    grind

/--
Step 4 from `bracketsDepthMap`:
For each value greater than 1 compared to the previous value in the result of step 3, decrement that value by 1.
The input is expected in *reverse order*. This works well with `partialSums`, which
produces the output in reverse order.

Example as if the input was in normal order:
input  : 00000112222111000000
output : 00000011222111000000
-/
private def removeOffset {LEN : ℕ} (revInput : Vector (F p) LEN) : Option (Vector (F p) LEN) := by
  let result := removeOffset₀ revInput.toList []
  match h : result with
  | none => exact none
  | some l =>
    have : l.toArray.size = LEN := by
      symm at h
      apply removeOffset_length at h
      grind
    exact some (⟨l.toArray, this⟩ : Vector (F p) LEN)

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
def bracketsDepthMap {LEN : ℕ} (input : Vector (F p) LEN) : Option (Vector (F p) LEN) := do
  -- Step 1
  let revSums := partialSums input
  -- Steps 2 and 3
  let revPrelim ← revSums.mapM minusOne
  -- Step 4
  removeOffset revPrelim
 where
  minusOne (a : F p) : Option (F p) := do a - 1 + (←isZero a)

def Vector.hadamardProduct {LEN : ℕ} (lhs rhs : Vector (F p) LEN) : Vector (F p) LEN :=
  lhs.zipWith (· * ·) rhs

def Vector.scalarProduct {LEN : ℕ} (i₁ i₂ : Vector (F p) LEN) : F p :=
  let p := hadamardProduct i₁ i₂
  p.sum

/--
  Given an input `brackets_depth_map`, which must be an output of `BracketsDepthMap` and
  corresponds to the nested brackets depth of the original JWT, and a `start_index` and `field_len`
  corresponding to the first index and length of a full field in the JWT, fails if the given field
  contains any indices inside nested brackets in the original JWT, and succeeds otherwise
-/
def enforceNotNested [Fact (Nat.Prime p)] (LEN : ℕ)
  (startIndex fieldLen : F p)
  (bracketsDepthMap : Vector (F p) LEN) :
  Option Unit
:= do
  let endIndex := startIndex + fieldLen
  let bracketsSelector ← FArray.arraySelector LEN startIndex endIndex
  let o := Vector.scalarProduct bracketsDepthMap bracketsSelector
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

def emailVerifiedCheck  (uidName evName evValue : String) : Option Bool := do
  let uidIsEmail := uidName = "email"
  Spec.FB.conditionallyAssert uidIsEmail (evName = "email_verified")
  Spec.FB.conditionallyAssert uidIsEmail (evValue = "true" || evValue = "\"true\"")
  return uidIsEmail

lemma evailVerifiedCheck_equiv [Fact (Nat.Prime p)] {wa wb wc}
  (h : 2^8 < p)
  (a : FString p wa) (ha: Spec.FString.valid a)
  (b : FString p wb) (hb: Spec.FString.valid b)
  (c : FString p wc) (hc: Spec.FString.valid c) :
  _root_.JWT.emailVerifiedCheck a b c =
    Option.map FB.ofBool
    (emailVerifiedCheck (Spec.FString.toString a)
                        (Spec.FString.toString b)
                        (Spec.FString.toString c)) := by
  unfold _root_.JWT.emailVerifiedCheck;
  rw [ Spec.FString.isPaddedOf_equiv, Spec.FString.isPaddedOf_equiv, Spec.FString.isPaddedOf_equiv, Spec.FString.isPaddedOf_equiv ];
  all_goals try assumption;
  all_goals try exact fun c hc => by fin_cases hc <;> decide;
  · unfold emailVerifiedCheck; simp +decide [ Spec.FB.conditionallyAssert_equiv, Spec.FB.or_equiv, Spec.FB.left_inv, Spec.FB.valid_ofBool ] ;
  · exact lt_of_le_of_lt ( by decide ) h;
  · exact lt_of_le_of_lt ( by decide ) h;
  · exact lt_of_le_of_lt ( by decide ) h;
  · exact lt_of_le_of_lt ( by decide ) h

def arraySelector_spec (len startIdx endIdx : ℕ) : Vector Bool len :=
  Vector.ofFn (fun i => decide (startIdx ≤ (i : ℕ) ∧ (i : ℕ) < endIdx))

lemma arraySelector_equiv [Fact (Nat.Prime p)] (len : ℕ) (startIdx endIdx : F p)
  (hlen : len ≤ p) (hstart : startIdx.val < len)
  (hlt : startIdx.val < endIdx.val)
  (hend : endIdx.val < 2 ^ Clap.minBits len)
  (hw : 2 ^ (Clap.minBits len + 1) < p) :
  FArray.arraySelector len startIdx endIdx
    = some ((arraySelector_spec len startIdx.val endIdx.val).map (FB.ofBool (p := p)))
:= by
  rw [FArray.arraySelector_eq len startIdx endIdx hlen hstart hlt hend hw]
  congr 1
  apply Vector.ext
  intro i hi
  simp only [arraySelector_spec, Vector.getElem_map, Vector.getElem_ofFn, FB.ofBool, FB.true,
    FB.false]
  by_cases h : startIdx.val ≤ (i : ℕ) ∧ (i : ℕ) < endIdx.val <;> simp [h]

/-
Over `ZMod p`, if the integer sum of the canonical representatives of a list is `< p`, then the
    list sums to `0` exactly when every entry is `0`.
-/
lemma zmod_sum_eq_zero_iff {p : ℕ} [NeZero p] (L : List (ZMod p))
    (h : (L.map ZMod.val).sum < p) :
    L.sum = 0 ↔ ∀ x ∈ L, x = 0 := by
      have h_sum_zero_iff : (L.sum : ZMod p) = (↑((List.map ZMod.val L).sum) : ZMod p) := by
        induction L <;> simp +decide [ * ];
      rw [ h_sum_zero_iff, ZMod.natCast_eq_zero_iff ];
      rw [ Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt h ];
      rw [ List.sum_eq_zero_iff ];
      simp +decide [ ZMod.val_eq_zero ]

/-
The scalar product of `bracketsDepthMap` with the `arraySelector` indicator of the window
    `[s, e)` equals the (field) sum of the window obtained by `Vector.extract`.
-/
lemma escalarProduct_arraySelectorSpec_eq {LEN : ℕ} (bdm : Vector (F p) LEN) (s e : ℕ) :
    Vector.escalarProduct bdm ((arraySelector_spec LEN s e).map (FB.ofBool (p := p)))
      = (bdm.extract s e).toList.sum := by
        unfold Vector.escalarProduct;
        unfold Vector.hadamardProduct; simp +decide [ arraySelector_spec ] ;
        rw [ show ( Vector.zipWith ( fun x1 x2 => x1 * x2 ) bdm ( Vector.map FB.ofBool ( Vector.ofFn fun i : Fin LEN => decide ( s ≤ ( i : ℕ ) ) && decide ( ( i : ℕ ) < e ) ) ) ) = Vector.ofFn ( fun i : Fin LEN => if s ≤ ( i : ℕ ) ∧ ( i : ℕ ) < e then bdm[i] else 0 ) from ?_ ];
        · rw [ show ( Vector.ofFn fun i : Fin LEN => if s ≤ ( i : ℕ ) ∧ ( i : ℕ ) < e then bdm[i] else 0 ).sum = ∑ i ∈ Finset.univ.filter ( fun i : Fin LEN => s ≤ ( i : ℕ ) ∧ ( i : ℕ ) < e ), bdm[i] from ?_ ];
          · rw [ ← Finset.sum_subset ( show Finset.image ( fun k : Fin ( Min.min e LEN - s ) => ⟨ s + k, by omega ⟩ : Fin ( Min.min e LEN - s ) → Fin LEN ) Finset.univ ⊆ Finset.filter ( fun i : Fin LEN => s ≤ ( i : ℕ ) ∧ ( i : ℕ ) < e ) Finset.univ from ?_ ) ];
            · rw [ Finset.sum_image ];
              · rw [ ← List.sum_ofFn ];
                congr;
                refine' List.ext_get _ _ <;> aesop;
              · exact fun a _ b _ h => by simpa [ Fin.ext_iff ] using h;
            · simp +zetaDelta at *;
              intro x hx₁ hx₂ hx₃; contrapose! hx₃; use ⟨ x - s, by omega ⟩ ; simp +decide [ hx₁, hx₂ ] ;
            · grind +splitIndPred;
          · rw [ Finset.sum_filter, Vector.sum ];
            convert Finset.sum_congr rfl fun i _ => ?_;
            rotate_left;
            exact fun i => if s ≤ i.val ∧ i.val < e then bdm[i] else 0;
            · rfl;
            · simp +decide [ Finset.sum ];
              conv => rw [ ← Array.toList_ofFn ] ;
              grind;
        · ext i; simp +decide [ FB.ofBool ] ;
          split_ifs <;> simp +decide [ *, FB.true, FB.false ]

def enforceNotNested_spec (LEN : ℕ)
  (startIdx fieldLen : ZMod p)
  (bracketsDepthMap : Vector (ZMod p) LEN) :
  Bool
:=
  let f := bracketsDepthMap.extract startIdx.val (startIdx + fieldLen).val
  f.all (· = 0)

/-
`enforceNotNested` succeeds iff every bracket-depth value inside the field window
    `[startIdx, startIdx + fieldLen)` is zero.

    The statement as originally written was not provable: the circuit only checks that the *sum* of
    the depth values over the window is zero (`eq0` of a scalar product), whereas the spec
    `enforceNotNested_spec` checks that *every* such value is zero. Over `ZMod p` these differ —
    e.g. a window `[1, p-1]` sums to `0` without being all-zero. We therefore add the
    no-cancellation hypothesis `hbound`, stating that the integer sum of the canonical
    representatives of the depth values in the window is `< p`. This is exactly the invariant
    enjoyed by genuine bracket-depth maps (small non-negative depths), and under it "sums to zero"
    is equivalent to "is all zero", making circuit and spec agree.
-/
lemma enforceNotNested_equiv (LEN) (hlen : LEN ≤ p)
  (startIdx fieldLen : F p)
  (hstart : startIdx.val < LEN)
  (hlt : startIdx.val < startIdx.val + fieldLen.val)
  (hend : startIdx.val + fieldLen.val < 2 ^ Clap.minBits LEN)
  (hw : 2 ^ (Clap.minBits LEN + 1) < p)
  (bracketsDepthMap : Vector (F p) LEN)
  (hbound : ((bracketsDepthMap.extract startIdx.val (startIdx + fieldLen).val).toList.map
      ZMod.val).sum < p) :
  JWT.enforceNotNested LEN startIdx fieldLen bracketsDepthMap =
    Spec.FB.assert (enforceNotNested_spec LEN startIdx fieldLen bracketsDepthMap)
:= by
  convert Option.bind_congr ?_;
  rotate_left;
  use fun a => if Vector.escalarProduct bracketsDepthMap a = 0 then some () else none;
  · unfold eq0; aesop;
  · rw [ arraySelector_equiv LEN startIdx ( startIdx + fieldLen ) hlen hstart ?_ ?_ hw ];
    · simp +decide [ Spec.FB.assert, enforceNotNested_spec ];
      convert zmod_sum_eq_zero_iff ( bracketsDepthMap.extract ( ZMod.val startIdx ) ( ZMod.val ( startIdx + fieldLen ) ) |> Vector.toList ) hbound |> Iff.symm using 1;
      rw [ escalarProduct_arraySelectorSpec_eq ];
      simp +decide [ List.mem_iff_get ];
      split_ifs <;> simp_all +decide [ Fin.forall_iff ];
    · rw [ ZMod.val_add ];
      rw [ Nat.mod_eq_of_lt ] <;> linarith [ pow_succ' 2 ( Clap.minBits LEN ) ];
    · convert hend using 1;
      convert ZMod.val_add_of_lt ( show startIdx.val + fieldLen.val < p from ?_ );
      exact lt_of_lt_of_le hend ( Nat.le_of_lt hw |> le_trans ( Nat.pow_le_pow_right ( by decide ) ( Nat.le_succ _ ) ) )

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

/-- JWT field with an unquoted value (iat). -/
structure UnquotedFieldInput (maxPairLen maxNameLen maxValueLen : ℕ) where
  field      : FString bn254 maxPairLen
  name       : FString bn254 maxNameLen
  value      : FString bn254 maxValueLen
  nameIndex  : F bn254
  colonIndex : F bn254
  valueIndex : F bn254

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
    (fi : UnquotedFieldInput maxKVPairLen maxNameLen maxValueLen)
    (h_name  : maxNameLen  ≤ maxKVPairLen)
    (h_value : maxValueLen ≤ maxKVPairLen)
    (skipChecks  : FB bn254 := 0)
    : Option Unit := do
  -- Delegate shared structural checks
  parseJWTFieldSharedLogic h_name h_value fi.field fi.name fi.value fi.colonIndex fi.valueIndex skipChecks
  let perform : FB bn254 := FB.not skipChecks
  -- Check 1: whitespace in three zones
  -- Zone A: [name_len + 2, colonIndex)  — between closing name-quote and colon
  -- Zone B: [colonIndex + 1, valueIndex)  — between colon and value (no quote around value)
  -- Zone C: [valueIndex + value_len, field_len - 1)  — after value, before terminator
  let zoneA ← arraySelectorComplex maxKVPairLen (fi.name.len + 2) fi.colonIndex
  let zoneB ← arraySelectorComplex maxKVPairLen (fi.colonIndex + 1) fi.valueIndex
  let zoneC ← arraySelectorComplex maxKVPairLen (fi.valueIndex + fi.value.len) (fi.field.len - 1)
  -- Merge zones: inZone[i] = zoneA[i] ∨ zoneB[i] ∨ zoneC[i]
  let inZone := (zoneA.zipWith FB.or zoneB).zipWith FB.or zoneC
  -- For each position in a whitespace zone, the character must be whitespace
  (inZone.zip fi.field.data).toList.forM fun (z, c) ↦ do
    let ws ← F8.isWhitespace c
    F.guardedEq0 perform (z &&& FB.not ws)
  -- Check 2: value must not contain ',', '}', or '"'
  -- valueSelector: 1s at [valueIndex, valueIndex + value_len)
  let valueSel ← arraySelector maxKVPairLen fi.valueIndex (fi.valueIndex + fi.value.len)
  (valueSel.zip fi.field.data).toList.forM fun (sel, c) ↦ do
    let isForbidden := (←F.eq c ',') ||| (←F.eq c '}') ||| (←F.eq c '\"')
    -- If in value range, character must not be forbidden
    F.guardedEq0 perform (sel &&& isForbidden)

/-- JWT field with a quoted value (aud, uid, iss, nonce). -/
structure QuotedFieldInput (maxPairLen maxNameLen maxValueLen : ℕ) where
  field             : FString bn254 maxPairLen
  name              : FString bn254 maxNameLen
  value             : FString bn254 maxValueLen
  fieldStringBodies : PaddedVector FB bn254 maxPairLen
  nameIndex         : F bn254
  colonIndex        : F bn254
  valueIndex        : F bn254

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
    (fi              : QuotedFieldInput maxKVPairLen maxNameLen maxValueLen)
    (h_name  : maxNameLen  ≤ maxKVPairLen)
    (h_value : maxValueLen ≤ maxKVPairLen)
    (skipChecks         : FB bn254 := 0)
    : Option Unit := do
  -- Delegate shared structural checks
  parseJWTFieldSharedLogic h_name h_value fi.field fi.name fi.value fi.colonIndex fi.valueIndex skipChecks
  let perform : FB bn254 := FB.not skipChecks
  -- Check 0: field[value_index - 1] == '"' (opening quote around value)
  let valueFirstQuote ← selectArrayValue fi.field.data (fi.valueIndex - 1)
  F.guardedAssertEq perform valueFirstQuote 34
  -- Check 1: field[value_index + value_len] == '"' (closing quote around value)
  let valueSecondQuote ← selectArrayValue fi.field.data (fi.valueIndex + fi.value.len)
  F.guardedAssertEq perform valueSecondQuote 34
  -- Check 2: whitespace zones + string bodies
  -- Zone A: [name_len + 2, colon_index)  — between closing name-quote and colon
  -- Zone B: [colon_index + 1, value_index - 1)  — between colon and opening value-quote
  -- Zone C: [value_index + value_len + 1, field_len - 1)  — after closing value-quote, before terminator
  let zoneA ← arraySelectorComplex maxKVPairLen (fi.name.len + 2) fi.colonIndex
  let zoneB ← arraySelectorComplex maxKVPairLen (fi.colonIndex + 1) (fi.valueIndex - 1)
  let zoneC ← arraySelectorComplex maxKVPairLen (fi.valueIndex + fi.value.len + 1) (fi.field.len - 1)
  let inZone := (zoneA.zipWith FB.or zoneB).zipWith FB.or zoneC
  -- Name selector: [1, name_len + 1) — name content inside its quotes
  let nameSel ← arraySelector maxKVPairLen 1 (fi.name.len + 1)
  -- Value selector: [valueIndex, valueIndex + value_len) — value content inside its quotes
  let valueSel ← arraySelector maxKVPairLen fi.valueIndex (fi.valueIndex + fi.value.len)
  let nameOrValue := nameSel.zipWith FB.or valueSel
  -- For each position: whitespace zone chars must be whitespace,
  -- and string bodies must match name/value selectors exactly
  (inZone.zip (nameOrValue.zip (fi.fieldStringBodies.data.zip fi.field.data))).toList.forM fun (z, nv, sb, c) ↦ do
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

private def parseCharsASCII (s : String) : FString p s.length := FString.ofString s
private def parseBitString (s : String) : Array (FB p) :=
  s.chars.filter (fun c ↦ c != ' ') |>.map (fun c ↦ if c = '0' then 0 else 1) |>.toArray

private def PaddedVector.toArray {w} : PaddedVector FB p w → Array (FB p)
  | ⟨data, len⟩ => data.toArray.take len.val

private def stringBodiesToArray {w} (input : FString p w) : Option (Array (FB p)) :=
  stringBodies input |>.map PaddedVector.toArray

/- from the Circom docstring
  { asdfsdf "as\"df" }
  00000000000111111000 -/
example :
  let inp      := parseCharsASCII "{ asdfsdf \"as\\\"df\" }"
  let expected := parseBitString  "0000000000 011 1 111 000"
  stringBodiesToArray inp == some expected := by native_decide

/-
  { a "a\"a" } →
  000001111000
-/
example :
  let inp      := parseCharsASCII "{ a \"a\\\"a\" }"
  let expected := parseBitString  "0000 01 1 11 000"
  stringBodiesToArray inp == expected := by native_decide

/-
  "i\i""i" →
  01110010
-/
example :
  let inp      := parseCharsASCII "\"i\\i\"\"i\""
  let expected := parseBitString  " 01 11 0 01 0"
  stringBodiesToArray inp == expected := by native_decide

/-
  "i\"\\\"i" →
  0111111110
-/
example :
  let inp      := parseCharsASCII "\"i\\\"\\\\\\\"i\""
  let expected := parseBitString  " 01 1 1 1 1 1 11 0"
  stringBodiesToArray inp == expected := by native_decide

/-
  """""" →
  000000
-/
example :
  let inp      := parseCharsASCII "\"\"\"\"\"\""
  let expected := parseBitString  " 0 0 0 0 0 0"
  stringBodiesToArray inp == expected := by native_decide

/-
  \"\""i"\"\" →
  00000100000
-/
example :
  let inp      := parseCharsASCII "\\\"\\\"\"i\"\\\"\\\""
  let expected := parseBitString  " 0 0 0 0 01 0 0 0 0 0"
  stringBodiesToArray inp == expected := by native_decide

/-
  \\"\\" →
  000110
-/
example :
  let inp      := parseCharsASCII "\\\\\"\\\\\""
  let expected := parseBitString  " 0 0 0 1 1 0"
  stringBodiesToArray inp == expected := by native_decide

private def br :=
  parseCharsASCII "{he{llo{}world!}}"
example :
  (bracketsMap (p := p) br).map PaddedVector.data == some #v[1, 0, 0, 1, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, -1, -1]
:= by
  native_decide

private def plusMinusOneBr₁ : Vector (F p) 20 :=
  #v[0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, -1]
example :
  bracketsDepthMap plusMinusOneBr₁ == some
    #v[0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0]
:= by
  native_decide

private def plusMinusOneBr₂ : Vector (F p) 10 :=
  #v[1,1,1,1,1,-1,-1,-1,-1,-1]

example : bracketsDepthMap plusMinusOneBr₂ == some #v[0, 0, 1, 2, 3, 3, 2, 1, 0, 0] := by
  native_decide

private def plusMinusOneBr₃ : Vector (F p) 20 :=
  #v[0,1,0,0,0,1,0,1,0,0,0,-1,0,0,-1,0,0,0,0,-1]

example :
  bracketsDepthMap plusMinusOneBr₃ == some #v[0,0,0,0,0,0,1,1,2,2,2,1,1,1,0,0,0,0,0,0]
:= by
  native_decide

example :
  enforceNotNested (p := p) 10 0 2 #v[0, 0, 1, 2, 3, 3, 2, 1, 0, 0] == .some ()
:= by
  native_decide

example : enforceNotNested (p := p) 10 8 10 #v[0, 0, 1, 2, 3, 3, 2, 1, 0, 0] == .some ()
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
  enforceNotNested (p := p) 10 2 4 #v[0, 0, 1, 2, 3, 3, 2, 1, 0, 0] == .none
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
  parseJWTFieldWithUnquotedValue {field, name, value, nameIndex:=0, colonIndex:=3, valueIndex:=4} (by omega) (by omega)
  ) = some () := by native_decide

-- valid: "a":b}   (ending with '}')
example : (do
  let field := strToFS 6 "\"a\":b}"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithUnquotedValue {field, name, value, nameIndex:=0, colonIndex:=3, valueIndex:=4} (by omega) (by omega)
  ) = some () := by native_decide

-- valid: "sub":123,  (multi-char name and numeric value)
example : (do
  let field := strToFS 10 "\"sub\":123,"
  let name  := strToFS 3 "sub"
  let value := strToFS 3 "123"
  parseJWTFieldWithUnquotedValue {field, name, value, nameIndex:=0, colonIndex:=5, valueIndex:=6} (by omega) (by omega)
  ) = some () := by native_decide

-- valid: "alg": RS256,  (single space between colon and value)
example : (do
  let field := strToFS 13 "\"alg\": RS256,"
  let name  := strToFS 3 "alg"
  let value := strToFS 5 "RS256"
  parseJWTFieldWithUnquotedValue {field, name, value, nameIndex:=0, colonIndex:=5, valueIndex:=7} (by omega) (by omega)
  ) = some () := by native_decide

-- valid: "iat":9876}  (numeric value, ending with '}')
example : (do
  let field := strToFS 11 "\"iat\":9876}"
  let name  := strToFS 3 "iat"
  let value := strToFS 4 "9876"
  parseJWTFieldWithUnquotedValue {field, name, value, nameIndex:=0, colonIndex:=5, valueIndex:=6} (by omega) (by omega)
  ) = some () := by native_decide

-- valid: "role": true ,  (spaces on both sides of value)
example : (do
  let field := strToFS 14 "\"role\": true ,"
  let name  := strToFS 4 "role"
  let value := strToFS 4 "true"
  parseJWTFieldWithUnquotedValue {field, name, value, nameIndex:=0, colonIndex:=6, valueIndex:=8} (by omega) (by omega)
  ) = some () := by native_decide

-- Reject: single non-whitespace byte 'X' between name-quote and colon.
-- "a"X:b,  — position 3 is 'X' (ASCII 88), colon at 4.
example : (do
  let field := strToFS 7 "\"a\"X:b,"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithUnquotedValue {field, name, value, nameIndex:=0, colonIndex:=4, valueIndex:=5} (by omega) (by omega)
  ) = none := by native_decide

-- Reject: Exploit 1 — "role"XX:true,
-- Mirrors the SharedLogic Exploit 1 example above.
-- Two garbage bytes between name-quote and colon; SharedLogic accepted this.
example : (do
  let field := strToFS 14 "\"role\"XX:true,"
  let name  := strToFS 4 "role"
  let value := strToFS 4 "true"
  parseJWTFieldWithUnquotedValue {field, name, value, nameIndex:=0, colonIndex:=8, valueIndex:=9} (by omega) (by omega)
  ) = none := by native_decide

-- Reject: value contains ',' — "a":b,,
example : (do
  let field := strToFS 7 "\"a\":b,,"
  let name  := strToFS 1 "a"
  let value := strToFS 2 "b,"
  parseJWTFieldWithUnquotedValue {field, name, value, nameIndex:=0, colonIndex:=3, valueIndex:=4} (by omega) (by omega)
  ) = none := by native_decide

-- Reject: Exploit 2 — "iat":1,"admin":true}
-- Value "1,\"admin\":true" spans the field boundary; contains both ',' and '"'.
example : (do
  let field := strToFS 24 "\"iat\":1,\"admin\":true}"
  let name  := strToFS 3 "iat"
  let value := strToFS 14 "1,\"admin\":true"
  parseJWTFieldWithUnquotedValue {field, name, value, nameIndex:=0, colonIndex:=5, valueIndex:=6} (by omega) (by omega)
  ) = none := by native_decide

-- Reject: value contains '}' — "a":b},
-- A value ending with '}' would be a valid JSON terminator but not a valid unquoted value body.
example : (do
  let field := strToFS 7 "\"a\":b},"
  let name  := strToFS 1 "a"
  let value := strToFS 2 "b}"
  parseJWTFieldWithUnquotedValue {field, name, value, nameIndex:=0, colonIndex:=3, valueIndex:=4} (by omega) (by omega)
  ) = none := by native_decide

-- Reject: value contains '"' — "a":"b",  (quoted value content presented as unquoted)
example : (do
  let field := strToFS 8 "\"a\":\"b\","
  let name  := strToFS 1 "a"
  let value := strToFS 3 "\"b\""
  parseJWTFieldWithUnquotedValue {field, name, value, nameIndex:=0, colonIndex:=3, valueIndex:=4} (by omega) (by omega)
  ) = none := by native_decide

-- Reject: Exploit 3 — "exp":1999999999,
example : (do
  let field := strToFS 18 "\"exp\":1999999999,"
  let name  := strToFS 3 "exp"
  let value := strToFS 1 "1"
  parseJWTFieldWithUnquotedValue {field, name, value, nameIndex:=0, colonIndex:=5, valueIndex:=6} (by omega) (by omega)
  ) = none := by native_decide

example : (do
  let field := strToFS 18 "\"exp\":1999999999,"
  let name  := strToFS 3 "exp"
  let value := strToFS 1 "1"
  parseJWTFieldWithUnquotedValue {field, name, value, nameIndex:=0, colonIndex:=5, valueIndex:=6} (by omega) (by omega) (skipChecks := 1)
  ) = some () := by native_decide

-- Reject: partial value with trailing non-whitespace — "nbf":16000 ,
-- value="160"; characters "00 " end with a space (whitespace) but "00" are digits, not whitespace.
example : (do
  let field := strToFS 13 "\"nbf\":16000 ,"
  let name  := strToFS 3 "nbf"
  let value := strToFS 3 "160"
  parseJWTFieldWithUnquotedValue {field, name, value, nameIndex:=0, colonIndex:=5, valueIndex:=6} (by omega) (by omega)
  ) = none := by native_decide

example : (do
  let field := strToFS 13 "\"nbf\":16000 ,"
  let name  := strToFS 3 "nbf"
  let value := strToFS 3 "160"
  parseJWTFieldWithUnquotedValue {field, name, value, nameIndex:=0, colonIndex:=5, valueIndex:=6} (by omega) (by omega) (skipChecks := 1)
  ) = some () := by native_decide

-- skipChecks = 1 does NOT bypass sub-template constraints: out-of-range indices still fail,
-- matching CIRCOM where sub-template constraints (one-hot encoding) always apply.
example : (do
  let field := strToFS 6 "\"a\":b,"
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithUnquotedValue {field, name, value, nameIndex:=0, colonIndex:=100, valueIndex:=200} (by omega) (by omega) (skipChecks := 1)
  ) = none := by native_decide

-- parseJWTFieldWithQuotedValue tests

-- valid: "a":"b",  (minimal quoted value)
-- field = "a":"b",  →  positions: 0=" 1=a 2=" 3=: 4=" 5=b 6=" 7=,
-- string_bodies:                    0   1   0   0   0   1   0   0
example : (do
  let field := strToFS 8 "\"a\":\"b\","
  let fieldStringBodies : PaddedVector FB p 8 := ⟨#v[0,1,0,0,0,1,0,0], 8⟩
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=3,valueIndex:=5} (by omega) (by omega)
  ) = some () := by native_decide

-- valid: "a":"b"}  (ending with '}')
example : (do
  let field := strToFS 8 "\"a\":\"b\"}"
  let fieldStringBodies : PaddedVector FB p 8 := ⟨#v[0,1,0,0,0,1,0,0], 8⟩
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=3, valueIndex:=5} (by omega) (by omega)
  ) = some () := by native_decide

-- valid: "sub":"abc",  (multi-char name and value)
-- field = "sub":"abc",  →  0=" 1=s 2=u 3=b 4=" 5=: 6=" 7=a 8=b 9=c 10=" 11=,
-- string_bodies:             0   1   1   1   0   0   0   1   1   1    0    0
example : (do
  let field := strToFS 12 "\"sub\":\"abc\","
  let fieldStringBodies : PaddedVector FB p 12 := ⟨#v[0,1,1,1,0,0,0,1,1,1,0,0], 12⟩
  let name  := strToFS 3 "sub"
  let value := strToFS 3 "abc"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=5, valueIndex:=7} (by omega) (by omega)
  ) = some () := by native_decide

-- valid: "email":"ab@c",  (value with special char)
-- field = "email":"ab@c",  → 0=" 1=e 2=m 3=a 4=i 5=l 6=" 7=: 8=" 9=a 10=b 11=@ 12=c 13=" 14=, 15=\0
-- string_bodies:               0   1   1   1   1   1   0   0   0   1    1    1    1    0    0    0
example : (do
  let field := strToFS 16 "\"email\":\"ab@c\","
  let fieldStringBodies : PaddedVector FB p 16 := ⟨#v[0,1,1,1,1,1,0,0,0,1,1,1,1,0,0,0], 16⟩
  let name  := strToFS 5 "email"
  let value := strToFS 4 "ab@c"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=7, valueIndex:=9} (by omega) (by omega)
  ) = some () := by native_decide

-- valid: "k": "v" ,  (spaces around quoted value and after)
-- field = "k": "v" ,  →  0=" 1=k 2=" 3=: 4=SP 5=" 6=v 7=" 8=SP 9=,
-- string_bodies:          0    1   0   0   0    0   1   0   0    0
example : (do
  let field := strToFS 10 "\"k\": \"v\" ,"
  let fieldStringBodies : PaddedVector FB p 10 := ⟨#v[0,1,0,0,0,0,1,0,0,0], 10⟩
  let name  := strToFS 1 "k"
  let value := strToFS 1 "v"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=3, valueIndex:=6} (by omega) (by omega)
  ) = some () := by native_decide

-- valid: "k":"v"}  (ending with '}')
example : (do
  let field := strToFS 8 "\"k\":\"v\"}"
  let fieldStringBodies : PaddedVector FB p 8 := ⟨#v[0,1,0,0,0,1,0,0], 8⟩
  let name  := strToFS 1 "k"
  let value := strToFS 1 "v"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=3, valueIndex:=5} (by omega) (by omega)
  ) = some () := by native_decide

-- Reject: opening value quote missing — "a":b",
-- field[value_index - 1] = field[3] = ':' ≠ '"'
example : (do
  let field := strToFS 7 "\"a\":b\","
  let fieldStringBodies : PaddedVector FB p 7 := ⟨#v[0,1,0,0,1,0,0], 7⟩
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=3, valueIndex:=4} (by omega) (by omega)
  ) = none := by native_decide

-- Reject: closing value quote missing — "a":"b,
-- field[value_index + value_len] = field[5] = ',' ≠ '"'
example : (do
  let field := strToFS 7 "\"a\":\"b,"
  let fieldStringBodies : PaddedVector FB p 7 := ⟨#v[0,1,0,0,0,1,0], 7⟩
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=3, valueIndex:=5} (by omega) (by omega)
  ) = none := by native_decide

-- Reject: non-whitespace between name-quote and colon — "a"X:"b",
-- string_bodies: 0 1 0 0 0 0 1 0 0
example : (do
  let field := strToFS 9 "\"a\"X:\"b\","
  let fieldStringBodies : PaddedVector FB p 9 := ⟨#v[0,1,0,0,0,0,1,0,0], 9⟩
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=4, valueIndex:=6} (by omega) (by omega)
  ) = none := by native_decide

-- Reject: non-whitespace between colon and opening value quote — "a":X"b",
-- string_bodies: 0 1 0 0 0 0 1 0 0
example : (do
  let field := strToFS 9 "\"a\":X\"b\","
  let fieldStringBodies : PaddedVector FB p 9 := ⟨#v[0,1,0,0,0,0,1,0,0], 9⟩
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=3, valueIndex:=6} (by omega) (by omega)
  ) = none := by native_decide

-- Reject: wrong string bodies — all zeros (should have 1s at name and value positions)
example : (do
  let field := strToFS 8 "\"a\":\"b\","
  let fieldStringBodies : PaddedVector FB p 8 := ⟨#v[0,0,0,0,0,0,0,0], 8⟩
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=3, valueIndex:=5} (by omega) (by omega)
  ) = none := by native_decide

-- Reject: wrong string bodies — all ones
example : (do
  let field := strToFS 8 "\"a\":\"b\","
  let fieldStringBodies : PaddedVector FB p 8 := ⟨#v[1,1,1,1,1,1,1,1], 8⟩
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=3, valueIndex:=5} (by omega) (by omega)
  ) = none := by native_decide

example : (do
  let field := strToFS 8 "\"a\":\"b\","
  let fieldStringBodies : PaddedVector FB p 8 := ⟨#v[1,1,1,1,1,1,1,1], 8⟩
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=3, valueIndex:=5} (by omega) (by omega) (skipChecks := 1)
  ) = some () := by native_decide

-- Reject: non-whitespace after closing value quote — "a":"b"X,
-- string_bodies: 0 1 0 0 0 1 0 0 0
example : (do
  let field := strToFS 9 "\"a\":\"b\"X,"
  let fieldStringBodies : PaddedVector FB p 9 := ⟨#v[0,1,0,0,0,1,0,0,0], 9⟩
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=3, valueIndex:=5} (by omega) (by omega)
  ) = none := by native_decide

example : (do
  let field := strToFS 9 "\"a\":\"b\"X,"
  let fieldStringBodies : PaddedVector FB p 9 := ⟨#v[0,1,0,0,0,1,0,0,0], 9⟩
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=3, valueIndex:=5} (by omega) (by omega) (skipChecks := 1)
  ) = some () := by native_decide

example : (do
  let field := strToFS 9 "\"a\":\"b\"X,"
  let fieldStringBodies : PaddedVector FB p 9 := ⟨#v[0,1,0,0,0,1,0,0,0], 9⟩
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=3, valueIndex:=5} (by omega) (by omega) (skipChecks := 1)
  ) = some () := by native_decide

-- skipChecks = 1 does NOT bypass sub-template constraints: out-of-range indices still fail,
-- matching CIRCOM where sub-template constraints (one-hot encoding) always apply.
example : (do
  let field := strToFS 6 "\"a\":b,"
  let fieldStringBodies : PaddedVector FB p 6 := ⟨#v[0,0,0,0,0,0], 6⟩
  let name  := strToFS 1 "a"
  let value := strToFS 1 "b"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=100, valueIndex:=200} (by omega) (by omega) (skipChecks := 1)
  ) = none := by native_decide

-- valid: "k":"ab cd",  (whitespace inside quoted value)
-- field = "k":"ab cd",  →  0=" 1=k 2=" 3=: 4=" 5=a 6=b 7=SP 8=c 9=d 10=" 11=,
-- string_bodies:            0    1   0   0   0   1   1   1    1   1    0    0
example : (do
  let field := strToFS 12 "\"k\":\"ab cd\","
  let fieldStringBodies : PaddedVector FB p 12 := ⟨#v[0,1,0,0,0,1,1,1,1,1,0,0], 12⟩
  let name  := strToFS 1 "k"
  let value := strToFS 5 "ab cd"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=3, valueIndex:=5} (by omega) (by omega)
  ) = some () := by native_decide

-- valid: "k":"a\"b",  (escaped quote inside quoted value)
-- field = "k":"a\"b",  →  0=" 1=k 2=" 3=: 4=" 5=a 6=\" 7=" 8=b 9=" 10=,
-- string_bodies:            0   1   0   0   0   1   1   1   1   0    0
-- The \" at positions 6-7 is an escaped quote, so stringBodies stays open through it.
-- value = a\"b (4 chars), value_index=5, value_sel=[5,9)
example : (do
  let field := strToFS 11 "\"k\":\"a\\\"b\","
  let fieldStringBodies : PaddedVector FB p 11 := ⟨#v[0,1,0,0,0,1,1,1,1,0,0], 11⟩
  let name  := strToFS 1 "k"
  let value := strToFS 4 "a\\\"b"
  parseJWTFieldWithQuotedValue {field, name, value, fieldStringBodies, nameIndex:=0, colonIndex:=3, valueIndex:=5} (by omega) (by omega)
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
