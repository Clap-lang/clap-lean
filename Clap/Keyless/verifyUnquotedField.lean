import Clap.RandomOracle.HashFn
import Clap.Lang.Poseidon.Computes
import Clap.Lang.Data.FString.asciiDigitsToScalar
import Clap.Lang.Data.FString.isSubstring
import Clap.Lang.Data.JWT.stringBodies
import Clap.Lang.Data.JWT.enforceNotNested
import Clap.Lang.Data.JWT.parseJWTFieldWithUnquotedValue
import Clap.Lang.Core.FB.not
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Keyless.Input
import Clap.Lang.Poseidon.Poseidon

open Clap Lang FString FArray FVec Primes

/-- Verify an unquoted JWT field: substring check, not-nested check, field parsing.
    Unlike `verifyQuotedField`, this does NOT perform a full string_bodies substring
    check. Instead, CIRCOM does a point check that the field does not start inside a
    string body (`SelectArrayValue(string_bodies, index) === 0`). -/
def verifyUnquotedField {maxPairLen maxNameLen maxValueLen : ℕ}
    (h_name : maxNameLen ≤ maxPairLen)
    (h_value : maxValueLen ≤ maxPairLen)
    (h_pair : maxPairLen ≤ MAX_JWT_PAYLOAD_LEN)
    (json : JSONStructure bn254)
    (inp : JWT.UnquotedFieldInput bn254 maxPairLen maxNameLen maxValueLen) :
    ClapM bn254 Unit
:= do
  -- Assert field is a substring of the decoded JWT payload
  FString.assertIsSubstring h_pair json.payload.data json.payloadHash
    inp.field
    inp.nameIndex
  -- Assert field is not inside nested brackets
  enforceNotNested inp.nameIndex inp.field.len json.bracketsDepthMap
  -- Assert field does not start inside a string body — CIRCOM: start_char === 0
  eq0 (← selectArrayValue _ json.stringBodies.data inp.nameIndex)
  -- Parse the field structure with unquoted value
  parseJWTFieldWithUnquotedValue inp h_name h_value (← FB.ofBool false)

namespace verifyUnquotedField

open Poseidon RandomOracle Primes FiatShamir

-- Poseidon is opaque to this proof (it sits beneath `assertIsSubstring`/`hashBytesToField`),
-- as in `Data/HashToField/hashElemsToField.lean` and `Keyless/computeJSONStructure.lean`.
attribute [local irreducible] Clap.Lang.Poseidon.poseidonBN254

lemma convertsM
  {H : HashFn}
  (h_H : Computes H)
  {state : ClapMState bn254}
  -- Circuit arguments
  {maxKVPairLen maxNameLen maxValueLen : ℕ}
  (h_name_len_lt  : maxNameLen  ≤ maxKVPairLen)
  (h_value_len_lt : maxValueLen ≤ maxKVPairLen)
  (h_pair : maxKVPairLen ≤ MAX_JWT_PAYLOAD_LEN)
  (h_len_bound    : maxKVPairLen ≤ 1953)
  {json : JSONStructure bn254}
  {unquoted : JWT.UnquotedFieldInput bn254 maxKVPairLen maxNameLen maxValueLen}
  -- Ideal values for `unquoted : JWT.UnquotedFieldInput`
  {field_vals : Vector (ZMod bn254) maxKVPairLen}
  {field_len : ZMod bn254}
  {name_vals : Vector (ZMod bn254) maxNameLen}
  {name_len : ZMod bn254}
  {value_vals : Vector (ZMod bn254) maxValueLen}
  {value_len : ZMod bn254}
  {colon_index_val value_index_val name_index_val : ZMod bn254}
  -- Ideal values for `json : JSONStructure`
  {payload_val : String}
  {payloadHash_val : ZMod bn254}
  {stringBodies_val : Vector Bool MAX_JWT_PAYLOAD_LEN}
  {bracketsDepthMap_val : Vector (ZMod bn254) MAX_JWT_PAYLOAD_LEN}
  -- Conversion hypotheses for `json : JWT.QuotedFieldInput`
  (h_field_val : Converts FVec.conversion state unquoted.field.data field_vals)
  (h_field_len : Converts F.conversion state unquoted.field.len field_len)
  (h_name_val : Converts FVec.conversion state unquoted.name.data name_vals)
  (h_name_len : Converts F.conversion state unquoted.name.len name_len)
  (h_value_val : Converts FVec.conversion state unquoted.value.data value_vals)
  (h_value_len : Converts F.conversion state unquoted.value.len value_len)
  (h_ci : Converts F.conversion state unquoted.colonIndex colon_index_val)
  (h_vi : Converts F.conversion state unquoted.valueIndex value_index_val)
  (h_ni : Converts F.conversion state unquoted.nameIndex name_index_val)
  -- Conversion hypotheses for `unquoted : JSONStructure`
  (h_payload          : Converts FString.conversion state json.payload payload_val)
  (h_payloadHash      : Converts F.conversion state json.payloadHash payloadHash_val)
  (h_stringBodies     : Converts FArray.conversion state json.stringBodies.data stringBodies_val)
  (h_bracketsDepthMap : Converts FVec.conversion state json.bracketsDepthMap bracketsDepthMap_val)
  -- Range bounds (`w := 20` is hard-coded in the body)
  (h_name_len_w : name_len.val < 2 ^ 20)
  (h_colon_index_w : colon_index_val.val < 2 ^ 20)
  (h_value_index_w : value_index_val.val < 2 ^ 20)
  (h_field_len_w : field_len.val < 2 ^ 20)
  (h_sum_len_w : (name_len + value_len).val < 2 ^ 20)
  -- Required by `parseJWTFieldWithUnquotedValue.convertsM`
  (h_value_window : (value_index_val + value_len).val ≤ maxKVPairLen) :
  let payloadV := encodeV (p := bn254) MAX_JWT_PAYLOAD_LEN payload_val
  ConvertsM FUnit.conversion
    (verifyUnquotedField h_name_len_lt h_value_len_lt h_pair json unquoted)
    state
    ()
    ( ( (∀ i : Fin maxKVPairLen, field_vals[i].val < 2 ^ 8) ∧
        (name_index_val + field_len).val < 2 ^ minBits' MAX_JWT_PAYLOAD_LEN ∧
        name_index_val.val < MAX_JWT_PAYLOAD_LEN ∧
        name_index_val.val < (name_index_val + field_len).val
      ) ∧
      isSubstring.accepts H payloadV payloadHash_val field_vals field_len name_index_val = true ∧
      ( name_index_val.val < MAX_JWT_PAYLOAD_LEN ∧
        (stringBodies_val.map fun b ↦ if b then (1 : ZMod bn254) else 0).getD name_index_val.val 0 = 0
      ) ∧
      (bracketsDepthMap_val.extract name_index_val.val (name_index_val + field_len).val).sum = 0 ∧
      ( (∀ i : Fin maxNameLen, name_vals[i].val < 2^8) ∧
        (∀ i : Fin maxValueLen, value_vals[i].val < 2^8) ∧

        name_len.val + 1 < maxKVPairLen ∧
        colon_index_val.val < maxKVPairLen ∧
        (field_len - 1).val < maxKVPairLen ∧

        0 < name_len.val ∧

        (value_index_val + value_len).val < 2 ^ minBits' maxKVPairLen ∧
        value_index_val.val < maxKVPairLen ∧
        value_index_val.val < (value_index_val + value_len).val ∧
        0 < value_len.val ∧

        parseJWTFieldWithUnquotedValue.parses H field_vals field_len name_vals name_len value_vals value_len
          colon_index_val
          value_index_val
          false
      )
    )
:= by
  intro payloadV
  have h_n_bn254 : MAX_JWT_PAYLOAD_LEN < bn254 := by decide
  have hw_minBits : 2 ^ (minBits' MAX_JWT_PAYLOAD_LEN + 1) < bn254 := by
    have h11 : minBits' MAX_JWT_PAYLOAD_LEN ≤ 11 := by
      unfold minBits'
      split
      · omega
      · rename_i hx
        have hx11 : MAX_JWT_PAYLOAD_LEN < 2 ^ 11 := by decide
        have := (Nat.log2_lt hx).mpr hx11
        omega
    have h2 : (2:ℕ) ^ (minBits' MAX_JWT_PAYLOAD_LEN + 1) ≤ 2 ^ 12 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4096 : (2:ℕ) ^ 12 < bn254 := by decide
    omega
  unfold verifyUnquotedField
  have hFact1 := assertIsSubstring.convertsM h_H h_pair
    (FString.converts_data h_payload) h_payloadHash h_field_val h_field_len h_ni
    h_len_bound h_n_bn254 hw_minBits
  replace h_payloadHash := converts_skip hFact1 h_payloadHash
  replace h_stringBodies := converts_skip hFact1 h_stringBodies
  replace h_field_val := converts_skip hFact1 h_field_val
  replace h_ni := converts_skip hFact1 h_ni
  replace h_field_len := converts_skip hFact1 h_field_len
  replace h_bracketsDepthMap := converts_skip hFact1 h_bracketsDepthMap
  replace h_name_val := converts_skip hFact1 h_name_val
  replace h_name_len := converts_skip hFact1 h_name_len
  replace h_value_val := converts_skip hFact1 h_value_val
  replace h_value_len := converts_skip hFact1 h_value_len
  replace h_ci := converts_skip hFact1 h_ci
  replace h_vi := converts_skip hFact1 h_vi
  have hFact2 := enforceNotNested.convertsM h_ni h_field_len h_bracketsDepthMap
    h_n_bn254 hw_minBits
  replace h_ni := converts_skip hFact2 h_ni
  replace h_field_len := converts_skip hFact2 h_field_len
  replace h_stringBodies := converts_skip hFact2 h_stringBodies
  replace h_field_val := converts_skip hFact2 h_field_val
  replace h_name_val := converts_skip hFact2 h_name_val
  replace h_name_len := converts_skip hFact2 h_name_len
  replace h_value_val := converts_skip hFact2 h_value_val
  replace h_value_len := converts_skip hFact2 h_value_len
  replace h_ci := converts_skip hFact2 h_ci
  replace h_vi := converts_skip hFact2 h_vi
  have hSel := selectArrayValue.convertsM h_ni
    (FVec.converts_of_FArray_converts h_stringBodies) h_n_bn254
  -- Propagate through `hSel` then `eq0` *separately*, rather than through one combined fact for
  -- `selectArrayValue … >>= eq0` — see the note by `hStateG` below for why the distributed,
  -- right-associated state is needed downstream instead of the left-grouped bind-level one.
  replace h_field_val := converts_skip hSel h_field_val
  replace h_field_len := converts_skip hSel h_field_len
  replace h_name_val := converts_skip hSel h_name_val
  replace h_name_len := converts_skip hSel h_name_len
  replace h_value_val := converts_skip hSel h_value_val
  replace h_value_len := converts_skip hSel h_value_len
  replace h_ci := converts_skip hSel h_ci
  replace h_vi := converts_skip hSel h_vi
  have hEq0 := eq0.convertsM hSel.result
  replace h_field_val := converts_skip hEq0 h_field_val
  replace h_field_len := converts_skip hEq0 h_field_len
  replace h_name_val := converts_skip hEq0 h_name_val
  replace h_name_len := converts_skip hEq0 h_name_len
  replace h_value_val := converts_skip hEq0 h_value_val
  replace h_value_len := converts_skip hEq0 h_value_len
  replace h_ci := converts_skip hEq0 h_ci
  replace h_vi := converts_skip hEq0 h_vi
  -- Make the post-stage-3 state opaque. Left as a literal nested `.getState` term, elaborating
  -- `parseJWTFieldWithUnquotedValue.convertsM` below forces `whnf` to unfold
  -- `selectArrayValue`/`eq0`/`enforceNotNested`/`assertIsSubstring` while unifying every sibling
  -- hypothesis's `state` argument against it, which times out. `subst` restores the concrete term
  -- afterward — pure substitution, no further unification needed.
  generalize hStateG :
    (eq0
      ((selectArrayValue MAX_JWT_PAYLOAD_LEN json.stringBodies.data unquoted.nameIndex).getResult
        ((enforceNotNested unquoted.nameIndex unquoted.field.len json.bracketsDepthMap).getState
            ((assertIsSubstring h_pair json.payload.data json.payloadHash unquoted.field
                  unquoted.nameIndex).getState
              state)).numAlloc
        ((enforceNotNested unquoted.nameIndex unquoted.field.len json.bracketsDepthMap).getState
            ((assertIsSubstring h_pair json.payload.data json.payloadHash unquoted.field
                  unquoted.nameIndex).getState
              state)).σ)).getState
      ((selectArrayValue MAX_JWT_PAYLOAD_LEN json.stringBodies.data unquoted.nameIndex).getState
        ((enforceNotNested unquoted.nameIndex unquoted.field.len json.bracketsDepthMap).getState
          ((assertIsSubstring h_pair json.payload.data json.payloadHash unquoted.field unquoted.nameIndex).getState
            state)))
    = stateG at h_field_val h_field_len h_name_val h_name_len h_value_val h_value_len h_ci h_vi
  have hOfBool := FB.ofBool.convertsM (p := bn254) (b := false) (state := stateG)
  replace h_field_val := converts_skip hOfBool h_field_val
  replace h_field_len := converts_skip hOfBool h_field_len
  replace h_name_val := converts_skip hOfBool h_name_val
  replace h_name_len := converts_skip hOfBool h_name_len
  replace h_value_val := converts_skip hOfBool h_value_val
  replace h_value_len := converts_skip hOfBool h_value_len
  replace h_ci := converts_skip hOfBool h_ci
  replace h_vi := converts_skip hOfBool h_vi
  have hFact4 := parseJWTFieldWithUnquotedValue.convertsM h_H h_name_len_lt h_value_len_lt
    h_field_val h_field_len h_name_val h_name_len h_value_val h_value_len
    h_ci h_vi hOfBool.result h_name_len_w h_colon_index_w h_value_index_w h_field_len_w
    h_sum_len_w h_len_bound h_value_window
  have hFact4' := convertsM_of_convertsM hFact4 rfl ⟨fun h _ ↦ h, fun h ↦ h trivial⟩
  have hStep4 := convertsM_bind (function := fun x ↦ parseJWTFieldWithUnquotedValue unquoted
    h_name_len_lt h_value_len_lt x) hOfBool hFact4' (fun _ ↦ trivial)
  subst stateG
  -- `do let x ← selectArrayValue …; eq0 x; let y ← FB.ofBool false; parse … y` right-associates
  -- as `selectArrayValue … >>= fun x ↦ (eq0 x >>= fun _ ↦ (FB.ofBool false >>= fun y ↦ parse … y))`.
  -- Pairing `selectArrayValue … >>= eq0` and `FB.ofBool false >>= parse` as two *separate* slots
  -- (e.g. via a generic 4-way bind helper) instead groups the first two left, as
  -- `(selectArrayValue … >>= eq0) >>= fun _ ↦ …` — propositionally equal by `bind_assoc`, but not
  -- the same term as the goal. Build the tail bottom-up with explicit continuations instead, to
  -- match the true right-associated shape exactly.
  have hRest := convertsM_bind_and (function := fun x ↦
      eq0 x >>= fun _ ↦ FB.ofBool false >>= fun y ↦
        parseJWTFieldWithUnquotedValue unquoted h_name_len_lt h_value_len_lt y)
    hSel
    (convertsM_bind_and (function := fun _ ↦ FB.ofBool false >>= fun y ↦
        parseJWTFieldWithUnquotedValue unquoted h_name_len_lt h_value_len_lt y)
      hEq0
      hStep4)
  have hWhole := convertsM_bind_and (function := fun _ ↦
      enforceNotNested unquoted.nameIndex unquoted.field.len json.bracketsDepthMap >>= fun _ ↦
        selectArrayValue MAX_JWT_PAYLOAD_LEN json.stringBodies.data unquoted.nameIndex >>= fun x ↦
          eq0 x >>= fun _ ↦ FB.ofBool false >>= fun y ↦
            parseJWTFieldWithUnquotedValue unquoted h_name_len_lt h_value_len_lt y)
    hFact1
    (convertsM_bind_and (function := fun _ ↦
        selectArrayValue MAX_JWT_PAYLOAD_LEN json.stringBodies.data unquoted.nameIndex >>= fun x ↦
          eq0 x >>= fun _ ↦ FB.ofBool false >>= fun y ↦
            parseJWTFieldWithUnquotedValue unquoted h_name_len_lt h_value_len_lt y)
      hFact2
      hRest)
  refine convertsM_of_convertsM hWhole rfl ?_
  constructor
  · rintro ⟨⟨hblock1, haccepts⟩, ⟨-, -, -, hsum0⟩, hCsel, hCeq0, hFieldByte, hC4rest⟩
    exact ⟨hblock1, haccepts, ⟨hCsel, hCeq0⟩, hsum0, hC4rest⟩
  · rintro ⟨hblock1, haccepts, ⟨hCsel, hCeq0⟩, hsum0, hC4rest⟩
    obtain ⟨hAbyte, hw1, hw2, hw3⟩ := hblock1
    exact ⟨⟨⟨hAbyte, hw1, hw2, hw3⟩, haccepts⟩, ⟨hw1, hw2, hw3, hsum0⟩, hCsel, hCeq0, hAbyte, hC4rest⟩

theorem sound
  {payloadLen fieldLen nameLen valueLen nameIndex : ℕ}
  {payload field name value : String}
  {colonIndex valueIndex : ZMod bn254}
  {payloadHash : ZMod bn254}
  (h_payload_len : payload.length ≤ payloadLen)
  (h_field_len : field.length ≤ fieldLen)
  (h_name_len : name.length ≤ nameLen)
  (h_value_len : value.length ≤ valueLen)
  (h_field_nonempty : 0 < field.length)
  (h_name_nonempty : 0 < name.length)
  (h_value_nonempty : 0 < value.length)
  (h_nameIndex : nameIndex < payloadLen)
  (h_nF_name : 1 < fieldLen)
  (h_valueIndex : valueIndex.val < fieldLen)
  (h_sum : payloadLen + fieldLen < bn254)
  (h_sum_name : fieldLen + nameLen < bn254)
  (h_sum_value : fieldLen + valueLen < bn254)
  (hc₁ : ∀ c ∈ payload.toList, c.toNat < 256)
  (hc₂ : ∀ c ∈ field.toList, 0 < c.toNat ∧ c.toNat < 256)
  (hc₃ : ∀ c ∈ name.toList, 0 < c.toNat ∧ c.toNat < 256)
  (hc₄ : ∀ c ∈ value.toList, 0 < c.toNat ∧ c.toNat < 256)
  (h_bad₁ :
    -- For `isSubstring.accepts`
    ¬ nameIndex + field.length ≤ payload.length ∨
    ¬ field.toList <+: payload.toList.drop nameIndex ∨
    -- For `parseJWTFieldWithUnquotedValue.parses`
    ¬ (1 + name.length ≤ field.length ∧ name.toList <+: field.toList.drop 1) ∨
    ¬ (valueIndex.val + value.length ≤ field.length ∧
        value.toList <+: field.toList.drop valueIndex.val
      )
  ) :
  randomOracle.toOuterMeasure
    {f |
      isSubstring.accepts (Query.toHashFn f) (encodeV payloadLen payload) payloadHash
        (encodeV fieldLen field)
        field.length
        nameIndex
        ∧
      parseJWTFieldWithUnquotedValue.parses (Query.toHashFn f)
        (encodeV fieldLen field) field.length
        (encodeV nameLen name)
        name.length
        (encodeV valueLen value)
        value.length
        colonIndex
        valueIndex
        false
    } ≤
      ((max (payloadLen - 1 + (fieldLen - 1) + 25) (fieldLen - 1 + (max nameLen valueLen - 1) + 50)
        : ℕ) : ENNReal) / bn254
:= by
  rcases h_bad₁ with h1 | h2 | h3 | h4
  · have h_sub :
        {f |
          isSubstring.accepts (Query.toHashFn f) (encodeV payloadLen payload) payloadHash
            (encodeV fieldLen field) field.length nameIndex ∧
          parseJWTFieldWithUnquotedValue.parses (Query.toHashFn f)
            (encodeV fieldLen field) field.length (encodeV nameLen name) name.length
            (encodeV valueLen value) value.length colonIndex valueIndex false} ⊆
        {f | isSubstring.accepts (Query.toHashFn f) (encodeV payloadLen payload) payloadHash
              (encodeV fieldLen field) field.length nameIndex = true} :=
      fun f hf => hf.1
    refine (MeasureTheory.measure_mono h_sub).trans ?_
    refine (isSubstring.sound (n := payloadLen) (m := fieldLen) (s := nameIndex) payloadHash
      h_payload_len h_field_len h_field_nonempty h_nameIndex h_sum hc₁ hc₂
      (not_and_or.mpr (Or.inl h1))).trans (ENNReal.div_le_div_right ?_ _)
    exact_mod_cast
      (show payloadLen - 1 + (fieldLen - 1) + 25 ≤
          max (payloadLen - 1 + (fieldLen - 1) + 25) (fieldLen - 1 + (max nameLen valueLen - 1) + 50)
        by omega)
  · have h_sub :
        {f |
          isSubstring.accepts (Query.toHashFn f) (encodeV payloadLen payload) payloadHash
            (encodeV fieldLen field) field.length nameIndex ∧
          parseJWTFieldWithUnquotedValue.parses (Query.toHashFn f)
            (encodeV fieldLen field) field.length (encodeV nameLen name) name.length
            (encodeV valueLen value) value.length colonIndex valueIndex false} ⊆
        {f | isSubstring.accepts (Query.toHashFn f) (encodeV payloadLen payload) payloadHash
              (encodeV fieldLen field) field.length nameIndex = true} :=
      fun f hf => hf.1
    refine (MeasureTheory.measure_mono h_sub).trans ?_
    refine (isSubstring.sound (n := payloadLen) (m := fieldLen) (s := nameIndex) payloadHash
      h_payload_len h_field_len h_field_nonempty h_nameIndex h_sum hc₁ hc₂
      (not_and_or.mpr (Or.inr h2))).trans (ENNReal.div_le_div_right ?_ _)
    exact_mod_cast
      (show payloadLen - 1 + (fieldLen - 1) + 25 ≤
          max (payloadLen - 1 + (fieldLen - 1) + 25) (fieldLen - 1 + (max nameLen valueLen - 1) + 50)
        by omega)
  · have h_sub :
        {f |
          isSubstring.accepts (Query.toHashFn f) (encodeV payloadLen payload) payloadHash
            (encodeV fieldLen field) field.length nameIndex ∧
          parseJWTFieldWithUnquotedValue.parses (Query.toHashFn f)
            (encodeV fieldLen field) field.length (encodeV nameLen name) name.length
            (encodeV valueLen value) value.length colonIndex valueIndex false} ⊆
        {f | parseJWTFieldWithUnquotedValue.parses (Query.toHashFn f)
              (encodeV fieldLen field) field.length (encodeV nameLen name) name.length
              (encodeV valueLen value) value.length colonIndex valueIndex false} :=
      fun f hf => hf.2
    refine (MeasureTheory.measure_mono h_sub).trans ?_
    refine (parseJWTFieldWithUnquotedValue.sound field name value colonIndex valueIndex
      h_field_len h_name_len h_value_len h_name_nonempty h_value_nonempty h_nF_name h_valueIndex
      h_sum_name h_sum_value (fun c hc => (hc₂ c hc).2) hc₃ hc₄
      (Or.inl h3)).trans (ENNReal.div_le_div_right ?_ _)
    exact_mod_cast
      (show fieldLen - 1 + (max nameLen valueLen - 1) + 50 ≤
          max (payloadLen - 1 + (fieldLen - 1) + 25) (fieldLen - 1 + (max nameLen valueLen - 1) + 50)
        by omega)
  · have h_sub :
        {f |
          isSubstring.accepts (Query.toHashFn f) (encodeV payloadLen payload) payloadHash
            (encodeV fieldLen field) field.length nameIndex ∧
          parseJWTFieldWithUnquotedValue.parses (Query.toHashFn f)
            (encodeV fieldLen field) field.length (encodeV nameLen name) name.length
            (encodeV valueLen value) value.length colonIndex valueIndex false} ⊆
        {f | parseJWTFieldWithUnquotedValue.parses (Query.toHashFn f)
              (encodeV fieldLen field) field.length (encodeV nameLen name) name.length
              (encodeV valueLen value) value.length colonIndex valueIndex false} :=
      fun f hf => hf.2
    refine (MeasureTheory.measure_mono h_sub).trans ?_
    refine (parseJWTFieldWithUnquotedValue.sound field name value colonIndex valueIndex
      h_field_len h_name_len h_value_len h_name_nonempty h_value_nonempty h_nF_name h_valueIndex
      h_sum_name h_sum_value (fun c hc => (hc₂ c hc).2) hc₃ hc₄
      (Or.inr h4)).trans (ENNReal.div_le_div_right ?_ _)
    exact_mod_cast
      (show fieldLen - 1 + (max nameLen valueLen - 1) + 50 ≤
          max (payloadLen - 1 + (fieldLen - 1) + 25) (fieldLen - 1 + (max nameLen valueLen - 1) + 50)
        by omega)

theorem complete
  {payloadLen fieldLen nameLen valueLen nameIndex : ℕ}
  {payload field name value : String}
  {colonIndex valueIndex : ZMod bn254}
  {payloadHash : ZMod bn254}
  (h_payload_len : payload.length ≤ payloadLen)
  (h_field_len : field.length ≤ fieldLen)
  (h_name_len : name.length ≤ nameLen)
  (h_value_len : value.length ≤ valueLen)
  (h_field_nonempty : 0 < field.length)
  (h_name_nonempty : 0 < name.length)
  (h_value_nonempty : 0 < value.length)
  (h_nF_name : 1 < fieldLen)
  (h_sum : payloadLen + fieldLen < bn254)
  (h_sum_name : fieldLen + nameLen < bn254)
  (h_sum_value : fieldLen + valueLen < bn254)
  (hc₁ : ∀ c ∈ payload.toList, c.toNat < 256)
  (hc₂ : ∀ c ∈ field.toList, 0 < c.toNat ∧ c.toNat < 256)
  (hc₃ : ∀ c ∈ name.toList, 0 < c.toNat ∧ c.toNat < 256)
  (hc₄ : ∀ c ∈ value.toList, 0 < c.toNat ∧ c.toNat < 256)
  -- For `isSubstring.accepts`
  (h_fit : nameIndex + field.length ≤ payload.length)
  (h_pre : field.toList <+: payload.toList.drop nameIndex)
  -- For `parseJWTFieldWithUnquotedValue.parses`
  (h_fit_name : 1 + name.length ≤ field.length)
  (h_pre_name : name.toList <+: field.toList.drop 1)
  (h_fit_val : valueIndex.val + value.length ≤ field.length)
  (h_pre_val : value.toList <+: field.toList.drop valueIndex.val)
  (h_colon_order : name.length < colonIndex.val)
  (h_value_order : colonIndex.val < valueIndex.val)
  (h_open_quote : field.toList[0]? = some '\"')
  (h_close_quote : field.toList[name.length + 1]? = some '\"')
  (h_colon : field.toList[colonIndex.val]? = some ':')
  (h_last_char : field.toList[field.length - 1]? = some ',' ∨
    field.toList[field.length - 1]? = some '}')
  (h_ws_zones : ∀ i,
    name.length + 2 ≤ i ∧ i < colonIndex.val ∨
    colonIndex.val + 1 ≤ i ∧ i < valueIndex.val ∨
    valueIndex.val + value.length ≤ i ∧ i < field.length - 1 →
    (field.toList[i]?.elim false (isWs ∘ Char.toNat) : Prop)
  )
  (h_no_forbidden : ∀ i,
    valueIndex.val ≤ i ∧ i < valueIndex.val + value.length →
        field.toList[i]?.elim false (· ∉ [',', '}', '"'])
  )
  :
  randomOracle.toOuterMeasure
    {f |
      ¬ isSubstring.accepts (Query.toHashFn f) (encodeV payloadLen payload) payloadHash
        (encodeV fieldLen field)
        field.length
        nameIndex
        ∨
      ¬ parseJWTFieldWithUnquotedValue.parses (Query.toHashFn f)
        (encodeV fieldLen field) field.length
        (encodeV nameLen name)
        name.length
        (encodeV valueLen value)
        value.length
        colonIndex
        valueIndex
        false
    } ≤
      ((payloadLen - 1 + 25 + (2 * (fieldLen - 1) + 100) : ℕ) : ENNReal) / bn254
:= by
  have hA : randomOracle.toOuterMeasure
      {f | ¬ isSubstring.accepts (Query.toHashFn f) (encodeV payloadLen payload) payloadHash
        (encodeV fieldLen field) field.length nameIndex} ≤
      (((payloadLen - 1) + 25 : ℕ) : ENNReal) / bn254 := by
    have h := isSubstring.complete (n := payloadLen) (m := fieldLen) (s := nameIndex) payloadHash
      h_payload_len h_field_len h_field_nonempty h_sum hc₁ hc₂ h_fit h_pre
    simpa only [Bool.not_eq_true] using h
  have hB := parseJWTFieldWithUnquotedValue.complete field name value colonIndex valueIndex
    h_field_len h_name_len h_value_len h_name_nonempty h_value_nonempty h_nF_name h_sum_name
    h_sum_value (fun c hc => (hc₂ c hc).2) hc₃ hc₄ h_fit_name h_pre_name h_fit_val h_pre_val
    h_colon_order h_value_order h_open_quote h_close_quote h_colon h_last_char h_ws_zones
    h_no_forbidden
  rw [Set.setOf_or]
  calc randomOracle.toOuterMeasure
        ({f | ¬ isSubstring.accepts (Query.toHashFn f) (encodeV payloadLen payload) payloadHash
            (encodeV fieldLen field) field.length nameIndex} ∪
          {f | ¬ parseJWTFieldWithUnquotedValue.parses (Query.toHashFn f)
            (encodeV fieldLen field) field.length (encodeV nameLen name) name.length
            (encodeV valueLen value) value.length colonIndex valueIndex false})
      ≤ randomOracle.toOuterMeasure
          {f | ¬ isSubstring.accepts (Query.toHashFn f) (encodeV payloadLen payload) payloadHash
            (encodeV fieldLen field) field.length nameIndex} +
        randomOracle.toOuterMeasure
          {f | ¬ parseJWTFieldWithUnquotedValue.parses (Query.toHashFn f)
            (encodeV fieldLen field) field.length (encodeV nameLen name) name.length
            (encodeV valueLen value) value.length colonIndex valueIndex false} :=
        MeasureTheory.measure_union_le _ _
    _ ≤ (((payloadLen - 1) + 25 : ℕ) : ENNReal) / bn254 + ((2 * (fieldLen - 1) + 100 : ℕ) : ENNReal) / bn254 :=
        add_le_add hA hB
    _ = ((payloadLen - 1 + 25 + (2 * (fieldLen - 1) + 100) : ℕ) : ENNReal) / bn254 := by
        rw [ENNReal.div_add_div_same]
        norm_cast

end verifyUnquotedField
