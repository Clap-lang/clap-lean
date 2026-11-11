import Clap.RandomOracle.HashFn
import Clap.Lang.Poseidon.Computes
import Clap.Lang.Data.FString.asciiDigitsToScalar
import Clap.Lang.Data.FString.isSubstring
import Clap.Lang.Data.JWT.stringBodies
import Clap.Lang.Data.JWT.enforceNotNested
import Clap.Lang.Data.JWT.parseJWTFieldWithQuotedValue
import Clap.Lang.Core.FB.not
import Clap.Lang.Data.HashToField.hashBytesToField
import Clap.Keyless.Input
import Clap.Lang.Poseidon.Poseidon

open Clap Lang FString FArray FVec Primes

/-- Verify a quoted JWT field: substring check, not-nested check, field parsing. -/
def verifyQuotedField {maxPairLen maxNameLen maxValueLen : ℕ}
    (h_name : maxNameLen ≤ maxPairLen)
    (h_value : maxValueLen ≤ maxPairLen)
    (h_pair : maxPairLen ≤ MAX_JWT_PAYLOAD_LEN)
    (json : JSONStructure bn254)
    (inp : JWT.QuotedFieldInput bn254 maxPairLen maxNameLen maxValueLen) :
    ClapM bn254 Unit
:= do
  -- Assert field is a substring of the decoded JWT payload
  FString.assertIsSubstring h_pair json.payload.data json.payloadHash
    inp.field
    inp.nameIndex
  -- Assert fieldStringBodies is a substring of stringBodies at the same index
  -- CIRCOM: AssertIsSubstring(stringBodies, jwt_payload_hash, x_field_string_bodies, x_field_len, x_index)
  FString.assertIsSubstring h_pair json.stringBodies json.payloadHash
    inp.fieldStringBodies
    inp.nameIndex
  -- Assert field is not inside nested brackets
  enforceNotNested inp.nameIndex inp.field.len json.bracketsDepthMap
  -- Parse the field structure with quoted value
  parseJWTFieldWithQuotedValue inp h_name h_value (← FB.ofBool false)

namespace verifyQuotedField

open Poseidon RandomOracle Primes FiatShamir

-- Poseidon is opaque to this proof (it sits beneath `assertIsSubstring`/`hashBytesToField`),
-- as in `Data/HashToField/hashElemsToField.lean` and `Keyless/computeJSONStructure.lean`.
attribute [local irreducible] Clap.Lang.Poseidon.poseidonBN254

/-- The four-stage `do`-chain behind `verifyQuotedField`, stated over four fully abstract `Unit`
actions, known only via their `ConvertsM` facts — never through `assertIsSubstring` /
`enforceNotNested` / the `FB.ofBool`+`parseJWTFieldWithQuotedValue` chain by name. Because
`action1`–`action4` are free variables here, nothing in this proof is headed by a concrete
gadget's definition, so chaining `convertsM_bind_and` has nothing to `whnf` through. Instantiating
this lemma with the concrete gadgets at the call site is a shallow, first-order match against the
`do` block unfolded there; it never needs to unfold what `action1`–`action4` get assigned to. See
`computeJSONStructure.bind_convertsM` for the same trick on a 3-stage, non-`Unit` chain. -/
private lemma bind_convertsM
  {state : ClapMState bn254}
  {action1 : ClapM bn254 Unit} {C1 : Prop}
  (h1 : ConvertsM FUnit.conversion action1 state () C1)
  {action2 : ClapM bn254 Unit} {C2 : Prop}
  (h2 : ConvertsM FUnit.conversion action2 (action1.getState state) () C2)
  {action3 : ClapM bn254 Unit} {C3 : Prop}
  (h3 : ConvertsM FUnit.conversion action3 (action2.getState (action1.getState state)) () C3)
  {action4 : ClapM bn254 Unit} {C4 : Prop}
  (h4 : ConvertsM FUnit.conversion action4
    (action3.getState (action2.getState (action1.getState state))) () C4)
:
  ConvertsM FUnit.conversion
    (do action1; action2; action3; action4)
    state () (C1 ∧ C2 ∧ C3 ∧ C4)
:= convertsM_bind_and h1 (convertsM_bind_and h2 (convertsM_bind_and h3 h4))

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
  {quoted : JWT.QuotedFieldInput bn254 maxKVPairLen maxNameLen maxValueLen}
  -- Ideal values for `quoted : JWT.QuotedFieldInput`
  {field_vals : Vector (ZMod bn254) maxKVPairLen}
  {sb_vals : Vector Bool maxKVPairLen}
  {field_len sb_len : ZMod bn254}
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
  (h_field_val : Converts FVec.conversion state quoted.field.data field_vals)
  (h_sb_val : Converts FArray.conversion state quoted.fieldStringBodies.data sb_vals)
  (h_sb_len : Converts F.conversion state quoted.fieldStringBodies.len sb_len)
  (h_field_len : Converts F.conversion state quoted.field.len field_len)
  (h_name_val : Converts FVec.conversion state quoted.name.data name_vals)
  (h_name_len : Converts F.conversion state quoted.name.len name_len)
  (h_value_val : Converts FVec.conversion state quoted.value.data value_vals)
  (h_value_len : Converts F.conversion state quoted.value.len value_len)
  (h_ci : Converts F.conversion state quoted.colonIndex colon_index_val)
  (h_vi : Converts F.conversion state quoted.valueIndex value_index_val)
  (h_ni : Converts F.conversion state quoted.nameIndex name_index_val)
  -- Conversion hypotheses for `quoted : JSONStructure`
  (h_payload          : Converts FString.conversion state json.payload payload_val)
  (h_payloadHash      : Converts F.conversion state json.payloadHash payloadHash_val)
  (h_stringBodies     : Converts FArray.conversion state json.stringBodies stringBodies_val)
  (h_bracketsDepthMap : Converts FVec.conversion state json.bracketsDepthMap bracketsDepthMap_val)
  -- Range bounds (`w := 20` is hard-coded in the body)
  (h_name_len_w : name_len.val < 2 ^ 20)
  (h_colon_index_w : colon_index_val.val < 2 ^ 20)
  (h_value_index_w : value_index_val.val < 2 ^ 20)
  (h_field_len_w : field_len.val < 2 ^ 20)
  (h_sum_len_w : (name_len + value_len).val < 2 ^ 20) :
  let payloadV := encodeV (p := bn254) MAX_JWT_PAYLOAD_LEN payload_val
  ConvertsM FUnit.conversion
    (verifyQuotedField h_name_len_lt h_value_len_lt h_pair json quoted)
    state
    ()
    ( ( (∀ i : Fin maxKVPairLen, field_vals[i].val < 2 ^ 8) ∧
        (name_index_val + field_len).val < 2 ^ minBits' MAX_JWT_PAYLOAD_LEN ∧
        name_index_val.val < MAX_JWT_PAYLOAD_LEN ∧
        name_index_val.val < (name_index_val + field_len).val
      ) ∧
      isSubstring.accepts H payloadV payloadHash_val field_vals field_len name_index_val = true ∧
      ( -- (∀ i : Fin maxKVPairLen, (if sb_vals[i] then (1 : ZMod bn254) else 0).val < 2 ^ 8) ∧
        (name_index_val + sb_len).val < 2 ^ minBits' MAX_JWT_PAYLOAD_LEN ∧
        -- name_index_val.val < MAX_JWT_PAYLOAD_LEN ∧
        name_index_val.val < (name_index_val + sb_len).val
      ) ∧
      isSubstring.accepts H (stringBodies_val.map fun b ↦ if b then 1 else 0) payloadHash_val
        (sb_vals.map fun b ↦ if b then 1 else 0)
        sb_len name_index_val
        ∧
      -- (name_index_val + field_len).val < 2 ^ minBits' MAX_JWT_PAYLOAD_LEN ∧
      -- name_index_val.val < MAX_JWT_PAYLOAD_LEN ∧
      -- name_index_val.val < (name_index_val + field_len).val ∧
      (bracketsDepthMap_val.extract name_index_val.val (name_index_val + field_len).val).sum = 0 ∧
      ( --(∀ i : Fin maxKVPairLen, field_vals[i].val < 2^8) ∧
        (∀ i : Fin maxNameLen, name_vals[i].val < 2^8) ∧
        (∀ i : Fin maxValueLen, value_vals[i].val < 2^8) ∧

        (value_index_val - 1).val < maxKVPairLen ∧
        (value_index_val + value_len).val < maxKVPairLen ∧
        0 < (name_len + 2).val ∧ (name_len + 2).val ≤ maxKVPairLen ∧ colon_index_val.val < maxKVPairLen ∧
        0 < (colon_index_val + 1).val ∧ (colon_index_val + 1).val ≤ maxKVPairLen ∧ -- (value_index_val - 1).val < maxKVPairLen ∧
        0 < (value_index_val + value_len + 1).val ∧ (value_index_val + value_len + 1).val ≤ maxKVPairLen ∧ (field_len - 1).val < maxKVPairLen ∧
        1 < maxKVPairLen ∧ 1 < (name_len + 1).val ∧
        value_index_val.val < maxKVPairLen ∧ value_index_val.val < (value_index_val + value_len).val ∧

        parseJWTFieldWithQuotedValue.parses H field_vals field_len name_vals name_len value_vals value_len
          sb_vals
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
  have hb8 : ∀ (b : Bool), (if b then (1 : ZMod bn254) else 0).val < 2 ^ 8 := by
    intro b; cases b <;> decide
  unfold verifyQuotedField
  have hFact1 := assertIsSubstring.convertsM h_H h_pair
    (FString.converts_data h_payload) h_payloadHash h_field_val h_field_len h_ni
    h_len_bound h_n_bn254 hw_minBits
  replace h_payloadHash := converts_skip hFact1 h_payloadHash
  replace h_stringBodies := converts_skip hFact1 h_stringBodies
  replace h_field_val := converts_skip hFact1 h_field_val
  replace h_sb_val := converts_skip hFact1 h_sb_val
  replace h_sb_len := converts_skip hFact1 h_sb_len
  replace h_ni := converts_skip hFact1 h_ni
  replace h_field_len := converts_skip hFact1 h_field_len
  replace h_bracketsDepthMap := converts_skip hFact1 h_bracketsDepthMap
  replace h_name_val := converts_skip hFact1 h_name_val
  replace h_name_len := converts_skip hFact1 h_name_len
  replace h_value_val := converts_skip hFact1 h_value_val
  replace h_value_len := converts_skip hFact1 h_value_len
  replace h_ci := converts_skip hFact1 h_ci
  replace h_vi := converts_skip hFact1 h_vi
  have hFact2 := assertIsSubstring.convertsM h_H h_pair
    (FVec.converts_of_FArray_converts h_stringBodies) h_payloadHash
    (FVec.converts_of_FArray_converts h_sb_val) h_sb_len h_ni
    h_len_bound h_n_bn254 hw_minBits
  replace h_ni := converts_skip hFact2 h_ni
  replace h_field_len := converts_skip hFact2 h_field_len
  replace h_bracketsDepthMap := converts_skip hFact2 h_bracketsDepthMap
  replace h_field_val := converts_skip hFact2 h_field_val
  replace h_sb_val := converts_skip hFact2 h_sb_val
  replace h_name_val := converts_skip hFact2 h_name_val
  replace h_name_len := converts_skip hFact2 h_name_len
  replace h_value_val := converts_skip hFact2 h_value_val
  replace h_value_len := converts_skip hFact2 h_value_len
  replace h_ci := converts_skip hFact2 h_ci
  replace h_vi := converts_skip hFact2 h_vi
  have hFact3 := enforceNotNested.convertsM h_ni h_field_len h_bracketsDepthMap
    h_n_bn254 hw_minBits
  replace h_field_val := converts_skip hFact3 h_field_val
  replace h_sb_val := converts_skip hFact3 h_sb_val
  replace h_field_len := converts_skip hFact3 h_field_len
  replace h_name_val := converts_skip hFact3 h_name_val
  replace h_name_len := converts_skip hFact3 h_name_len
  replace h_value_val := converts_skip hFact3 h_value_val
  replace h_value_len := converts_skip hFact3 h_value_len
  replace h_ci := converts_skip hFact3 h_ci
  replace h_vi := converts_skip hFact3 h_vi
  have hOfBool := FB.ofBool.convertsM (p := bn254) (b := false)
    (state := (enforceNotNested quoted.nameIndex quoted.field.len json.bracketsDepthMap).getState
      ((assertIsSubstring h_pair json.stringBodies json.payloadHash quoted.fieldStringBodies
          quoted.nameIndex).getState
        ((assertIsSubstring h_pair json.payload.data json.payloadHash quoted.field
            quoted.nameIndex).getState state)))
  replace h_field_val := converts_skip hOfBool h_field_val
  replace h_sb_val := converts_skip hOfBool h_sb_val
  replace h_field_len := converts_skip hOfBool h_field_len
  replace h_name_val := converts_skip hOfBool h_name_val
  replace h_name_len := converts_skip hOfBool h_name_len
  replace h_value_val := converts_skip hOfBool h_value_val
  replace h_value_len := converts_skip hOfBool h_value_len
  replace h_ci := converts_skip hOfBool h_ci
  replace h_vi := converts_skip hOfBool h_vi
  have hFact4 := parseJWTFieldWithQuotedValue.convertsM h_H h_name_len_lt h_value_len_lt
    h_len_bound h_field_val h_sb_val h_field_len h_name_val h_name_len h_value_val h_value_len
    h_ci h_vi hOfBool.result h_name_len_w h_colon_index_w h_value_index_w h_field_len_w
    h_sum_len_w
  have hFact4' := convertsM_of_convertsM hFact4 rfl ⟨fun h _ ↦ h, fun h ↦ h trivial⟩
  have hStep4 := convertsM_bind hOfBool hFact4' (fun _ ↦ trivial)
  have hWhole := bind_convertsM hFact1 hFact2 hFact3 hStep4
  -- `parseJWTFieldWithQuotedValue.convertsM`'s own conclusion states
  -- `(value_index_val - 1).val < maxKVPairLen` twice (once standalone, once just before the
  -- `0 < (value_index_val + value_len + 1).val` block); the public-facing goal above drops the
  -- second occurrence (and the leading field-byte-range conjunct, redundant with `hA1`'s own).
  refine convertsM_of_convertsM hWhole rfl ?_
  constructor
  · rintro ⟨⟨hA1, haccepts1⟩, ⟨⟨-, hA2b1, -, hA2b2⟩, haccepts2⟩,
      ⟨-, -, -, hsum0⟩,
      -, h2, h3, h4, h5, h6, h7, h8, h9, h10, -, h12, h13, h14, h15, h16, h17, h18, h19⟩
    obtain ⟨hAbyte, hA1b1, hA1MAX, hA1b2⟩ := hA1
    exact ⟨⟨hAbyte, hA1b1, hA1MAX, hA1b2⟩, haccepts1, ⟨hA2b1, hA2b2⟩, haccepts2, hsum0,
      h2, h3, h4, h5, h6, h7, h8, h9, h10, h12, h13, h14, h15, h16, h17, h18, h19⟩
  · rintro ⟨hA1, haccepts1, ⟨hA2b1, hA2b2⟩, haccepts2, hsum0,
      h2, h3, h4, h5, h6, h7, h8, h9, h10, h12, h13, h14, h15, h16, h17, h18, h19⟩
    obtain ⟨hAbyte, hA1b1, hA1MAX, hA1b2⟩ := hA1
    have hByteSb : ∀ i : Fin maxKVPairLen,
        (sb_vals.map fun (b : Bool) ↦ if b then (1 : ZMod bn254) else 0)[i].val < 2 ^ 8 := by
      intro i
      simp only [Fin.getElem_fin, Vector.getElem_map]
      exact hb8 sb_vals[i]
    exact ⟨⟨⟨hAbyte, hA1b1, hA1MAX, hA1b2⟩, haccepts1⟩,
      ⟨⟨hByteSb, hA2b1, hA1MAX, hA2b2⟩, haccepts2⟩,
      ⟨hA1b1, hA1MAX, hA1b2, hsum0⟩,
      ⟨hAbyte, h2, h3, h4, h5, h6, h7, h8, h9, h10, h4, h12, h13, h14, h15, h16, h17, h18, h19⟩⟩

end verifyQuotedField
