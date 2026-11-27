
import Clap.RandomOracle.HashFn
import Clap.Lang.Poseidon.Computes
import Clap.Lang.Data.FString.isSubstring
import Clap.Lang.Data.JWT.enforceNotNested
import Clap.Lang.Data.JWT.emailVerifiedCheck
import Clap.Lang.Data.JWT.parseEmailVerifiedField
import Clap.Keyless.Input
import Clap.Lang.Poseidon.Poseidon
import Clap.Model.Convert.PaddedVector

namespace Clap.Lang

open Primes FString

/-- Verify the email_verified field and cross-check with uid name.
    CIRCOM truth table: fail only if uidIsEmail AND NOT evInJwt. -/
def verifyEvField (json : JSONStructure bn254)
  (ev : EvFieldInput bn254 MAX_EV_KV_PAIR_LEN MAX_EV_NAME_LEN MAX_EV_VALUE_LEN)
  (uidName : FString bn254 MAX_UID_NAME_LEN) :
  ClapM bn254 Unit
:= do
  -- Cross-check: get uidIsEmail from emailVerifiedCheck
  let uidIsEmail ←
    emailVerifiedCheck
      uidName
      ev.name
      ev.value
  -- Check if ev field is in JWT (non-asserting)
  let evInJwt ←
    FString.isSubstring (by decide) json.payload.data json.payloadHash
      ev.field
      ev.nameIndex
  FB.conditionallyAssert uidIsEmail evInJwt
  -- Assert not inside nested brackets
  enforceNotNested ev.nameIndex ev.field.len json.bracketsDepthMap
  -- Parse the email_verified field (allows both quoted and unquoted true/false)
  parseEmailVerifiedField (by decide) (by decide) ev.field ev.name ev.value
    ev.colonIndex
    ev.valueIndex

namespace verifyEvField

open Poseidon RandomOracle

-- Poseidon is opaque to this proof (it sits beneath `isSubstring`/`hashBytesToField`), as in
-- `verifyQuotedField.lean` and `Keyless/computeJSONStructure.lean`.
attribute [local irreducible] Clap.Lang.Poseidon.poseidonBN254

/-- The five-stage `do`-chain behind `verifyEvField`, stated over five fully abstract actions,
known only via their `ConvertsM` facts — never through `emailVerifiedCheck`/`isSubstring`/
`FB.conditionallyAssert`/`enforceNotNested`/`parseEmailVerifiedField` by name. `action3` is a
curried function of `action1`'s and `action2`'s results, instantiated at the call site as
`fun x y ↦ FB.conditionallyAssert x y`. Same trick as `verifyQuotedField.bind_convertsM` /
`computeJSONStructure.bind_convertsM`, extended to two value-producing stages up front. -/
private lemma bind_convertsM
  {state : ClapMState bn254}
  {action1 : ClapM bn254 (FB bn254)} {val1 : Bool} {C1 : Prop}
  (h1 : ConvertsM FB.conversion action1 state val1 C1)
  {action2 : ClapM bn254 (FB bn254)} {val2 : Bool} {C2 : Prop}
  (h2 : ConvertsM FB.conversion action2 (action1.getState state) val2 C2)
  {action3 : FB bn254 → FB bn254 → ClapM bn254 Unit} {C3 : Prop}
  (h3 : ConvertsM FUnit.conversion
          (action3 (action1.getResult state.numAlloc state.σ)
                   (action2.getResult (action1.getState state).numAlloc (action1.getState state).σ))
          (action2.getState (action1.getState state)) () C3)
  {action4 : ClapM bn254 Unit} {C4 : Prop}
  (h4 : ConvertsM FUnit.conversion action4
          ((action3 (action1.getResult state.numAlloc state.σ)
                    (action2.getResult (action1.getState state).numAlloc (action1.getState state).σ)).getState
            (action2.getState (action1.getState state)))
          () C4)
  {action5 : ClapM bn254 Unit} {C5 : Prop}
  (h5 : ConvertsM FUnit.conversion action5
          (action4.getState
            ((action3 (action1.getResult state.numAlloc state.σ)
                      (action2.getResult (action1.getState state).numAlloc (action1.getState state).σ)).getState
              (action2.getState (action1.getState state))))
          () C5)
:
  ConvertsM FUnit.conversion
    (do
      let uidIsEmail ← action1
      let evInJwt ← action2
      action3 uidIsEmail evInJwt
      action4
      action5)
    state () (C1 ∧ C2 ∧ C3 ∧ C4 ∧ C5)
:= convertsM_bind_and h1 (convertsM_bind_and h2 (convertsM_bind_and h3 (convertsM_bind_and h4 h5)))

lemma convertsM {H : HashFn} (h_H : Computes H) {state : ClapMState bn254}
  {json    : JSONStructure bn254}
  {ev      : EvFieldInput bn254 MAX_EV_KV_PAIR_LEN MAX_EV_NAME_LEN MAX_EV_VALUE_LEN}
  {uidName : FString bn254 MAX_UID_NAME_LEN}
  -- Ideal values
  {field_vals           : Vector (ZMod bn254) MAX_EV_KV_PAIR_LEN}
  {bracketsDepthMap_val : Vector (ZMod bn254) MAX_JWT_PAYLOAD_LEN}
  {payloadHash_val field_len name_index_val colon_index_val value_index_val : ZMod bn254}
  {uidName_val evName_val evValue_val payload_val : String}
  -- Conversion lemmas
  (h_uidName : Converts FString.conversion state uidName uidName_val)
  -- `ev` conversion lemmas
  (h_field_val : Converts FVec.conversion  state ev.field.data field_vals)
  (h_field_len : Converts F.conversion     state ev.field.len field_len)
  (h_ni        : Converts F.conversion     state ev.nameIndex name_index_val)
  (h_ci        : Converts F.conversion     state ev.colonIndex colon_index_val)
  (h_vi        : Converts F.conversion     state ev.valueIndex value_index_val)
  (h_evName : Converts FString.conversion  state ev.name evName_val)
  (h_evValue : Converts FString.conversion state ev.value evValue_val)
  -- `json` conversion lemmas
  (h_payload          : Converts FString.conversion state json.payload payload_val)
  (h_payloadHash      : Converts F.conversion       state json.payloadHash payloadHash_val)
  (h_bracketsDepthMap : Converts FVec.conversion    state json.bracketsDepthMap bracketsDepthMap_val)
  -- Required by `emailVerifiedCheck.convertsM`:
  (h_uidName_len : uidName_val.length < MAX_UID_NAME_LEN)
  (h_evName_len  : evName_val.length  < MAX_EV_NAME_LEN)
  (h_evValue_len : evValue_val.length < MAX_EV_VALUE_LEN)
  (h_uidName_chars : ∀ c ∈ uidName_val.toList, c.toNat < 256)
  (h_evName_chars  : ∀ c ∈ evName_val.toList,  c.toNat < 256)
  (h_evValue_chars : ∀ c ∈ evValue_val.toList, c.toNat < 256)
  -- Required by `parseEmailVerifiedField.convertsM`:
  (h_colon_index_w : colon_index_val.val < 2 ^ 20)
  (h_value_index_w : value_index_val.val < 2 ^ 20)
  (h_field_len_w : field_len.val < 2 ^ 20)
  :
  let payloadV := FString.encodeV (p := bn254) MAX_JWT_PAYLOAD_LEN payload_val
  let nameV := FString.encodeV (p := bn254) MAX_EV_NAME_LEN evName_val
  let nameLen : ZMod bn254 := evName_val.length
  let valueV := FString.encodeV (p := bn254) MAX_EV_VALUE_LEN evValue_val
  let valueLen : ZMod bn254 := evValue_val.length
  ConvertsM FUnit.conversion
    (verifyEvField json ev uidName)
    state
    ()
    ( -- From `emailVerifiedCheck.convertsM`.
      ( uidName_val = "email" →
        evName_val = "email_verified" ∧ (evValue_val = "true" ∨ evValue_val = "\"true\"")
      ) ∧
      -- From `isSubstring.convertsM`.
      ( (∀ i : Fin MAX_EV_KV_PAIR_LEN, field_vals[i].val < 2 ^ 8) ∧
        (name_index_val + field_len).val < 2 ^ minBits' MAX_JWT_PAYLOAD_LEN ∧
        name_index_val.val < MAX_JWT_PAYLOAD_LEN ∧
        name_index_val.val < (name_index_val + field_len).val
      ) ∧
      -- From `FB.conditionallyAssert uidIsEmail evInJwt`
      ( decide (uidName_val = "email") = true →
          FString.isSubstring.accepts H payloadV payloadHash_val field_vals field_len name_index_val
      ) ∧
      -- From `enforceNotNested.convertsM`
      ( -- redundant: (name_index_val + field_len).val < 2 ^ minBits' MAX_JWT_PAYLOAD_LEN ∧
        -- redundant: name_index_val.val < MAX_JWT_PAYLOAD_LEN ∧
        -- redundant: name_index_val.val < (name_index_val + field_len).val ∧
        (bracketsDepthMap_val.extract name_index_val.val (name_index_val + field_len).val).sum = 0
      ) ∧
      -- From `parseEmailVerifiedField.convertsM`
      ( -- redundant: (∀ i : Fin MAX_EV_KV_PAIR_LEN, field_vals[i].val < 2 ^ 8) ∧
        (∀ i : Fin MAX_EV_NAME_LEN, nameV[i].val < 2 ^ 8) ∧
        (∀ i : Fin MAX_EV_VALUE_LEN, valueV[i].val < 2 ^ 8) ∧

        nameLen.val + 1 < MAX_EV_KV_PAIR_LEN ∧
        colon_index_val.val < MAX_EV_KV_PAIR_LEN ∧
        (field_len - 1).val < MAX_EV_KV_PAIR_LEN ∧

        0 < nameLen.val ∧

        (value_index_val + valueLen).val < MAX_EV_KV_PAIR_LEN ∧
        value_index_val.val < (value_index_val + valueLen).val ∧
        0 < valueLen.val ∧

        parseEmailVerifiedField.parses H field_vals field_len nameV nameLen valueV valueLen
          colon_index_val
          value_index_val
      )
    )
:= by
  intro payloadV nameV nameLen valueV valueLen
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
  have h_evName_max_bn254  : MAX_EV_NAME_LEN  < bn254 := by decide
  have h_evValue_max_bn254 : MAX_EV_VALUE_LEN < bn254 := by decide
  have h_evName_max_w  : MAX_EV_NAME_LEN  < 2 ^ 20 := by decide
  have h_evValue_max_w : MAX_EV_VALUE_LEN < 2 ^ 20 := by decide
  have h_sum_max_bn254 : MAX_EV_NAME_LEN + MAX_EV_VALUE_LEN < bn254 := by decide
  have h_sum_max_w : MAX_EV_NAME_LEN + MAX_EV_VALUE_LEN < 2 ^ 20 := by decide
  have h_evName_len_bn254 : evName_val.length < bn254 := by omega
  have h_evValue_len_bn254 : evValue_val.length < bn254 := by omega
  have h_sum_len_bn254 : evName_val.length + evValue_val.length < bn254 := by omega
  have h_name_len_w' : nameLen.val < 2 ^ 20 := by
    show (evName_val.length : ZMod bn254).val < 2 ^ 20
    rw [ZMod.val_natCast_of_lt h_evName_len_bn254]
    omega
  have h_sum_len_w' : (nameLen + valueLen).val < 2 ^ 20 := by
    show ((evName_val.length : ZMod bn254) + (evValue_val.length : ZMod bn254)).val < 2 ^ 20
    rw [← Nat.cast_add, ZMod.val_natCast_of_lt h_sum_len_bn254]
    omega
  unfold verifyEvField
  have h1 := emailVerifiedCheck.convertsM
    h_uidName h_evName h_evValue
    (by decide) (by decide) (by decide) (by decide)
    h_uidName_len h_evName_len h_evValue_len
    h_uidName_chars h_evName_chars h_evValue_chars
    (by decide) (by decide) (by decide)
  replace h_evName := converts_skip h1 h_evName
  replace h_evValue := converts_skip h1 h_evValue
  replace h_payload := converts_skip h1 h_payload
  replace h_payloadHash := converts_skip h1 h_payloadHash
  replace h_field_val := converts_skip h1 h_field_val
  replace h_field_len := converts_skip h1 h_field_len
  replace h_ni := converts_skip h1 h_ni
  replace h_bracketsDepthMap := converts_skip h1 h_bracketsDepthMap
  replace h_ci := converts_skip h1 h_ci
  replace h_vi := converts_skip h1 h_vi
  have h2 := FString.isSubstring.convertsM h_H (by decide)
    (FString.converts_data h_payload) h_payloadHash h_field_val h_field_len h_ni
    (by decide) h_n_bn254 hw_minBits
  replace h_evName := converts_skip h2 h_evName
  replace h_evValue := converts_skip h2 h_evValue
  replace h_field_val := converts_skip h2 h_field_val
  replace h_field_len := converts_skip h2 h_field_len
  replace h_ni := converts_skip h2 h_ni
  replace h_bracketsDepthMap := converts_skip h2 h_bracketsDepthMap
  replace h_ci := converts_skip h2 h_ci
  replace h_vi := converts_skip h2 h_vi
  have h3 := FB.conditionallyAssert.convertsM (converts_skip h2 h1.result) h2.result
  replace h_evName := converts_skip h3 h_evName
  replace h_evValue := converts_skip h3 h_evValue
  replace h_field_val := converts_skip h3 h_field_val
  replace h_field_len := converts_skip h3 h_field_len
  replace h_ni := converts_skip h3 h_ni
  replace h_bracketsDepthMap := converts_skip h3 h_bracketsDepthMap
  replace h_ci := converts_skip h3 h_ci
  replace h_vi := converts_skip h3 h_vi
  have h4 := enforceNotNested.convertsM h_ni h_field_len h_bracketsDepthMap h_n_bn254 hw_minBits
  replace h_evName := converts_skip h4 h_evName
  replace h_evValue := converts_skip h4 h_evValue
  replace h_field_val := converts_skip h4 h_field_val
  replace h_field_len := converts_skip h4 h_field_len
  replace h_ci := converts_skip h4 h_ci
  replace h_vi := converts_skip h4 h_vi
  have h5 := parseEmailVerifiedField.convertsM h_H (by decide) (by decide)
    h_field_val h_field_len
    (FString.converts_data h_evName) (FString.converts_len h_evName)
    (FString.converts_data h_evValue) (FString.converts_len h_evValue)
    h_ci h_vi
    h_name_len_w' h_colon_index_w h_value_index_w h_field_len_w h_sum_len_w' (by decide)
  have hWhole := bind_convertsM h1 h2 h3 h4 h5
  refine convertsM_of_convertsM hWhole rfl ?_
  constructor
  · rintro ⟨hc1, ⟨hbyte, hbound, hlt1, hlt2⟩, hc3, ⟨-, -, -, hsum⟩, -, hc5rest⟩
    exact ⟨hc1, ⟨hbyte, hbound, hlt1, hlt2⟩, hc3, hsum, hc5rest⟩
  · rintro ⟨hg1, ⟨hbyte, hbound, hlt1, hlt2⟩, hg3, hsum, hg5rest⟩
    exact ⟨hg1, ⟨hbyte, hbound, hlt1, hlt2⟩, hg3, ⟨hbound, hlt1, hlt2, hsum⟩, hbyte, hg5rest⟩

theorem sound {nF nN nV nP}
  {nameIndex : ℕ}
  {payload field name value uid : String}
  (colonIndex valueIndex : ZMod bn254)
  (strHash : ZMod bn254)
  (h_payload_len : payload.length ≤ nP)
  (h_field_len : field.length ≤ nF)
  (h_0 : 0 < field.length)
  (h_sn : nameIndex < nP)
  (h_nm : nP + nF < bn254)
  (h_nameLen : name.length ≤ nN)
  (h_valueLen : value.length ≤ nV)
  (h_namePos : 0 < name.length)
  (h_valuePos : 0 < value.length)
  (h_nF_name : 1 < nF)
  (h_valueIndex : valueIndex.val < nF)
  (h_nm_name : nF + nN < bn254)
  (h_nm_value : nF + nV < bn254)
  (h_name_bytes : ∀ c ∈ name.toList, 0 < c.toNat ∧ c.toNat < 256)
  (h_value_bytes : ∀ c ∈ value.toList, 0 < c.toNat ∧ c.toNat < 256)
  (h_payload_bytes : ∀ c ∈ payload.toList, c.toNat < 256)
  (h_field_bytes : ∀ c ∈ field.toList, 0 < c.toNat ∧ c.toNat < 256)
  (h_bad :
    (uid = "email" ∧
      ¬ (nameIndex + field.length ≤ payload.length ∧ field.toList <+: payload.toList.drop nameIndex)
    ) ∨
    ¬ (1 + name.length ≤ field.length ∧ name.toList <+: field.toList.drop 1) ∨
    ¬ (valueIndex.val + value.length ≤ field.length ∧
        value.toList <+: field.toList.drop valueIndex.val
      )
  )
  :
  randomOracle.toOuterMeasure
    {f |
      (uid = "email" →
        isSubstring.accepts (Query.toHashFn f) (encodeV nP payload) strHash
          (encodeV nF field)
          field.length
          nameIndex
      ) ∧
      parseEmailVerifiedField.parses (Query.toHashFn f)
        (encodeV nF field)
        field.length
        (encodeV nN name)
        name.length
        (encodeV nV value)
        value.length
        colonIndex
        valueIndex
    }
      ≤ ((max (nP - 1 + (nF - 1) + 25) (nF - 1 + (max nN nV - 1) + 50) : ℕ) : ENNReal) / bn254
:= by
  rcases h_bad with ⟨h_uid, h_loc⟩ | h_name_bad | h_value_bad
  · -- the field isn't really at `nameIndex` in `payload` (and `uid = "email"`, so the circuit
    -- really does check it)
    have h_sub :
        {f |
          (uid = "email" →
            isSubstring.accepts (Query.toHashFn f) (encodeV nP payload) strHash
              (encodeV nF field) field.length nameIndex) ∧
          parseEmailVerifiedField.parses (Query.toHashFn f)
            (encodeV nF field) field.length (encodeV nN name) name.length (encodeV nV value)
            value.length colonIndex valueIndex} ⊆
        {f | isSubstring.accepts (Query.toHashFn f) (encodeV nP payload) strHash
              (encodeV nF field) field.length nameIndex = true} :=
      fun f hf => hf.1 h_uid
    refine (MeasureTheory.measure_mono h_sub).trans ?_
    refine (isSubstring.sound (n := nP) (m := nF) (s := nameIndex) strHash
      h_payload_len h_field_len h_0 h_sn h_nm h_payload_bytes h_field_bytes h_loc).trans
      (ENNReal.div_le_div_right ?_ _)
    exact_mod_cast
      (show nP - 1 + (nF - 1) + 25 ≤
          max (nP - 1 + (nF - 1) + 25) (nF - 1 + (max nN nV - 1) + 50) by omega)
  · -- `name` isn't really at position `1` in `field`
    have h_sub :
        {f |
          (uid = "email" →
            isSubstring.accepts (Query.toHashFn f) (encodeV nP payload) strHash
              (encodeV nF field) field.length nameIndex) ∧
          parseEmailVerifiedField.parses (Query.toHashFn f)
            (encodeV nF field) field.length (encodeV nN name) name.length (encodeV nV value)
            value.length colonIndex valueIndex} ⊆
        {f | parseEmailVerifiedField.parses (Query.toHashFn f)
              (encodeV nF field) field.length (encodeV nN name) name.length (encodeV nV value)
              value.length colonIndex valueIndex} :=
      fun f hf => hf.2
    refine (MeasureTheory.measure_mono h_sub).trans ?_
    refine (parseEmailVerifiedField.sound field name value colonIndex valueIndex
      h_field_len h_nameLen h_valueLen h_namePos h_valuePos h_nF_name h_valueIndex
      h_nm_name h_nm_value (fun c hc => (h_field_bytes c hc).2) h_name_bytes h_value_bytes
      (Or.inl h_name_bad)).trans (ENNReal.div_le_div_right ?_ _)
    exact_mod_cast
      (show nF - 1 + (max nN nV - 1) + 50 ≤
          max (nP - 1 + (nF - 1) + 25) (nF - 1 + (max nN nV - 1) + 50) by omega)
  · -- `value` isn't really at `valueIndex` in `field` — symmetric to the previous case
    have h_sub :
        {f |
          (uid = "email" →
            isSubstring.accepts (Query.toHashFn f) (encodeV nP payload) strHash
              (encodeV nF field) field.length nameIndex) ∧
          parseEmailVerifiedField.parses (Query.toHashFn f)
            (encodeV nF field) field.length (encodeV nN name) name.length (encodeV nV value)
            value.length colonIndex valueIndex} ⊆
        {f | parseEmailVerifiedField.parses (Query.toHashFn f)
              (encodeV nF field) field.length (encodeV nN name) name.length (encodeV nV value)
              value.length colonIndex valueIndex} :=
      fun f hf => hf.2
    refine (MeasureTheory.measure_mono h_sub).trans ?_
    refine (parseEmailVerifiedField.sound field name value colonIndex valueIndex
      h_field_len h_nameLen h_valueLen h_namePos h_valuePos h_nF_name h_valueIndex
      h_nm_name h_nm_value (fun c hc => (h_field_bytes c hc).2) h_name_bytes h_value_bytes
      (Or.inr h_value_bad)).trans (ENNReal.div_le_div_right ?_ _)
    exact_mod_cast
      (show nF - 1 + (max nN nV - 1) + 50 ≤
          max (nP - 1 + (nF - 1) + 25) (nF - 1 + (max nN nV - 1) + 50) by omega)

theorem complete {nF nN nV nP}
  {nameIndex : ℕ}
  {payload field name value uid : String}
  (colonIndex valueIndex : ZMod bn254)
  (strHash : ZMod bn254)
  (h_payload_len : payload.length ≤ nP)
  (h_field_len : field.length ≤ nF)
  (h_0 : 0 < field.length)
  (h_nm : nP + nF < bn254)
  (h_nameLen : name.length ≤ nN)
  (h_valueLen : value.length ≤ nV)
  (h_namePos : 0 < name.length)
  (h_valuePos : 0 < value.length)
  (h_nF_name : 1 < nF)
  (h_nm_name : nF + nN < bn254)
  (h_nm_value : nF + nV < bn254)
  (h_name_bytes : ∀ c ∈ name.toList, 0 < c.toNat ∧ c.toNat < 256)
  (h_value_bytes : ∀ c ∈ value.toList, 0 < c.toNat ∧ c.toNat < 256)
  (h_payload_bytes : ∀ c ∈ payload.toList, c.toNat < 256)
  (h_field_bytes : ∀ c ∈ field.toList, 0 < c.toNat ∧ c.toNat < 256)
  (h_substr₁ :
    (uid = "email" →
      nameIndex + field.length ≤ payload.length ∧ field.toList <+: payload.toList.drop nameIndex
    )
   )
  (h_substr₂ : 1 + name.length ≤ field.length ∧ name.toList <+: field.toList.drop 1)
  (h_substr₃ :
    valueIndex.val + value.length ≤ field.length ∧
    value.toList <+: field.toList.drop valueIndex.val
  )
  (h_colon_order : name.length < colonIndex.val)
  (h_value_order : colonIndex.val < valueIndex.val)
  (h_open_quote : field.toList[0]? = some '\"')
  (h_close_quote : field.toList[name.length + 1]? = some '\"')
  (h_colon : field.toList[colonIndex.val]? = some ':')
  (h_last_char : field.toList[field.length - 1]? = some ',' ∨
    field.toList[field.length - 1]? = some '}')
  (h_char_before : let charBefore := field.toList[valueIndex.val - 1]?;
    charBefore = some '\"' ∨
      charBefore.elim false (isWs ∘ Char.toNat) ∨
      valueIndex.val = colonIndex.val + 1
  )
  (h_char_after : let charAfter := field.toList[valueIndex.val + value.length]?;
    charAfter = some '\"' ∨
      charAfter.elim false (isWs ∘ Char.toNat) ∨
      field.length = valueIndex.val + value.length + 1
  )
  (h_quoteMatch :
    let charBefore := field.toList[valueIndex.val - 1]?;
    let charAfter := field.toList[valueIndex.val + value.length]?;
    (charBefore == some '\"') = (charAfter == some '\"')
  )
  (h_ws_zones : ∀ i,
    name.length + 2 ≤ i ∧ i < colonIndex.val ∨
    colonIndex.val + 1 ≤ i ∧ i < valueIndex.val - 1 ∨
    valueIndex.val + value.length + 1 ≤ i ∧ i < field.length - 1 →
    (field.toList[i]?.elim false (isWs ∘ Char.toNat) : Prop)
  )
  :
  randomOracle.toOuterMeasure
    {f |
      (uid = "email" ∧
        ¬ isSubstring.accepts (Query.toHashFn f) (encodeV nP payload) strHash
          (encodeV nF field)
          field.length
          nameIndex
      ) ∨
      ¬parseEmailVerifiedField.parses (Query.toHashFn f)
        (encodeV nF field)
        field.length
        (encodeV nN name)
        name.length
        (encodeV nV value)
        value.length
        colonIndex
        valueIndex
    }
      ≤ ((nP - 1 + 25 + (2 * (nF - 1) + 100) : ℕ) : ENNReal) / bn254
:= by
  have hB := parseEmailVerifiedField.complete field name value colonIndex valueIndex
    h_field_len h_nameLen h_valueLen h_namePos h_valuePos h_nF_name h_nm_name h_nm_value
    (fun c hc => (h_field_bytes c hc).2) h_name_bytes h_value_bytes
    h_substr₂.1 h_substr₂.2 h_substr₃.1 h_substr₃.2
    h_colon_order h_value_order h_open_quote h_close_quote h_colon h_last_char
    h_char_before h_char_after h_quoteMatch h_ws_zones
  have hA : randomOracle.toOuterMeasure
      {f | uid = "email" ∧ ¬isSubstring.accepts (Query.toHashFn f) (encodeV nP payload) strHash
        (encodeV nF field) field.length nameIndex} ≤
      (((nP - 1) + 25 : ℕ) : ENNReal) / bn254 := by
    by_cases h_uid : uid = "email"
    · obtain ⟨h_fit_pay, h_pre_pay⟩ := h_substr₁ h_uid
      refine le_trans (MeasureTheory.measure_mono ?_)
        (isSubstring.complete (n := nP) (m := nF) (s := nameIndex) strHash
          h_payload_len h_field_len h_0 h_nm h_payload_bytes h_field_bytes h_fit_pay h_pre_pay)
      rintro f ⟨-, hf⟩
      simp only [Set.mem_setOf_eq, Bool.not_eq_true] at hf ⊢
      exact hf
    · have hEmpty : {f : Query → ZMod bn254 | uid = "email" ∧
          ¬isSubstring.accepts (Query.toHashFn f) (encodeV nP payload) strHash
            (encodeV nF field) field.length nameIndex} = ∅ := by
        ext f; simp [h_uid]
      rw [hEmpty, MeasureTheory.measure_empty]
      exact zero_le
  rw [Set.setOf_or]
  calc randomOracle.toOuterMeasure
        ({f | uid = "email" ∧ ¬isSubstring.accepts (Query.toHashFn f) (encodeV nP payload) strHash
            (encodeV nF field) field.length nameIndex} ∪
          {f | ¬parseEmailVerifiedField.parses (Query.toHashFn f) (encodeV nF field) field.length
            (encodeV nN name) name.length (encodeV nV value) value.length colonIndex valueIndex})
      ≤ randomOracle.toOuterMeasure
          {f | uid = "email" ∧ ¬isSubstring.accepts (Query.toHashFn f) (encodeV nP payload) strHash
            (encodeV nF field) field.length nameIndex} +
        randomOracle.toOuterMeasure
          {f | ¬parseEmailVerifiedField.parses (Query.toHashFn f) (encodeV nF field) field.length
            (encodeV nN name) name.length (encodeV nV value) value.length colonIndex valueIndex} :=
        MeasureTheory.measure_union_le _ _
    _ ≤ (((nP - 1) + 25 : ℕ) : ENNReal) / bn254 + ((2 * (nF - 1) + 100 : ℕ) : ENNReal) / bn254 :=
        add_le_add hA hB
    _ = ((nP - 1 + 25 + (2 * (nF - 1) + 100) : ℕ) : ENNReal) / bn254 := by
        rw [ENNReal.div_add_div_same]
        norm_cast

end verifyEvField

end Clap.Lang
