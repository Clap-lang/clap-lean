import Clap.Model.Convert.Specialised
import Clap.Model.Convert.PaddedVector
import Clap.Model.Convert.Vector

/-!
# Keyless circuit input types

The Lean-level shape of the top-level Keyless circuit's public input, and the size constants
that fix each field's width. Allocation of these into circuit variables lives in
`Clap/Keyless/Allocate.lean`, on top of the generic allocators in
`Clap/Model/PublicInput.lean`.
-/

namespace Clap

open Lang

-- JWT encoding lengths
abbrev MAX_B64U_JWT_NO_SIG_LEN := 1536
abbrev MAX_B64U_JWT_HEADER_W_DOT_LEN := 300
abbrev MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN := 1472
abbrev MAX_JWT_PAYLOAD_LEN := 3 * MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN / 4 -- 1104

-- JWT field max lengths: (kv_pair, name, value)
abbrev MAX_AUD_KV_PAIR_LEN := 140
abbrev MAX_AUD_NAME_LEN    := 40
abbrev MAX_AUD_VALUE_LEN   := 120

abbrev MAX_ISS_KV_PAIR_LEN := 140
abbrev MAX_ISS_NAME_LEN    := 40
abbrev MAX_ISS_VALUE_LEN   := 120

abbrev MAX_IAT_KV_PAIR_LEN := 50
abbrev MAX_IAT_NAME_LEN    := 10
abbrev MAX_IAT_VALUE_LEN   := 45

abbrev MAX_NONCE_KV_PAIR_LEN := 105
abbrev MAX_NONCE_NAME_LEN    := 10
abbrev MAX_NONCE_VALUE_LEN   := 100

abbrev MAX_EV_KV_PAIR_LEN := 30
abbrev MAX_EV_NAME_LEN    := 20
abbrev MAX_EV_VALUE_LEN   := 10

abbrev MAX_UID_KV_PAIR_LEN := 350
abbrev MAX_UID_NAME_LEN    := 30
abbrev MAX_UID_VALUE_LEN   := 330

abbrev MAX_EXTRA_FIELD_KV_PAIR_LEN := 350

-- RSA constants
abbrev RSA_NUM_LIMBS := 32 -- 32 × 64-bit limbs = 2048 bits
abbrev RSA_KEY_BYTES := RSA_NUM_LIMBS * 8  -- 256 bytes

-- SHA2 constants
abbrev SHA2_PADDING_LEN  := 64
abbrev SHA2_NUM_BITS_LEN := 8

-- EPK constants
abbrev EPK_NUM_FIELDS := 3

/-- Email-verified field input (special parsing: value may be quoted or unquoted). -/
structure EvFieldInput (p maxPairLen maxNameLen maxValueLen : ℕ) where
  field      : FString p maxPairLen
  name       : FString p maxNameLen
  value      : FString p maxValueLen
  nameIndex  : F p
  colonIndex : F p
  valueIndex : F p

/-- JWT raw data and SHA2 signals. -/
structure JWTRawInput (p) where
  b64u_jwt_no_sig_sha2_padded   : FString p MAX_B64U_JWT_NO_SIG_LEN
  b64u_jwt_header_w_dot         : FString p MAX_B64U_JWT_HEADER_W_DOT_LEN
  b64u_jwt_payload_sha2_padded  : FString p MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN
  b64u_jwt_payload              : FString p MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN
  sha2_num_blocks               : F p
  sha2_num_bits                 : Vector (F p) SHA2_NUM_BITS_LEN
  sha2_padding                  : Vector (F p) SHA2_PADDING_LEN

/-- RSA signature input: 32 × 64-bit limbs each. -/
structure RSAInput (p) where
  signature     : Vector (F p) RSA_NUM_LIMBS
  pubkeyModulus : Vector (F p) RSA_NUM_LIMBS

/-- Audience override signals. -/
structure AudOverrideInput (p) where
  useAudOverride   : F p
  skipAudChecks    : F p
  privateAudValue  : FString p MAX_AUD_VALUE_LEN
  overrideAudValue : FString p MAX_AUD_VALUE_LEN

/-- Extra field signals. -/
structure ExtraFieldInput (p) where
  extraField      : FString p MAX_EXTRA_FIELD_KV_PAIR_LEN
  extraFieldIndex : F p
  useExtraField   : F p

/-- Cryptographic commitment signals: EPK, expiration, pepper. -/
structure CommitmentInput (p) where
  epk        : Vector (F p) EPK_NUM_FIELDS
  epkLen     : F p
  epkBlinder : F p
  expDate    : F p
  expHorizon : F p
  pepper     : F p

/-- JWT field with an unquoted value (iat). -/
structure JWT.UnquotedFieldInput (p maxPairLen maxNameLen maxValueLen : ℕ) where
  field      : FString p maxPairLen
  name       : FString p maxNameLen
  value      : FString p maxValueLen
  nameIndex  : F p
  colonIndex : F p
  valueIndex : F p

/-- JWT field with a quoted value (aud, uid, iss, nonce). -/
structure JWT.QuotedFieldInput (p maxPairLen maxNameLen maxValueLen : ℕ) where
  field             : FString p maxPairLen
  name              : FString p maxNameLen
  value             : FString p maxValueLen
  fieldStringBodies : PaddedVector (FB p) p maxPairLen
  nameIndex         : F p
  colonIndex        : F p
  valueIndex        : F p

/-- Top-level Keyless circuit input. -/
structure FKeylessInput (p) where
  jwtRaw           : JWTRawInput p
  rsa              : RSAInput p
  aud              : JWT.QuotedFieldInput p MAX_AUD_KV_PAIR_LEN MAX_AUD_NAME_LEN MAX_AUD_VALUE_LEN
  audOverride      : AudOverrideInput p
  uid              : JWT.QuotedFieldInput p MAX_UID_KV_PAIR_LEN MAX_UID_NAME_LEN MAX_UID_VALUE_LEN
  iss              : JWT.QuotedFieldInput p MAX_ISS_KV_PAIR_LEN MAX_ISS_NAME_LEN MAX_ISS_VALUE_LEN
  iat              : JWT.UnquotedFieldInput p MAX_IAT_KV_PAIR_LEN MAX_IAT_NAME_LEN MAX_IAT_VALUE_LEN
  nonce            : JWT.QuotedFieldInput p MAX_NONCE_KV_PAIR_LEN MAX_NONCE_NAME_LEN MAX_NONCE_VALUE_LEN
  ev               : EvFieldInput p MAX_EV_KV_PAIR_LEN MAX_EV_NAME_LEN MAX_EV_VALUE_LEN
  extra            : ExtraFieldInput p
  commit           : CommitmentInput p
  publicInputsHash : F p

/-- The left half of a `Converts` fact about two conversions laid end to end. The reverse
direction of `converts_append_of_eq`; no such combinator exists in the shared library yet, so it
is kept local to this file. -/
private lemma converts_append_fst
  {p : ℕ} {α₁ α₂ α₃ : Type}
  {C₁ : Conversion p α₁} {C₂ : Conversion p α₂} {C₃ : Conversion p α₃}
  {state : ClapMState p}
  {x₁ : α₁} {x₂ : α₂} {x₃ : α₃}
  {v₁ : C₁.IdealT} {v₂ : C₂.IdealT} {v₃ : C₃.IdealT}
  (h : Converts C₃ state x₃ v₃)
  (h_ptr : C₃.toExprs x₃ = C₁.toExprs x₁ ++ C₂.toExprs x₂)
  (h_val : C₃.conversion v₃ = C₁.conversion v₁ ++ C₂.conversion v₂)
  (h_len₁ : (C₁.conversion v₁).length = (C₁.toExprs x₁).length)
:
  Converts C₁ state x₁ v₁
:= by
  obtain ⟨_, varSet, wf, val⟩ := h
  refine ⟨h_len₁, ?_, ?_, ?_⟩
  · intro ⟨i, h_i⟩
    have hi : i < (C₁.toExprs x₁).length := by simpa using h_i
    have h_i3 : i < (C₃.toExprs x₃).length := by rw [h_ptr, List.length_append]; omega
    simpa [Fin.getElem_fin, h_ptr, List.getElem_append_left hi] using varSet ⟨i, h_i3⟩
  · intro ⟨i, h_i⟩
    have hi : i < (C₁.toExprs x₁).length := by simpa using h_i
    have h_i3 : i < (C₃.toExprs x₃).length := by rw [h_ptr, List.length_append]; omega
    simpa [Fin.getElem_fin, h_ptr, List.getElem_append_left hi] using wf ⟨i, h_i3⟩
  · intro ⟨i, h_i⟩
    have hi : i < (C₁.toExprs x₁).length := by simpa using h_i
    have hi' : i < (C₁.conversion v₁).length := by rw [h_len₁]; exact hi
    have h_i3 : i < (C₃.toExprs x₃).length := by rw [h_ptr, List.length_append]; omega
    simpa [Fin.getElem_fin, h_ptr, h_val, List.getElem_append_left hi,
      List.getElem_append_left hi'] using val ⟨i, h_i3⟩

/-- The right half of a `Converts` fact about two conversions laid end to end. -/
private lemma converts_append_snd
  {p : ℕ} {α₁ α₂ α₃ : Type}
  {C₁ : Conversion p α₁} {C₂ : Conversion p α₂} {C₃ : Conversion p α₃}
  {state : ClapMState p}
  {x₁ : α₁} {x₂ : α₂} {x₃ : α₃}
  {v₁ : C₁.IdealT} {v₂ : C₂.IdealT} {v₃ : C₃.IdealT}
  (h : Converts C₃ state x₃ v₃)
  (h_ptr : C₃.toExprs x₃ = C₁.toExprs x₁ ++ C₂.toExprs x₂)
  (h_val : C₃.conversion v₃ = C₁.conversion v₁ ++ C₂.conversion v₂)
  (h_len₁ : (C₁.conversion v₁).length = (C₁.toExprs x₁).length)
  (h_len₂ : (C₂.conversion v₂).length = (C₂.toExprs x₂).length)
:
  Converts C₂ state x₂ v₂
:= by
  obtain ⟨_, varSet, wf, val⟩ := h
  refine ⟨h_len₂, ?_, ?_, ?_⟩
  · intro ⟨i, h_i⟩
    have hi : i < (C₂.toExprs x₂).length := by simpa using h_i
    have h_i3 : (C₁.toExprs x₁).length + i < (C₃.toExprs x₃).length := by
      rw [h_ptr, List.length_append]; omega
    simpa [Fin.getElem_fin, h_ptr,
      List.getElem_append_right (show (C₁.toExprs x₁).length ≤ (C₁.toExprs x₁).length + i by omega),
      Nat.add_sub_cancel_left] using varSet ⟨(C₁.toExprs x₁).length + i, h_i3⟩
  · intro ⟨i, h_i⟩
    have hi : i < (C₂.toExprs x₂).length := by simpa using h_i
    have h_i3 : (C₁.toExprs x₁).length + i < (C₃.toExprs x₃).length := by
      rw [h_ptr, List.length_append]; omega
    simpa [Fin.getElem_fin, h_ptr,
      List.getElem_append_right (show (C₁.toExprs x₁).length ≤ (C₁.toExprs x₁).length + i by omega),
      Nat.add_sub_cancel_left] using wf ⟨(C₁.toExprs x₁).length + i, h_i3⟩
  · intro ⟨i, h_i⟩
    have hi : i < (C₂.toExprs x₂).length := by simpa using h_i
    have hi' : i < (C₂.conversion v₂).length := by rw [h_len₂]; exact hi
    have h_i3 : (C₁.toExprs x₁).length + i < (C₃.toExprs x₃).length := by
      rw [h_ptr, List.length_append]; omega
    simpa [Fin.getElem_fin, h_ptr, h_val, h_len₁,
      List.getElem_append_right (show (C₁.toExprs x₁).length ≤ (C₁.toExprs x₁).length + i by omega),
      List.getElem_append_right (show (C₁.conversion v₁).length ≤ (C₁.toExprs x₁).length + i by
        rw [h_len₁]; omega),
      Nat.add_sub_cancel_left] using val ⟨(C₁.toExprs x₁).length + i, h_i3⟩

/-- Precomputed JSON structural data for the decoded JWT payload. -/
structure JSONStructure (p) where
  payload          : FString p MAX_JWT_PAYLOAD_LEN
  payloadHash      : F p
  stringBodies     : FArray p MAX_JWT_PAYLOAD_LEN --PaddedVector (FB p) p MAX_JWT_PAYLOAD_LEN
  bracketsDepthMap : FVec p MAX_JWT_PAYLOAD_LEN

namespace JSONStructure

abbrev JSONStructureIdealType p :=
  String × ZMod p × Vector Bool MAX_JWT_PAYLOAD_LEN × Vector (ZMod p) MAX_JWT_PAYLOAD_LEN

abbrev conversion {p} : Conversion p (JSONStructure p) where
  IdealT := JSONStructureIdealType p
    -- String × ZMod p × Vector Bool MAX_JWT_PAYLOAD_LEN × Vector (ZMod p) MAX_JWT_PAYLOAD_LEN
  toExprs x :=
    FString.conversion.toExprs x.payload ++
    F.conversion.toExprs x.payloadHash ++
    FArray.conversion.toExprs x.stringBodies ++
    FVec.conversion.toExprs x.bracketsDepthMap
  conversion
    | ⟨s, z, bs, zs⟩ =>
    FString.conversion (w := MAX_JWT_PAYLOAD_LEN).conversion s ++
    F.conversion.conversion z ++
    FArray.conversion.conversion bs ++
    FVec.conversion.conversion zs

-- Intermediate conversions matching the left-associated `++` nesting above, so that
-- `converts_append_of_eq` / `converts_append_fst` / `converts_append_snd` can be chained against
-- them and the result cast into `conversion` via `converts_cast`.
private abbrev C12 (p : ℕ) : Conversion p (FString p MAX_JWT_PAYLOAD_LEN × F p) where
  IdealT := String × ZMod p
  toExprs e := FString.conversion.toExprs e.1 ++ F.conversion.toExprs e.2
  conversion v :=
    FString.conversion (w := MAX_JWT_PAYLOAD_LEN).conversion v.1 ++ F.conversion.conversion v.2

private abbrev C123 (p : ℕ) :
    Conversion p ((FString p MAX_JWT_PAYLOAD_LEN × F p) × FArray p MAX_JWT_PAYLOAD_LEN) where
  IdealT := (String × ZMod p) × Vector Bool MAX_JWT_PAYLOAD_LEN
  toExprs e := (C12 p).toExprs e.1 ++ FArray.conversion.toExprs e.2
  conversion v := (C12 p).conversion v.1 ++ FArray.conversion.conversion v.2

private abbrev C1234 (p : ℕ) :
    Conversion p
      (((FString p MAX_JWT_PAYLOAD_LEN × F p) × FArray p MAX_JWT_PAYLOAD_LEN) ×
        FVec p MAX_JWT_PAYLOAD_LEN) where
  IdealT :=
    ((String × ZMod p) × Vector Bool MAX_JWT_PAYLOAD_LEN) × Vector (ZMod p) MAX_JWT_PAYLOAD_LEN
  toExprs e := (C123 p).toExprs e.1 ++ FVec.conversion.toExprs e.2
  conversion v := (C123 p).conversion v.1 ++ FVec.conversion.conversion v.2

lemma converts_intro {p} {state : ClapMState p}
  {s : JSONStructure p}
  {x : JSONStructureIdealType p}
  (h_payload : Converts FString.conversion state s.payload x.1)
  (h_payloadHash : Converts F.conversion state s.payloadHash x.2.1)
  (h_stringBodies : Converts FArray.conversion state s.stringBodies x.2.2.1)
  (h_bracketsDepthMap : Converts FVec.conversion state s.bracketsDepthMap x.2.2.2)
  :
  Converts conversion state s x
:= by
  have h12 : Converts (C12 p) state (s.payload, s.payloadHash) (x.1, x.2.1) :=
    converts_append_of_eq h_payload h_payloadHash rfl rfl
  have h123 :
      Converts (C123 p) state ((s.payload, s.payloadHash), s.stringBodies)
        ((x.1, x.2.1), x.2.2.1) :=
    converts_append_of_eq h12 h_stringBodies rfl rfl
  have h1234 :
      Converts (C1234 p) state
        (((s.payload, s.payloadHash), s.stringBodies), s.bracketsDepthMap)
        (((x.1, x.2.1), x.2.2.1), x.2.2.2) :=
    converts_append_of_eq h123 h_bracketsDepthMap rfl rfl
  exact converts_cast h1234 rfl rfl

lemma converts_payload {p} {state : ClapMState p}
  {s : JSONStructure p}
  {x : JSONStructureIdealType p}
  (h : Converts conversion state s x) :
  Converts FString.conversion state s.payload x.1
:= by
  have h_cast :
      Converts (C1234 p) state
        (((s.payload, s.payloadHash), s.stringBodies), s.bracketsDepthMap)
        (((x.1, x.2.1), x.2.2.1), x.2.2.2) :=
    converts_cast h rfl rfl
  have h123 := converts_append_fst h_cast rfl rfl (by simp)
  have h12 := converts_append_fst h123 rfl rfl (by simp)
  exact converts_append_fst h12 rfl rfl (by simp)

lemma converts_payloadHash {p} {state : ClapMState p}
  {s : JSONStructure p}
  {x : JSONStructureIdealType p}
  (h : Converts conversion state s x) :
  Converts F.conversion state s.payloadHash x.2.1
:= by
  have h_cast :
      Converts (C1234 p) state
        (((s.payload, s.payloadHash), s.stringBodies), s.bracketsDepthMap)
        (((x.1, x.2.1), x.2.2.1), x.2.2.2) :=
    converts_cast h rfl rfl
  have h123 := converts_append_fst h_cast rfl rfl (by simp)
  have h12 := converts_append_fst h123 rfl rfl (by simp)
  exact converts_append_snd h12 rfl rfl (by simp) (by simp)

lemma converts_stringBodies {p} {state : ClapMState p}
  {s : JSONStructure p}
  {x : JSONStructureIdealType p}
  (h : Converts conversion state s x) :
  Converts FArray.conversion state s.stringBodies x.2.2.1
:= by
  have h_cast :
      Converts (C1234 p) state
        (((s.payload, s.payloadHash), s.stringBodies), s.bracketsDepthMap)
        (((x.1, x.2.1), x.2.2.1), x.2.2.2) :=
    converts_cast h rfl rfl
  have h123 := converts_append_fst h_cast rfl rfl (by simp)
  exact converts_append_snd h123 rfl rfl (by simp) (by simp)

lemma converts_bracketsDepthMap {p} {state : ClapMState p}
  {s : JSONStructure p}
  {x : JSONStructureIdealType p}
  (h : Converts conversion state s x) :
  Converts FVec.conversion state s.bracketsDepthMap x.2.2.2
:= by
  have h_cast :
      Converts (C1234 p) state
        (((s.payload, s.payloadHash), s.stringBodies), s.bracketsDepthMap)
        (((x.1, x.2.1), x.2.2.1), x.2.2.2) :=
    converts_cast h rfl rfl
  exact converts_append_snd h_cast rfl rfl (by simp) (by simp)

end JSONStructure

end Clap
