import Clap.Model.PublicInput
import Clap.Keyless.Input
/-!
# Keyless circuit public-input allocation

Allocators for the top-level Keyless circuit's input, built from the generic ones in
`Clap/Model/PublicInput.lean`. `allocateKeyless` is the `allocate` field of an
`AllocatedProgram`, and `allocateKeylessWidth` is its `numAlloc`.
-/

namespace Clap

open Lang

section mkInput

variable {p numAlloc : ℕ} {σ : HashConsSt p}

def mkInputJWTRawInput {p} (numAlloc : ℕ) : HashConsM p (JWTRawInput p × ℕ) := do
  let (b64u_jwt_no_sig_sha2_padded, numAlloc) ← mkInputFString numAlloc MAX_B64U_JWT_NO_SIG_LEN
  let (b64u_jwt_header_w_dot, numAlloc) ← mkInputFString numAlloc MAX_B64U_JWT_HEADER_W_DOT_LEN
  let (b64u_jwt_payload_sha2_padded, numAlloc) ← mkInputFString numAlloc MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN
  let (b64u_jwt_payload, numAlloc) ← mkInputFString numAlloc MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN
  let (sha2_num_blocks, numAlloc) ← mkInputF numAlloc
  let (sha2_num_bits, numAlloc) ← mkInputVectorF numAlloc SHA2_NUM_BITS_LEN
  let (sha2_padding, numAlloc) ← mkInputVectorF numAlloc SHA2_PADDING_LEN
  return (
    {
      b64u_jwt_no_sig_sha2_padded := b64u_jwt_no_sig_sha2_padded
      b64u_jwt_header_w_dot := b64u_jwt_header_w_dot
      b64u_jwt_payload_sha2_padded := b64u_jwt_payload_sha2_padded
      b64u_jwt_payload := b64u_jwt_payload
      sha2_num_blocks := sha2_num_blocks
      sha2_num_bits := sha2_num_bits
      sha2_padding := sha2_padding
    },
    numAlloc
  )

@[simp, grind =]
def mkInputJWTRawInputWidth :=
  MAX_B64U_JWT_NO_SIG_LEN + 1 +
  MAX_B64U_JWT_HEADER_W_DOT_LEN + 1 +
  MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN + 1 +
  MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN + 1 +
  1 +
  SHA2_NUM_BITS_LEN +
  SHA2_PADDING_LEN

@[simp, grind =]
lemma numAlloc_mkInputJWTRawInput :
  (HashConsM.getResult (p := p) (mkInputJWTRawInput (p := p) numAlloc) σ).2 =
  numAlloc + mkInputJWTRawInputWidth := by
  unfold mkInputJWTRawInputWidth
  simp only [←add_assoc]
  rfl

def mkInputRSAInput (numAlloc : ℕ) : HashConsM p (RSAInput p × ℕ) := do
  let (signature, numAlloc) ← mkInputVectorF numAlloc RSA_NUM_LIMBS
  let (pubkeyModulus, numAlloc) ← mkInputVectorF numAlloc RSA_NUM_LIMBS
  return (
    {
      signature := signature
      pubkeyModulus := pubkeyModulus
    },
    numAlloc
  )

@[simp, grind =]
def mkInputRSAInputWidth := RSA_NUM_LIMBS + RSA_NUM_LIMBS

@[simp, grind =]
lemma numAlloc_mkInputRSAInput :
  (HashConsM.getResult (p := p) (mkInputRSAInput (p := p) numAlloc) σ).2 =
  numAlloc + mkInputRSAInputWidth := rfl

def mkInputJWTQuotedFieldInput (numAlloc : ℕ) (maxPairLen maxNameLen maxValueLen) :
  HashConsM p (JWT.QuotedFieldInput p maxPairLen maxNameLen maxValueLen × ℕ) := do
  let (field, numAlloc) ← mkInputFString numAlloc maxPairLen
  let (name, numAlloc) ← mkInputFString numAlloc maxNameLen
  let (value, numAlloc) ← mkInputFString numAlloc maxValueLen
  let (fieldStringBodies, numAlloc) ← mkInputFBPaddedVector numAlloc maxPairLen
  let (nameIndex, numAlloc) ← mkInputF numAlloc
  let (colonIndex, numAlloc) ← mkInputF numAlloc
  let (valueIndex, numAlloc) ← mkInputF numAlloc
  return (
    {
      field := field
      name := name
      value := value
      fieldStringBodies := fieldStringBodies
      nameIndex := nameIndex
      colonIndex := colonIndex
      valueIndex := valueIndex
    },
    numAlloc
  )

@[simp, grind =]
def mkInputJWTQuotedFieldInputWidth (maxPairLen maxNameLen maxValueLen) :=
  maxPairLen + 1 +
  maxNameLen + 1 +
  maxValueLen + 1 +
  maxPairLen + 1 +
  1 +
  1 +
  1

@[simp, grind =]
lemma numAlloc_mkInputJWTQuotedFieldInput {maxPairLen maxNameLen maxValueLen} :
  (HashConsM.getResult (p := p) (mkInputJWTQuotedFieldInput (p := p) numAlloc maxPairLen maxNameLen maxValueLen) σ).2 =
  numAlloc +
  mkInputJWTQuotedFieldInputWidth maxPairLen maxNameLen maxValueLen := by
  unfold mkInputJWTQuotedFieldInputWidth
  simp only [←add_assoc]
  rfl

def mkInputAudOverrideInput (numAlloc : ℕ) : HashConsM p (AudOverrideInput p × ℕ) := do
  let (useAudOverride, numAlloc) ← mkInputF numAlloc
  let (skipAudChecks, numAlloc) ← mkInputF numAlloc
  let (privateAudValue, numAlloc) ← mkInputFString numAlloc MAX_AUD_VALUE_LEN
  let (overrideAudValue, numAlloc) ← mkInputFString numAlloc MAX_AUD_VALUE_LEN
  return (
    {
      useAudOverride := useAudOverride
      skipAudChecks := skipAudChecks
      privateAudValue := privateAudValue
      overrideAudValue := overrideAudValue
    },
    numAlloc
  )

@[simp, grind =]
def mkInputAudOverrideInputWidth :=
  1 +
  1 +
  MAX_AUD_VALUE_LEN + 1 +
  MAX_AUD_VALUE_LEN + 1

@[simp, grind =]
lemma numAlloc_mkInputAudOverrideInput :
  (HashConsM.getResult (p := p) (mkInputAudOverrideInput (p := p) numAlloc) σ).2 =
  numAlloc +
  mkInputAudOverrideInputWidth := by
  unfold mkInputAudOverrideInputWidth
  simp only [←add_assoc]
  rfl

def mkInputJWTUnquotedFieldInput (numAlloc : ℕ) (maxPairLen maxNameLen maxValueLen) :
  HashConsM p (JWT.UnquotedFieldInput p maxPairLen maxNameLen maxValueLen × ℕ) := do
  let (field, numAlloc) ← mkInputFString numAlloc maxPairLen
  let (name, numAlloc) ← mkInputFString numAlloc maxNameLen
  let (value, numAlloc) ← mkInputFString numAlloc maxValueLen
  let (nameIndex, numAlloc) ← mkInputF numAlloc
  let (colonIndex, numAlloc) ← mkInputF numAlloc
  let (valueIndex, numAlloc) ← mkInputF numAlloc
  return (
    {
      field := field
      name := name
      value := value
      nameIndex := nameIndex
      colonIndex := colonIndex
      valueIndex := valueIndex
    },
    numAlloc
  )

@[simp, grind =]
def mkInputJWTUnquotedFieldInputWidth (maxPairLen maxNameLen maxValueLen) :=
  maxPairLen + 1 +
  maxNameLen + 1 +
  maxValueLen + 1 +
  1 +
  1 +
  1

@[simp, grind =]
lemma numAlloc_mkInputJWTUnquotedFieldInput {maxPairLen maxNameLen maxValueLen} :
  (HashConsM.getResult (p := p)
    (mkInputJWTUnquotedFieldInput (p := p) numAlloc maxPairLen maxNameLen maxValueLen) σ).2 =
  numAlloc +
  mkInputJWTUnquotedFieldInputWidth maxPairLen maxNameLen maxValueLen := by
  unfold mkInputJWTUnquotedFieldInputWidth
  simp only [←add_assoc]
  rfl

def mkInputEvFieldInput (numAlloc : ℕ) (maxPairLen maxNameLen maxValueLen) :
  HashConsM p (EvFieldInput p maxPairLen maxNameLen maxValueLen × ℕ) := do
  let (field, numAlloc) ← mkInputFString numAlloc maxPairLen
  let (name, numAlloc) ← mkInputFString numAlloc maxNameLen
  let (value, numAlloc) ← mkInputFString numAlloc maxValueLen
  let (nameIndex, numAlloc) ← mkInputF numAlloc
  let (colonIndex, numAlloc) ← mkInputF numAlloc
  let (valueIndex, numAlloc) ← mkInputF numAlloc
  return (
    {
      field := field
      name := name
      value := value
      nameIndex := nameIndex
      colonIndex := colonIndex
      valueIndex := valueIndex
    },
    numAlloc
  )

@[simp, grind =]
def mkInputEvFieldInputWidth (maxPairLen maxNameLen maxValueLen) :=
  maxPairLen + 1 +
  maxNameLen + 1 +
  maxValueLen + 1 +
  1 +
  1 +
  1

@[simp, grind =]
lemma numAlloc_mkInputEvFieldInput {maxPairLen maxNameLen maxValueLen} :
  (HashConsM.getResult (p := p)
    (mkInputEvFieldInput (p := p) numAlloc maxPairLen maxNameLen maxValueLen) σ).2 =
  numAlloc +
  mkInputEvFieldInputWidth maxPairLen maxNameLen maxValueLen := by
  unfold mkInputEvFieldInputWidth
  simp only [←add_assoc]
  rfl

def mkInputExtraFieldInput (numAlloc : ℕ) :
  HashConsM p (ExtraFieldInput p × ℕ) := do
  let (extraField, numAlloc) ← mkInputFString numAlloc MAX_EXTRA_FIELD_KV_PAIR_LEN
  let (extraFieldIndex, numAlloc) ← mkInputF numAlloc
  let (useExtraField, numAlloc) ← mkInputF numAlloc
  return (
    {
      extraField := extraField
      extraFieldIndex := extraFieldIndex
      useExtraField := useExtraField
    },
    numAlloc
  )

@[simp, grind =]
def mkInputExtraFieldInputWidth :=
  MAX_EXTRA_FIELD_KV_PAIR_LEN + 1 +
  1 +
  1

@[simp, grind =]
lemma numAlloc_mkInputExtraFieldInput :
  (HashConsM.getResult (p := p)
    (mkInputExtraFieldInput (p := p) numAlloc) σ).2 =
  numAlloc +
  mkInputExtraFieldInputWidth := rfl

def mkInputCommitmentInput (numAlloc : ℕ) :
  HashConsM p (CommitmentInput p × ℕ) := do
  let (epk, numAlloc) ← mkInputVectorF numAlloc EPK_NUM_FIELDS
  let (epkLen, numAlloc) ← mkInputF numAlloc
  let (epkBlinder, numAlloc) ← mkInputF numAlloc
  let (expDate, numAlloc) ← mkInputF numAlloc
  let (expHorizon, numAlloc) ← mkInputF numAlloc
  let (pepper, numAlloc) ← mkInputF numAlloc
  return (
    {
      epk := epk
      epkLen := epkLen
      epkBlinder := epkBlinder
      expDate := expDate
      expHorizon := expHorizon
      pepper := pepper
    },
    numAlloc
  )

@[simp, grind =]
def mkInputCommitmentInputWidth := EPK_NUM_FIELDS + 1 + 1 + 1 + 1 + 1

@[simp, grind =]
lemma numAlloc_mkInputCommitmentInput :
  (HashConsM.getResult (p := p) (mkInputCommitmentInput (p := p) numAlloc) σ).2 =
  numAlloc + mkInputCommitmentInputWidth
  := by
  unfold mkInputCommitmentInputWidth
  simp only [←add_assoc]
  rfl

def allocateKeylessAux : HashConsM p (FKeylessInput p × ℕ) := do
  let numAlloc := 0
  let (jwtRaw, numAlloc)           ← mkInputJWTRawInput numAlloc
  let (rsa, numAlloc)              ← mkInputRSAInput numAlloc
  let (aud, numAlloc)              ← mkInputJWTQuotedFieldInput numAlloc MAX_AUD_KV_PAIR_LEN MAX_AUD_NAME_LEN MAX_AUD_VALUE_LEN
  let (audOverride, numAlloc)      ← mkInputAudOverrideInput numAlloc
  let (uid, numAlloc)              ← mkInputJWTQuotedFieldInput numAlloc MAX_UID_KV_PAIR_LEN MAX_UID_NAME_LEN MAX_UID_VALUE_LEN
  let (iss, numAlloc)              ← mkInputJWTQuotedFieldInput numAlloc MAX_ISS_KV_PAIR_LEN MAX_ISS_NAME_LEN MAX_ISS_VALUE_LEN
  let (iat, numAlloc)              ← mkInputJWTUnquotedFieldInput numAlloc MAX_IAT_KV_PAIR_LEN MAX_IAT_NAME_LEN MAX_IAT_VALUE_LEN
  let (nonce, numAlloc)            ← mkInputJWTQuotedFieldInput numAlloc MAX_NONCE_KV_PAIR_LEN MAX_NONCE_NAME_LEN MAX_NONCE_VALUE_LEN
  let (ev, numAlloc)               ← mkInputEvFieldInput numAlloc MAX_EV_KV_PAIR_LEN MAX_EV_NAME_LEN MAX_EV_VALUE_LEN
  let (extra, numAlloc)            ← mkInputExtraFieldInput numAlloc
  let (commit, numAlloc)           ← mkInputCommitmentInput numAlloc
  let (publicInputsHash, numAlloc) ← mkInputF numAlloc
  return (
    {
      jwtRaw := jwtRaw,
      rsa := rsa,
      aud := aud,
      audOverride := audOverride,
      uid := uid,
      iss := iss,
      iat := iat,
      nonce := nonce,
      ev := ev,
      extra := extra,
      commit := commit,
      publicInputsHash := publicInputsHash
    },
    numAlloc
  )

def allocateKeyless : HashConsM p (FKeylessInput p) := do
  let (theThing, _) ← allocateKeylessAux
  return theThing

@[simp, grind =]
def allocateKeylessWidth :=
  mkInputJWTRawInputWidth +
  mkInputRSAInputWidth +
  mkInputJWTQuotedFieldInputWidth MAX_AUD_KV_PAIR_LEN MAX_AUD_NAME_LEN MAX_AUD_VALUE_LEN +
  mkInputAudOverrideInputWidth +
  mkInputJWTQuotedFieldInputWidth MAX_UID_KV_PAIR_LEN MAX_UID_NAME_LEN MAX_UID_VALUE_LEN +
  mkInputJWTQuotedFieldInputWidth MAX_ISS_KV_PAIR_LEN MAX_ISS_NAME_LEN MAX_ISS_VALUE_LEN +
  mkInputJWTUnquotedFieldInputWidth MAX_IAT_KV_PAIR_LEN MAX_IAT_NAME_LEN MAX_IAT_VALUE_LEN +
  mkInputJWTQuotedFieldInputWidth MAX_NONCE_KV_PAIR_LEN MAX_NONCE_NAME_LEN MAX_NONCE_VALUE_LEN +
  mkInputEvFieldInputWidth MAX_EV_KV_PAIR_LEN MAX_EV_NAME_LEN MAX_EV_VALUE_LEN +
  mkInputExtraFieldInputWidth +
  mkInputCommitmentInputWidth +
  mkInputFWidth

@[simp, grind =]
lemma numAlloc_allocateKeylessWidth :
  (HashConsM.getResult (p := p) (allocateKeylessAux (p := p)) σ).2 =
  allocateKeylessWidth := by
  simp [allocateKeylessAux]

end mkInput

end Clap
