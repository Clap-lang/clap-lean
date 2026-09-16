import Clap.eDSLState.Monad
import Clap.eDSLState.Convert.Specialised
import Clap.eDSLState.ConstraintSystem.toCs
import Clap.eDSLState.WitnessGenerator.toWg

namespace Clap

open Lang

def allocAThing {p} (numAlloc : ℕ) : HashConsM p (F p × ℕ) := do
  let x ← HashConsM.mkVar numAlloc
  return (x, numAlloc + 1)

def keyLessImpl {p} (e : ExprRef) : ClapM p Unit := do
  eq0 e


def keyLess {p} : ClapM p Unit := do
  let thingFromIt ← ClapM.alloc
  -- Not well formed, but: if keyLessImpl has convertsM and the function
  -- before it bumps numAlloc a certain amount and varstore is allocated up to that,
  -- then constraints ↔ spec
  keyLessImpl thingFromIt

structure theEnvisaged (p : ℕ) where
  StructExprRef : Type
  keyless : StructExprRef → ClapM p Unit
  numAlloc : ℕ
  allocate : HashConsM p StructExprRef

-- def inputsVarStore
--   {p} {α}
--   (conversion : Conversion p α)
--   (input : conversion.IdealT)
-- : VarStore p :=
--   .ofList ((conversion.conversion input).zipIdx.map Prod.swap)

-- def inputsHashConsState
--   {p}
--   (width : ℕ)
-- : HashConsSt p where
--   exprs := (Array.range width).map λ (x : ℕ) => CacheExpr.c (x : ZMod p)
--   wellFormed := by grind

-- def inputsState
--   {p} {α}
--   (conversion : Conversion p α)
--   (input : conversion.IdealT)
-- : ClapMState p where
--   varStore := inputsVarStore conversion input
--   σ := inputsHashConsState (conversion.conversion input).length
--   numAlloc := (conversion.conversion input).length

-- lemma full
--   {conversion : Conversion p α}
--   {input : conversion.IdealT}
--   (h_inputs : Converts conversion )
--   (h_function : ConvertsM FUnit.conversion (function inputs) (inputsState conversion input))
-- :


def constraintsKeyless {p} (te : theEnvisaged (p := p)) : ConstraintSystem p :=
  let (inputs, σ) := te.allocate.run (HashConsSt.empty p)
  ((te.keyless inputs).getCircuit te.numAlloc σ).toCs (p := p) σ te.numAlloc

def witnessKeyless {p} (te : theEnvisaged (p := p)) : WitnessGenerator p :=
  let (inputs, σ) := te.allocate.run (HashConsSt.empty p)
  ((te.keyless inputs).getCircuit te.numAlloc σ).toWg (p := p) σ te.numAlloc

def constraints {p} (numAlloc : ℕ) (σ : HashConsSt p) :=
  (keyLess.getCircuit numAlloc σ).toCs (p := p)

def witness {p} (numAlloc : ℕ) (σ : HashConsSt p) :=
  (keyLess.getCircuit numAlloc σ).toWg (p := p)

-- def FKeylessInput.conversion {p} : Conversion p FKeylessInput := sorry
-- def inputWidth : ℕ := sorry
-- lemma fixedWidth {p} : ∀ i : FKeylessInput, (FKeylessInput.conversion.toExprs (p := p) i).length = inputWidth := by sorry
-- def keylessProgram {p} (input : FKeylessInput) : ClapM p Unit := do
--   pure ()



-- Constants (from main.circom)

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







abbrev F8 (p) := F p

structure PaddedVector (α : Type) (p w : ℕ) where
  data : Vector α w
  len : F p

abbrev FString (p maxLen : ℕ) := PaddedVector (F8 p) p maxLen

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

section mkInput

variable {p numAlloc : ℕ} {σ : HashConsSt p} {α : Type}

def mkInputF (numAlloc : ℕ) : HashConsM p (F p × ℕ) := do
  let x ← HashConsM.mkVar numAlloc
  return (x, numAlloc + 1)

@[simp, grind =]
lemma numAlloc_mkInputF :
  (ClapM.getResult (p := p) (liftM (mkInputF (p := p) numAlloc)) numAlloc σ).2 =
  numAlloc + 1 := rfl

def mkInputF8 (numAlloc : ℕ) : HashConsM p (F8 p × ℕ) := do
  let x ← HashConsM.mkVar numAlloc
  return (x, numAlloc + 1)

@[simp, grind =]
lemma numAlloc_mkInputF8 :
  (ClapM.getResult (p := p) (liftM (mkInputF8 (p := p) numAlloc)) numAlloc σ).2 =
  numAlloc + 1 := rfl  

def mkInputFB {p} (numAlloc : ℕ) : HashConsM p (FB p × ℕ) := do
  let x ← HashConsM.mkVar numAlloc
  return (x, numAlloc + 1)

@[simp, grind =]
lemma numAlloc_mkInputFB :
  (ClapM.getResult (p := p) (liftM (mkInputFB (p := p) numAlloc)) numAlloc σ).2 =
  numAlloc + 1 := rfl  

def mkInputFString (numAlloc : ℕ) (maxLen : ℕ) : HashConsM p (FString p maxLen × ℕ) := do
  let (data, _numAllocs) ← Vector.unzip <$> ((Vector.range maxLen).map (·+numAlloc)).mapM mkInputF8
  let numAlloc := numAlloc + maxLen
  let (len, numAlloc) ← mkInputF8 numAlloc
  return (⟨data, len⟩, numAlloc)

@[simp, grind =]
lemma numAlloc_mkInputFString {maxLen} :
  (ClapM.getResult (p := p) (liftM (mkInputFString (p := p) numAlloc maxLen)) numAlloc σ).2 =
  numAlloc + maxLen + 1 := rfl

def mkInputFBPaddedVector (numAlloc : ℕ) (maxLen : ℕ) : HashConsM p (PaddedVector (FB p) p maxLen × ℕ) := do
  let (data, _numAllocs) ← Vector.unzip <$> ((Vector.range maxLen).map (·+numAlloc)).mapM mkInputFB
  let numAlloc := numAlloc + maxLen
  let (len, numAlloc) ← mkInputF8 numAlloc
  return (⟨data, len⟩, numAlloc)

@[simp, grind =]
lemma numAlloc_mkInputFBPaddedVector {maxLen} :
  (ClapM.getResult (p := p) (liftM (mkInputFBPaddedVector (p := p) numAlloc maxLen)) numAlloc σ).2 =
  numAlloc + maxLen + 1 := rfl

def mkInputVectorF (numAlloc k : ℕ) : HashConsM p (Vector (F p) k × ℕ) := do
  let (data, _numAllocs) ← Vector.unzip <$> ((Vector.range k).map (·+numAlloc)).mapM mkInputF
  return (data, numAlloc + k)

@[simp, grind =]
lemma numAlloc_mkInputVectorF {k} :
  (ClapM.getResult (p := p) (liftM (mkInputVectorF (p := p) numAlloc k)) numAlloc σ).2 =
  numAlloc + k := rfl

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
lemma numAlloc_mkInputJWTRawInput :
  (ClapM.getResult (p := p) (liftM (mkInputJWTRawInput (p := p) numAlloc)) numAlloc σ).2 =
  numAlloc +
  MAX_B64U_JWT_NO_SIG_LEN + 1 +
  MAX_B64U_JWT_HEADER_W_DOT_LEN + 1 +
  MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN + 1 +
  MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN + 1 +
  1 +
  SHA2_NUM_BITS_LEN +
  SHA2_PADDING_LEN  := rfl

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
lemma numAlloc_mkInputRSAInput :
  (ClapM.getResult (p := p) (liftM (mkInputRSAInput (p := p) numAlloc)) numAlloc σ).2 =
  numAlloc + RSA_NUM_LIMBS + RSA_NUM_LIMBS := rfl

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
lemma numAlloc_mkInputJWTQuotedFieldInput {maxPairLen maxNameLen maxValueLen} :
  (ClapM.getResult (p := p) (liftM (mkInputJWTQuotedFieldInput (p := p) numAlloc maxPairLen maxNameLen maxValueLen)) numAlloc σ).2 =
  numAlloc +
  maxPairLen + 1 +
  maxNameLen + 1 +
  maxValueLen + 1 +
  maxPairLen + 1 +
  1 +
  1 +
  1 := rfl

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
lemma numAlloc_mkInputAudOverrideInput :
  (ClapM.getResult (p := p) (liftM (mkInputAudOverrideInput (p := p) numAlloc)) numAlloc σ).2 =
  numAlloc +
  1 +
  1 +
  MAX_AUD_VALUE_LEN + 1 + 
  MAX_AUD_VALUE_LEN + 1 := rfl

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
lemma numAlloc_mkInputJWTUnquotedFieldInput {maxPairLen maxNameLen maxValueLen} :
  (ClapM.getResult (p := p)
    (liftM (mkInputJWTUnquotedFieldInput (p := p) numAlloc maxPairLen maxNameLen maxValueLen)) numAlloc σ).2 =
  numAlloc +
  maxPairLen + 1 +
  maxNameLen + 1 +
  maxValueLen + 1 +
  1 + 1 + 1 := rfl

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
lemma numAlloc_mkInputEvFieldInput {maxPairLen maxNameLen maxValueLen} :
  (ClapM.getResult (p := p)
    (liftM (mkInputEvFieldInput (p := p) numAlloc maxPairLen maxNameLen maxValueLen)) numAlloc σ).2 =
  numAlloc +
  maxPairLen + 1 +
  maxNameLen + 1 +
  maxValueLen + 1 +
  1 +
  1 +
  1 := rfl

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
lemma numAlloc_mkInputExtraFieldInput :
  (ClapM.getResult (p := p)
    (liftM (mkInputExtraFieldInput (p := p) numAlloc)) numAlloc σ).2 =
  numAlloc +
  MAX_EXTRA_FIELD_KV_PAIR_LEN + 1 +
  1 + 
  1 := rfl

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
lemma numAlloc_mkInputCommitmentInput :
  (ClapM.getResult (p := p) (liftM (mkInputCommitmentInput (p := p) numAlloc)) numAlloc σ).2 =
  numAlloc + EPK_NUM_FIELDS + 1 + 1 + 1 + 1 + 1 
  := by
  rfl

end mkInput

def keyless (p : ℕ) : theEnvisaged p where
  StructExprRef := FKeylessInput p
  keyless := keylessProgram
  numAlloc := inputWidth
  allocate := do
    let numAlloc := 0
    let (jwtRaw, numAlloc)            ← mkInputJWTRawInput numAlloc
    let (rsa, numAlloc)               ← mkInputRSAInput numAlloc
    let (aud, numAlloc)               ← mkInputJWTQuotedFieldInput numAlloc MAX_AUD_KV_PAIR_LEN MAX_AUD_NAME_LEN MAX_AUD_VALUE_LEN
    let (audOverride, numAlloc)       ← mkInputAudOverrideInput numAlloc
    let (uid, numAlloc)               ← mkInputJWTQuotedFieldInput numAlloc MAX_UID_KV_PAIR_LEN MAX_UID_NAME_LEN MAX_UID_VALUE_LEN
    let (iss, numAlloc)               ← mkInputJWTQuotedFieldInput numAlloc MAX_ISS_KV_PAIR_LEN MAX_ISS_NAME_LEN MAX_ISS_VALUE_LEN
    let (iat, numAlloc)               ← mkInputJWTUnquotedFieldInput numAlloc MAX_IAT_KV_PAIR_LEN MAX_IAT_NAME_LEN MAX_IAT_VALUE_LEN
    let (nonce, numAlloc)             ← mkInputJWTQuotedFieldInput numAlloc MAX_NONCE_KV_PAIR_LEN MAX_NONCE_NAME_LEN MAX_NONCE_VALUE_LEN
    let (ev, numAlloc)                ← mkInputEvFieldInput numAlloc MAX_EV_KV_PAIR_LEN MAX_EV_NAME_LEN MAX_EV_VALUE_LEN
    let (extra, numAlloc)             ← mkInputExtraFieldInput numAlloc
    let (commit, numAlloc)            ← mkInputCommitmentInput numAlloc
    let (publicInputsHash, numAlloc)  ← mkInputF numAlloc
    return {
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
    }
end Clap
