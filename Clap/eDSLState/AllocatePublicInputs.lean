import Clap.eDSLState.Monad
import Clap.eDSLState.Convert.Specialised
import Clap.eDSLState.ConstraintSystem.toCs
import Clap.eDSLState.WitnessGenerator.toWg
import Clap.Poseidon.NewPoseidon
import Clap.Lang.FUnit.assert_eq

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
  prawgrawm : StructExprRef → ClapM p Unit
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


def theEnvisaged.getCircuit {p} (te : theEnvisaged p) : Circuit × HashConsSt p :=
  let (inputs, σ) := te.allocate.run (HashConsSt.empty p)
  (
    (te.prawgrawm inputs).getCircuit te.numAlloc σ,
    (te.prawgrawm inputs).getHashConsState te.numAlloc σ
  )

def constraintsKeyless {p} (te : theEnvisaged (p := p)) : ConstraintSystem p :=
  let (circuit, σ) := te.getCircuit
  circuit.toCs (p := p) σ te.numAlloc

def witnessKeyless {p} (te : theEnvisaged (p := p)) : WitnessGenerator p :=
  let (circuit, σ) := te.getCircuit
  circuit.toWg (p := p) σ te.numAlloc

def constraints {p} (numAlloc : ℕ) (σ : HashConsSt p) :=
  (keyLess.getCircuit numAlloc σ).toCs (p := p)

def witness {p} (numAlloc : ℕ) (σ : HashConsSt p) :=
  (keyLess.getCircuit numAlloc σ).toWg (p := p)

def theEnvisaged.getConstraints {p} (te : theEnvisaged p) (inputs : Vector (ZMod p) te.numAlloc) :=
  let (circuit, σ) := te.getCircuit
  [.ofArray (inputs.toArray.zipIdx.map Prod.swap), σ, te.numAlloc|circuit]ₑ.constraints

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
def mkInputFWidth := 1

@[simp, grind =]
lemma numAlloc_mkInputF :
  (HashConsM.getResult (mkInputF numAlloc) σ).2 =
  numAlloc + mkInputFWidth := rfl

def mkInputF8 (numAlloc : ℕ) : HashConsM p (F8 p × ℕ) := do
  let x ← HashConsM.mkVar numAlloc
  return (x, numAlloc + 1)

@[simp, grind =]
def mkInputF8Width := 1

@[simp, grind =]
lemma numAlloc_mkInputF8 :
  (HashConsM.getResult (mkInputF8 numAlloc) σ).2 =
  numAlloc + mkInputF8Width := rfl  

def mkInputFB {p} (numAlloc : ℕ) : HashConsM p (FB p × ℕ) := do
  let x ← HashConsM.mkVar numAlloc
  return (x, numAlloc + 1)

@[simp, grind =]
def mkInputFBWidth := 1

@[simp, grind =]
lemma numAlloc_mkInputFB :
  (HashConsM.getResult (mkInputFB numAlloc) σ).2 =
  numAlloc + mkInputFBWidth := rfl

def mkInputFString (numAlloc : ℕ) (maxLen : ℕ) : HashConsM p (FString p maxLen × ℕ) := do
  let (data, _numAllocs) ← Vector.unzip <$> ((Vector.range maxLen).map (·+numAlloc)).mapM mkInputF8
  let numAlloc := numAlloc + maxLen
  let (len, numAlloc) ← mkInputF8 numAlloc
  return (⟨data, len⟩, numAlloc)

@[simp, grind =]
def mkInputFStringWidth (maxLen : ℕ) := maxLen + 1

@[simp, grind =]
lemma numAlloc_mkInputFString {maxLen} :
  (HashConsM.getResult (p := p) (mkInputFString (p := p) numAlloc maxLen) σ).2 =
  numAlloc + mkInputFStringWidth maxLen := rfl

def mkInputFBPaddedVector (numAlloc : ℕ) (maxLen : ℕ) : HashConsM p (PaddedVector (FB p) p maxLen × ℕ) := do
  let (data, _numAllocs) ← Vector.unzip <$> ((Vector.range maxLen).map (·+numAlloc)).mapM mkInputFB
  let numAlloc := numAlloc + maxLen
  let (len, numAlloc) ← mkInputF8 numAlloc
  return (⟨data, len⟩, numAlloc)

@[simp, grind =]
def mkInputFBPaddedVectorWidth (maxLen : ℕ) := maxLen + 1

@[simp, grind =]
lemma numAlloc_mkInputFBPaddedVector {maxLen} :
  (HashConsM.getResult (p := p) (mkInputFBPaddedVector (p := p) numAlloc maxLen) σ).2 =
  numAlloc + mkInputFBPaddedVectorWidth maxLen := rfl

def mkInputVectorF (numAlloc k : ℕ) : HashConsM p (Vector (F p) k × ℕ) := do
  let (data, _numAllocs) ← Vector.unzip <$> ((Vector.range k).map (·+numAlloc)).mapM mkInputF
  return (data, numAlloc + k)

@[simp, grind =]
def mkInputVectorFWidth (k : ℕ) := k

@[simp, grind =]
lemma numAlloc_mkInputVectorF {k} :
  (HashConsM.getResult (p := p) (mkInputVectorF (p := p) numAlloc k) σ).2 =
  numAlloc + mkInputVectorFWidth k := rfl

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

def keyless (p : ℕ) : theEnvisaged p where
  StructExprRef := FKeylessInput p
  prawgrawm := fun _ ↦ return ()
  numAlloc := allocateKeylessWidth
  allocate := allocateKeyless

def poseidon_the_envisaged (k : ℕ) : theEnvisaged Primes.bn254 where
  StructExprRef := (Vector (F Primes.bn254) k × F Primes.bn254)
  prawgrawm := fun (input, hash) ↦ do
    let result ← poseidonBN254 input
    assert_eq result hash
  numAlloc := k + 1
  allocate := do
    let (vec, numAlloc) ← mkInputVectorF 0 k
    let (f, _numAlloc) ← mkInputF numAlloc
    return (vec, f)

/--
This be da spec, mon'.
-/
opaque poseidon_the_opaque {k} (inputs : Vector (ZMod Primes.bn254) k) : ZMod Primes.bn254

theorem poseidon.convertsM_convertsMs
  {k}
  {inputs : Vector (F Primes.bn254) k} {state}
  {input_vals : Vector (ZMod Primes.bn254) k}
  (h : ∀ i : Fin k, Converts F.conversion state inputs[i] input_vals[i])
  :
  ConvertsM F.conversion (poseidonBN254 inputs) state (poseidon_the_opaque input_vals) True := by
  sorry

@[grind =]
lemma _root_.Clap.HashConsM.getHashConsState_bind
  {α β p}
  {action : HashConsM p α} {function : α → HashConsM p β}
  {σ : HashConsSt p}
:
  (action >>= function).getHashConsState σ =
  ((function (action.getResult σ)).getHashConsState (action.getHashConsState σ))
:= rfl

@[simp, grind =]
lemma _root_.Clap.HashConsM.getHashConsState_map
  {α β p}
  {action : HashConsM p α} {function : α → β}
  {σ : HashConsSt p}
:
  (function <$> action).getHashConsState σ =
  action.getHashConsState σ
:= rfl

theorem poseidon_the_specd
  {k}
  {state}
  {input : Vector (F Primes.bn254) k × F Primes.bn254}
  {input_vals : Vector (ZMod Primes.bn254) k}
  {input_val2 : ZMod Primes.bn254}
  (h₀ : Converts F.conversion state input.2 input_val2)
  (h : ∀ i : Fin k, Converts F.conversion state input.1[i] input_vals[i])
  :
  ConvertsM FUnit.conversion
    ((poseidon_the_envisaged k).prawgrawm input) state ()
    (poseidon_the_opaque input_vals = input_val2) := by
  unfold poseidon_the_envisaged
  dsimp
  step poseidon.convertsM_convertsMs h as poseidon
  apply convertsM_of_convertsM (assert_eq.convertsM h_poseidon h₀) rfl
  simp

lemma theLemma {α β : Type} [Ord α] [inst : Std.TransCmp (compare (α := α))] [Std.LawfulEqCmp (compare (α := α))] {kvPairs : List (α × β)} : 
  Std.ExtTreeMap.ofArray kvPairs.toArray compare = Std.ExtTreeMap.ofList kvPairs compare := by
  ext k v
  unfold Std.ExtTreeMap.ofArray
  unfold Std.ExtTreeMap.ofList
  unfold Std.ExtDTreeMap.Const.ofArray
  unfold Std.ExtDTreeMap.Const.ofList
  unfold Std.DTreeMap.Const.ofArray
  unfold Std.DTreeMap.Const.ofList
  unfold Std.DTreeMap.Internal.Impl.Const.ofArray
  unfold Std.DTreeMap.Internal.Impl.Const.ofList
  unfold Std.DTreeMap.Internal.Impl.Const.insertMany
  unfold_projs
  simp
  rfl

abbrev _root_.Clap.Lang.FVector.conversion {p} {k} : Conversion p (Vector (F p) k) where
  IdealT := Vector (ZMod p) k
  toExprs x := x.toList
  conversion x := x.toList

theorem tutatis {k : ℕ} {numAlloc} {input : Vector (ZMod Primes.bn254) (k + 1)} :
  ∀ (i : Fin k),
    ConvertsM FVector.conversion (mkInputVectorF numAlloc k) := sorry


theorem odysseus
  {k}
  {input : Vector (ZMod Primes.bn254) (k + 1)} :
  (poseidon_the_envisaged k).getConstraints input ↔
  letI inputInit := input.take k
  letI inputLast := input.back!
  poseidon_the_opaque inputInit = inputLast := by
  unfold theEnvisaged.getConstraints
  dsimp [theEnvisaged.getCircuit]
  set numAlloc := (poseidon_the_envisaged k).numAlloc with eq₁
  simp_rw [←eq₁]
  set varStore := Std.ExtTreeMap.ofArray (Array.map Prod.swap input.toArray.zipIdx) compare with eq₂
  set σ := ((poseidon_the_envisaged k).allocate.run (HashConsSt.empty Primes.bn254)).2 with eq₃
  set cmd := (poseidon_the_envisaged k).prawgrawm
               ((poseidon_the_envisaged k).allocate.run (HashConsSt.empty Primes.bn254)).1 with eq₄
  set inputRef := ((poseidon_the_envisaged k).allocate.run (HashConsSt.empty Primes.bn254)).1 with eq₅
  set state : ClapMState Primes.bn254 := ⟨varStore, σ, numAlloc⟩
  change (cmd.runAndEval state.numAlloc state.varStore state.σ).2.constraints ↔ poseidon_the_opaque (input.extract 0 k) = input.back!
  subst cmd
  rw [(poseidon_the_specd _ _).constraints]
  swap
  exact Vector.cast (by grind) (input.take k)
  swap
  exact input.back!
  simp
  · constructor
    all_goals {
      intros h
      rw [←h]
      congr
      grind
      symm
      rcases input with ⟨array, h⟩
      simp
      grind
    }
  · unfold poseidon_the_envisaged
    dsimp
    constructor <;> simp
    · subst σ
      subst state numAlloc
      simp [←HashConsM.getHashConsState.eq_def]
      simp [←HashConsM.getResult.eq_def]
      dsimp [poseidon_the_envisaged]
      unfold mkInputF
      simp [Expr.varSet_wellFormed]
      rw [HashConsM.getHashConsState_bind]
      simp
    · subst σ
      subst state numAlloc
      simp [←HashConsM.getHashConsState.eq_def]
      simp [←HashConsM.getResult.eq_def]
      dsimp [poseidon_the_envisaged]
      simp [Expr.wellFormed]
      unfold mkInputF
      rw [HashConsM.getHashConsState_bind]
      simp
      exact HashConsM.getResult_lt_getHashConsState_size_mkVar
    · subst σ
      subst state numAlloc
      subst varStore
      simp [←HashConsM.getHashConsState.eq_def]
      simp [←HashConsM.getResult.eq_def]
      dsimp [poseidon_the_envisaged]
      unfold mkInputF
      rw [HashConsM.getHashConsState_bind]
      simp
      rw [eval_eq_evalRec (by grind)]
      rw [HashConsM.getResult_mkVar]
      rw [HashConsM.getHashConsState_mkVar]
      unfold Expr.evalRec
      
      simp_all only [Option.map_eq_map, inputRef]
      split
      next heq =>
        simp_all only [reduceCtorEq]
        (grind)
      next expr heq =>
        split
        next expr h k_1 h_1 =>
          simp_all only [Option.some.injEq]
          subst h
          (grind)
        next expr h idx h_1 =>
          simp_all only [Option.some.injEq]
          subst h
          split at heq
          all_goals {
            rcases input with ⟨⟨a⟩, c⟩
            simp
            have : idx = k := by grind
            subst this
            rw [theLemma]
            rw [Std.ExtTreeMap.ofList_eq_insertMany_empty]
            let aSplit := a.take idx ++ [a.getLast!]
            have : a = aSplit := by
              simp [aSplit]
              ext1 i
              grind
            rw [this]
            simp [aSplit]
            rw [List.zipIdx_append]
            simp
            rw [Std.ExtTreeMap.insertMany_append]
            simp
            grind
          }
        next expr h lhs rhs op h_1 =>
          simp_all only [Option.some.injEq]
          subst h
          (grind)
  · extract_goal
    unfold poseidon_the_envisaged
    dsimp
    intros i
    rcases i with ⟨i, hi⟩
    clear eq₁
    clear_value numAlloc
    clear eq₃
    clear_value σ
    clear_value inputRef
    clear eq₅
    clear eq₄


    induction' k with k ih generalizing σ
    · exfalso; grind
    · unfold mkInputVectorF mkInputF
      constructor <;> simp
      · simp [←HashConsM.getHashConsState.eq_def] at ih ⊢
        simp [←HashConsM.getResult.eq_def] at ih ⊢
        simp [Vector.mapM_succ]
        specialize @ih ((input.take (k + 1)).cast (by grind))
        rcases inputRef with ⟨vec, f⟩
        specialize ih ?yourFace ⟨vec.take k |>.cast (by grind), f⟩
        swap
        by_cases eq₉ : i < k
        · specialize ih (by grind)
          simp [Vector.range_succ]
          rw [Vector.getElem_push]
          simp [eq₉]
          rcases ih with ⟨_, here, _, _⟩
          specialize here 0
          
          simp [mkInputVectorF] at here
          delta mkInputF at here
          simp at here
          exact here
        · simp at eq₉
          have : i = k := by grind
          subst this
          rw [Vector.getElem_push]
          simp

          sorry
      · subst σ
        subst state numAlloc
        simp [←HashConsM.getHashConsState.eq_def]
        simp [←HashConsM.getResult.eq_def]
        dsimp [poseidon_the_envisaged]
        simp [Expr.wellFormed]
        unfold mkInputF
        rw [HashConsM.getHashConsState_bind]
        simp
        exact HashConsM.getResult_lt_getHashConsState_size_mkVar
      · subst σ
        subst state numAlloc
        subst varStore
        simp [←HashConsM.getHashConsState.eq_def]
        simp [←HashConsM.getResult.eq_def]
        dsimp [poseidon_the_envisaged]
        unfold mkInputF
        rw [HashConsM.getHashConsState_bind]
        simp
        rw [eval_eq_evalRec (by grind)]
        rw [HashConsM.getResult_mkVar]
        rw [HashConsM.getHashConsState_mkVar]
        unfold Expr.evalRec
        
        simp_all only [Option.map_eq_map, inputRef]
        split
        next heq =>
          simp_all only [reduceCtorEq]
          (grind)
        next expr heq =>
          split
          next expr h k_1 h_1 =>
            simp_all only [Option.some.injEq]
            subst h
            (grind)
          next expr h idx h_1 =>
            simp_all only [Option.some.injEq]
            subst h
            split at heq
            all_goals {
              rcases input with ⟨⟨a⟩, c⟩
              simp
              have : idx = k := by grind
              subst this
              rw [theLemma]
              rw [Std.ExtTreeMap.ofList_eq_insertMany_empty]
              let aSplit := a.take idx ++ [a.getLast!]
              have : a = aSplit := by
                simp [aSplit]
                ext1 i
                grind
              rw [this]
              simp [aSplit]
              rw [List.zipIdx_append]
              simp
              rw [Std.ExtTreeMap.insertMany_append]
              simp
              grind
            }
          next expr h lhs rhs op h_1 =>
            simp_all only [Option.some.injEq]
            subst h
            (grind)
  -- have := @poseidon_the_specd
  -- -- rw [(poseidon_the_specd _ _).constraints]
  -- have := @ClapM.runAndEval.eq_def
  -- rw [←ClapM.runAndEval.eq_def]

end Clap
