import Clap.Lang
import Clap.Wheels
import Clap.Array
import Clap.FString
import Clap.HashToField
import Clap.JWT
import Clap.Poseidon.Poseidon
import Clap.Base64Len
import Clap.Sha2.Keyless
import Clap.RSA

/-!
# Aptos Keyless Circuit

Top-level ZK circuit for Aptos Keyless accounts, translated from the CIRCOM reference at
`aptos-labs/keyless-zk-proofs/circuit/templates/{main,keyless}.circom`.

The circuit proves that a user controls a JWT from an OIDC provider (e.g., Google) without
revealing the JWT itself. It verifies JWT structure, RSA signature, field parsing, nonce
commitment, identity commitment, and produces a public inputs hash.

## References
- CIRCOM: https://github.com/aptos-labs/keyless-zk-proofs/tree/main/circuit/templates
- AIP-061: https://github.com/aptos-foundation/AIPs/blob/main/aips/aip-061-keyless-accounts.md
-/

namespace Keyless

open Clap.Lang Primes Clap.RSA

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

-- ============================================================================
-- Stubs for WIP components
-- ============================================================================

-- Input structures

/-- Email-verified field input (special parsing: value may be quoted or unquoted). -/
structure EvFieldInput (maxPairLen maxNameLen maxValueLen : ℕ) where
  field      : FString bn254 maxPairLen
  name       : FString bn254 maxNameLen
  value      : FString bn254 maxValueLen
  nameIndex  : F bn254
  colonIndex : F bn254
  valueIndex : F bn254

/-- JWT raw data and SHA2 signals. -/
structure JWTRawInput where
  b64u_jwt_no_sig_sha2_padded   : FString bn254 MAX_B64U_JWT_NO_SIG_LEN
  b64u_jwt_header_w_dot         : FString bn254 MAX_B64U_JWT_HEADER_W_DOT_LEN
  b64u_jwt_payload_sha2_padded  : FString bn254 MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN
  b64u_jwt_payload              : FString bn254 MAX_B64U_JWT_PAYLOAD_SHA2_PADDED_LEN
  sha2_num_blocks               : F bn254
  sha2_num_bits                 : Vector (F bn254) SHA2_NUM_BITS_LEN
  sha2_padding                  : Vector (F bn254) SHA2_PADDING_LEN

/-- RSA signature input: 32 × 64-bit limbs each. -/
structure RSAInput where
  signature     : Vector (F bn254) RSA_NUM_LIMBS
  pubkeyModulus : Vector (F bn254) RSA_NUM_LIMBS

/-- Audience override signals. -/
structure AudOverrideInput where
  useAudOverride   : F bn254
  skipAudChecks    : F bn254
  privateAudValue  : FString bn254 MAX_AUD_VALUE_LEN
  overrideAudValue : FString bn254 MAX_AUD_VALUE_LEN

/-- Extra field signals. -/
structure ExtraFieldInput where
  extraField      : FString bn254 MAX_EXTRA_FIELD_KV_PAIR_LEN
  extraFieldIndex : F bn254
  useExtraField   : F bn254

/-- Cryptographic commitment signals: EPK, expiration, pepper. -/
structure CommitmentInput where
  epk        : Vector (F bn254) EPK_NUM_FIELDS
  epkLen     : F bn254
  epkBlinder : F bn254
  expDate    : F bn254
  expHorizon : F bn254
  pepper     : F bn254

/-- Top-level Keyless circuit input. -/
structure KeylessInput where
  jwtRaw           : JWTRawInput
  rsa              : RSAInput
  aud              : JWT.QuotedFieldInput MAX_AUD_KV_PAIR_LEN MAX_AUD_NAME_LEN MAX_AUD_VALUE_LEN
  audOverride      : AudOverrideInput
  uid              : JWT.QuotedFieldInput MAX_UID_KV_PAIR_LEN MAX_UID_NAME_LEN MAX_UID_VALUE_LEN
  iss              : JWT.QuotedFieldInput MAX_ISS_KV_PAIR_LEN MAX_ISS_NAME_LEN MAX_ISS_VALUE_LEN
  iat              : JWT.UnquotedFieldInput MAX_IAT_KV_PAIR_LEN MAX_IAT_NAME_LEN MAX_IAT_VALUE_LEN
  nonce            : JWT.QuotedFieldInput MAX_NONCE_KV_PAIR_LEN MAX_NONCE_NAME_LEN MAX_NONCE_VALUE_LEN
  ev               : EvFieldInput MAX_EV_KV_PAIR_LEN MAX_EV_NAME_LEN MAX_EV_VALUE_LEN
  extra            : ExtraFieldInput
  commit           : CommitmentInput
  publicInputsHash : F bn254

-- Intermediate structures and helpers

/-- Precomputed JSON structural data for the decoded JWT payload. -/
structure JSONStructure where
  payload          : FString bn254 MAX_JWT_PAYLOAD_LEN
  payloadHash      : F bn254
  stringBodies     : PaddedVector FB bn254 MAX_JWT_PAYLOAD_LEN
  bracketsDepthMap : List (F bn254)

/-- Multiplexer for FString: `if sel = 1 then a else b`. CIRCOM: `out[i] = (a[i] - b[i]) * sel + b[i]` -/
def muxFString {maxLen : ℕ} (sel : F bn254) (a b : FString bn254 maxLen) : FString bn254 maxLen :=
  { data := a.data.zipWith (F.conditionalSwap sel) b.data
    len := F.conditionalSwap sel a.len b.len }

-- Sub-circuits

open FString FArray HashToField

/-- Assert that the first characters of a field name match `expected` ASCII values.
    When `guard = 1` (default), checks are unconditional. When `guard = 0`, all
    assertions are bypassed (used for conditionally-checked fields like `aud`). -/
def assertFieldName {n : ℕ} (name : FString bn254 n) (expected : String) (guard : FB bn254 := 1) : Option Unit := do
  let isEq ← name.isPaddedOf expected
  FB.conditionallyAssert guard isEq

/-- Verify JWT structural integrity.
    Concatenation, SHA2 padding, SHA2 hash, RSA signature, and base64 decode.
    Returns the decoded JWT payload as an FString. -/
def verifyJWTStructure (jwtRaw : JWTRawInput) (rsa : RSAInput) : Option (FString bn254 MAX_JWT_PAYLOAD_LEN) := do
  -- Step 1: Assert header_w_dot ++ payload_sha2_padded = jwt_no_sig_sha2_padded
  FString.assertIsConcatenation (by decide) (by decide)
    jwtRaw.b64u_jwt_no_sig_sha2_padded jwtRaw.b64u_jwt_header_w_dot jwtRaw.b64u_jwt_payload_sha2_padded
  -- Assert the last character of header_w_dot is '.' (ASCII 46)
  -- This prevents the circuit from being tricked about where the payload starts.
  let dot ← selectArrayValue jwtRaw.b64u_jwt_no_sig_sha2_padded.data (jwtRaw.b64u_jwt_header_w_dot.len - 1)
  F.assert_eq dot (F8.ofChar '.')
  -- Steps 2–3: SHA2-256 padding verification + hash computation
  -- Unified into a single call that verifies RFC 4634 padding and computes
  -- the SHA2-256 hash, returning 4 × 64-bit limbs for RSA.
  -- CIRCOM: SHA2_256_PaddingVerify(...) + SHA2_256_Prepadded_Hash(...)
  -- paddingStart = where real data ends = header_w_dot_len + payload_sha2_padded_len
  -- CIRCOM: b64u_jwt_header_w_dot_len + b64u_jwt_payload_sha2_padded_len
  let paddingStart := jwtRaw.b64u_jwt_header_w_dot.len + jwtRaw.b64u_jwt_payload_sha2_padded.len
  let sha2Hash ← Clap.Sha2.Keyless.sha256VerifiedDigest
    jwtRaw.b64u_jwt_no_sig_sha2_padded
    paddingStart
    jwtRaw.sha2_num_blocks
    jwtRaw.sha2_num_bits
    jwtRaw.sha2_padding
  -- Step 4: RSA signature verification (STUB)
  RSA_2048_e_65537_PKCS1_V1_5_Verify sha2Hash rsa.signature rsa.pubkeyModulus
  -- Step 4b: Assert b64u_jwt_payload is a valid prefix of b64u_jwt_payload_sha2_padded
  -- This removes SHA2 padding and ensures consistency.
  -- CIRCOM: AssertIsSubstring(b64u_jwt_payload_sha2_padded, ..., b64u_jwt_payload, ..., 0)
  let paddedHash ← hashBytesToField jwtRaw.b64u_jwt_payload_sha2_padded
  assertIsSubstringFS (by decide) jwtRaw.b64u_jwt_payload_sha2_padded paddedHash jwtRaw.b64u_jwt_payload 0
  -- Step 5: Base64-decode the payload
  Base64Len.base64UrlDecode (by decide) jwtRaw.b64u_jwt_payload

/-- Compute JSON structural analysis from the decoded JWT payload.
    Returns the payload with its hash, string bodies, and brackets depth map. -/
def computeJSONStructure (payload : FString bn254 MAX_JWT_PAYLOAD_LEN) : Option JSONStructure := do
  -- Compute payload hash
  let payloadHash ← hashBytesToField payload
  -- JSON structural analysis on raw field elements
  let stringBodies ← JWT.stringBodies payload
  let inverted := stringBodies.data.map FB.not
  let brackets_map : List (FB p) ← JWT.bracketsMap payload.data.toArray.toList
  let unquoted_brackets := inverted.toArray.toList.zipWith (· * ·) brackets_map
  let bracketsDepthMap ← JWT.bracketsDepthMap unquoted_brackets
  return { payload, payloadHash, stringBodies, bracketsDepthMap }

/-- Verify a quoted JWT field: substring check, not-nested check, field parsing. -/
def verifyQuotedField {maxPairLen maxNameLen maxValueLen : ℕ}
    (h_name : maxNameLen ≤ maxPairLen) (h_value : maxValueLen ≤ maxPairLen) (h_pair : maxPairLen ≤ MAX_JWT_PAYLOAD_LEN)
    (json : JSONStructure) (inp : JWT.QuotedFieldInput maxPairLen maxNameLen maxValueLen)
    : Option Unit := do
  -- Assert field is a substring of the decoded JWT payload
  FString.assertIsSubstringFS h_pair json.payload json.payloadHash inp.field inp.nameIndex
  -- Assert fieldStringBodies is a substring of stringBodies at the same index
  -- CIRCOM: AssertIsSubstring(stringBodies, jwt_payload_hash, x_field_string_bodies, x_field_len, x_index)
  FString.assertIsSubstringFS h_pair json.stringBodies json.payloadHash inp.fieldStringBodies inp.nameIndex
  -- Assert field is not inside nested brackets
  JWT.enforceNotNested MAX_JWT_PAYLOAD_LEN inp.nameIndex inp.field.len json.bracketsDepthMap
  -- Parse the field structure with quoted value
  JWT.parseJWTFieldWithQuotedValue inp h_name h_value

/-- Verify an unquoted JWT field: substring check, not-nested check, field parsing.
    Unlike `verifyQuotedField`, this does NOT perform a full string_bodies substring
    check. Instead, CIRCOM does a point check that the field does not start inside a
    string body (`SelectArrayValue(string_bodies, index) === 0`). -/
def verifyUnquotedField {maxPairLen maxNameLen maxValueLen : ℕ}
    (h_name : maxNameLen ≤ maxPairLen) (h_value : maxValueLen ≤ maxPairLen) (h_pair : maxPairLen ≤ MAX_JWT_PAYLOAD_LEN)
    (json : JSONStructure) (inp : JWT.UnquotedFieldInput maxPairLen maxNameLen maxValueLen)
    : Option Unit := do
  FString.assertIsSubstringFS h_pair json.payload json.payloadHash inp.field inp.nameIndex
  JWT.enforceNotNested MAX_JWT_PAYLOAD_LEN inp.nameIndex inp.field.len json.bracketsDepthMap
  -- Assert field does not start inside a string body — CIRCOM: start_char === 0
  eq0 (← selectArrayValue json.stringBodies.data inp.nameIndex)
  JWT.parseJWTFieldWithUnquotedValue inp h_name h_value

/-- Verify the audience (aud) field with override and skip support.
    CIRCOM: the `ParseJWTFieldWithQuotedValue` takes a `skip_checks` flag;
    in Lean we handle this by conditionally running the verification. -/
def verifyAudField (json : JSONStructure)
    (aud : JWT.QuotedFieldInput MAX_AUD_KV_PAIR_LEN MAX_AUD_NAME_LEN MAX_AUD_VALUE_LEN)
    (audOverride : AudOverrideInput)
    : Option Unit := do
  -- Validate boolean flags
  FB.assertBool audOverride.useAudOverride
  FB.assertBool audOverride.skipAudChecks
  -- Cannot skip aud checks while using override
  eq0 (audOverride.skipAudChecks * audOverride.useAudOverride)
  let performAudChecks : FB bn254 := FB.not audOverride.skipAudChecks
  -- Mux the effective aud value: if useAudOverride then override else private
  let audValue := muxFString audOverride.useAudOverride audOverride.overrideAudValue audOverride.privateAudValue
  -- Construct the effective field input with muxed value
  let audEff : JWT.QuotedFieldInput _ _ _ := { aud with value := audValue }
  -- Assert field is a substring of the decoded JWT payload (conditioned on performAudChecks)
  let field_passes ← FString.isSubstringFS (by decide) json.payload json.payloadHash audEff.field audEff.nameIndex
  FB.conditionallyAssert performAudChecks field_passes
  -- Assert fieldStringBodies matches stringBodies (conditioned on performAudChecks)
  -- CIRCOM: AssertIsSubstring(stringBodies, jwt_payload_hash, aud_field_string_bodies, aud_field_len, aud_index)
  let sb_passes ← FString.isSubstringFS (by decide) json.stringBodies json.payloadHash audEff.fieldStringBodies audEff.nameIndex
  FB.conditionallyAssert performAudChecks sb_passes
  -- Assert field is not inside nested brackets
  JWT.enforceNotNested MAX_JWT_PAYLOAD_LEN audEff.nameIndex audEff.field.len json.bracketsDepthMap
  -- Parse the field structure, gated by skipAudChecks.
  -- CIRCOM: `succeed = checks_pass OR skip_checks; succeed === 1`
  -- We model this by passing skipChecks to the parser, which gates each constraint
  -- with `perform * constraint === 0` where `perform = NOT(skipChecks)`.
  JWT.parseJWTFieldWithQuotedValue audEff (by decide) (by decide) audOverride.skipAudChecks
  -- Verify aud name is literally "aud" (conditioned on performAudChecks)
  -- CIRCOM: aud_name[i] * performAudChecks === EXPECTED[i] * performAudChecks
  assertFieldName aud.name "aud" performAudChecks

/-- Verify the email_verified field and cross-check with uid name.
    CIRCOM truth table: fail only if uidIsEmail AND NOT evInJwt. -/
def verifyEvField (json : JSONStructure)
    (ev : EvFieldInput MAX_EV_KV_PAIR_LEN MAX_EV_NAME_LEN MAX_EV_VALUE_LEN)
    (uidName : FString bn254 MAX_UID_NAME_LEN)
    : Option Unit := do
  -- Cross-check: get uidIsEmail from emailVerifiedCheck
  let uidIsEmail ←
    JWT.emailVerifiedCheck
      uidName
      ev.name
      ev.value
  -- Check if ev field is in JWT (non-asserting)
  let evInJwt ← FString.isSubstringFS (by decide) json.payload json.payloadHash ev.field ev.nameIndex
  FB.conditionallyAssert uidIsEmail evInJwt
  -- Assert not inside nested brackets
  JWT.enforceNotNested MAX_JWT_PAYLOAD_LEN ev.nameIndex ev.field.len json.bracketsDepthMap
  -- Parse the email_verified field (allows both quoted and unquoted true/false)
  JWT.parseEmailVerifiedField (by decide) (by decide) ev.field ev.name ev.value ev.colonIndex ev.valueIndex

/-- Verify the extra field (optional). -/
def verifyExtraField (json : JSONStructure) (extra : ExtraFieldInput) : Option Unit := do
  -- useExtraField must be boolean
  FB.assertBool extra.useExtraField
  -- Check substring
  let efPasses ← FString.isSubstringFS (by decide) json.payload json.payloadHash extra.extraField extra.extraFieldIndex
  -- Assert not inside nested brackets
  JWT.enforceNotNested MAX_JWT_PAYLOAD_LEN extra.extraFieldIndex extra.extraField.len json.bracketsDepthMap
  FB.conditionallyAssert extra.useExtraField efPasses
  -- Assert extra field does not start inside a string body
  -- CIRCOM: ef_start_char === 0
  eq0 (← selectArrayValue json.stringBodies.data extra.extraFieldIndex)

/-- Verify the nonce field matches the cryptographic commitment.
    `nonceValue` (from JWT) must equal `Poseidon(epk[0..2], epkLen, expDate, epkBlinder)`. -/
def verifyNonce (nonceValue : FString bn254 MAX_NONCE_VALUE_LEN) (commit : CommitmentInput) : Option Unit := do
  -- Compute expected nonce: Poseidon(epk[0], epk[1], epk[2], epkLen, expDate, epkBlinder)
  let expectedNonce ← Clap.Poseidon.poseidonBN254 #v[ commit.epk[0], commit.epk[1], commit.epk[2], commit.epkLen, commit.expDate, commit.epkBlinder ]
  -- Convert nonce value (ASCII digits) to scalar
  let nonceScalar ← FString.asciiDigitsToScalar nonceValue
  -- Assert equality
  F.assert_eq nonceScalar expectedNonce

/-- CIRCOM uses `LessThan(252)` for the comparison. We use 64-bit (`F.lessThan 64`)
    instead because Unix timestamps are seconds since 1970-01-01 and fit comfortably
    in 64 bits (`2^64 ≈ 5.8 × 10^{17}` seconds, i.e., ~18 billion years). Even with
    a generous `expHorizon`, the sum `iat + expHorizon` cannot overflow 64 bits for
    any realistic timestamp. Using 64 bits produces fewer constraints than 252.

    NOTE: CIRCOM checks `expDate < iat + expHorizon`, meaning the expiration
    date must fall before issued-at + horizon. AIP-061 describes this differently
    as `iat < expDate + expHorizon`. We follow CIRCOM as source of truth. -/
def verifyTimestamp (iatValue : FString bn254 MAX_IAT_VALUE_LEN) (expDate expHorizon : F bn254) : Option Unit := do
  let iatScalar ← FString.asciiDigitsToScalar iatValue
  -- 64-bit comparison suffices for timestamps (CIRCOM uses 252 bits)
  FB.assert (← F.lessThan 64 expDate (iatScalar + expHorizon))

/-- Compute the identity commitment.
    `idc = Poseidon(pepper, privateAudValHashed, uidValueHashed, uidNameHashed)`
    When `skipAudChecks = 1`, `privateAudValue` is zeroed before hashing. -/
def computeIdentityCommitment (pepper : F bn254) (privateAudValue : FString bn254 MAX_AUD_VALUE_LEN)
    (performAudChecks : FB bn254) (uidValue : FString bn254 MAX_UID_VALUE_LEN) (uidName : FString bn254 MAX_UID_NAME_LEN)
    : Option (F bn254) := do
  -- Conditionally zero privateAudValue: hashable[i] = privateAudValue[i] * performAudChecks
  let hashableAud : Vector (F bn254) MAX_AUD_VALUE_LEN := privateAudValue.data.map (· * performAudChecks)
  let privateAudValHashed ← hashBytesToField {data := hashableAud,  len := privateAudValue.len * performAudChecks}
  let uidValueHashed ← hashBytesToField uidValue
  let uidNameHashed ← hashBytesToField uidName
  Clap.Poseidon.poseidonBN254 #v[pepper, privateAudValHashed, uidValueHashed, uidNameHashed]

/-- Phase 7: Compute and verify the public inputs hash.
    Collects all verifier-facing data and checks it matches `declaredHash`. -/
def verifyPublicInputsHash
    (idc : F bn254)
    (commit : CommitmentInput)
    (rsa : RSAInput)
    (issValue : FString bn254 MAX_ISS_VALUE_LEN)
    (extra : ExtraFieldInput)
    (audOverride : AudOverrideInput)
    (jwtHeader : FString bn254 MAX_B64U_JWT_HEADER_W_DOT_LEN)
    (declaredHash : F bn254)
    : Option Unit := do
  -- Hash components
  let hashedIssValue ← hashBytesToField issValue
  let hashedExtraField ← hashBytesToField extra.extraField
  let hashedJwtHeader ← hashBytesToField jwtHeader
  -- CIRCOM: Hash64BitLimbsToFieldWithLen(32)(pubkey_modulus_tagged, 256)
  -- 256 = RSA_KEY_BYTES = 32 limbs * 8 bytes/limb
  let hashedPubkeyModulus ← hash64BitLimbsToField {data := rsa.pubkeyModulus, len := RSA_KEY_BYTES}
  let overrideAudValHashed ← hashBytesToField audOverride.overrideAudValue
  -- Poseidon(14 inputs) in the exact order from CIRCOM
  let computed ← Clap.Poseidon.poseidonBN254
    #v[ commit.epk[0], commit.epk[1], commit.epk[2], commit.epkLen
    , idc
    , commit.expDate
    , commit.expHorizon
    , hashedIssValue
    , extra.useExtraField
    , hashedExtraField
    , hashedJwtHeader
    , hashedPubkeyModulus
    , overrideAudValHashed
    , audOverride.useAudOverride
    ]
  F.assert_eq computed declaredHash

-- Top-level circuit

/-- The Aptos Keyless circuit. -/
def keyless (input : KeylessInput) : Option Unit := do
  -- Phase 1: JWT structural verification (concatenation, base64, SHA2, RSA)
  let jwtPayload ← verifyJWTStructure input.jwtRaw input.rsa

  -- Phase 2: Compute JSON structure for field parsing
  let json ← computeJSONStructure jwtPayload

  -- Phase 3: Verify JWT fields
  verifyAudField json input.aud input.audOverride
  verifyQuotedField (by decide) (by decide) (by decide) json input.uid
  verifyQuotedField (by decide) (by decide) (by decide) json input.iss
  assertFieldName input.iss.name "iss"
  verifyUnquotedField (by decide) (by decide) (by decide) json input.iat
  assertFieldName input.iat.name "iat"
  verifyQuotedField (by decide) (by decide) (by decide) json input.nonce
  assertFieldName input.nonce.name "nonce"

  verifyEvField json input.ev input.uid.name
  verifyExtraField json input.extra

  -- Nonce verification
  verifyNonce input.nonce.value input.commit

  -- Timestamp check
  verifyTimestamp input.iat.value input.commit.expDate input.commit.expHorizon

  -- Identity commitment
  let performAudChecks : FB bn254 := FB.not input.audOverride.skipAudChecks
  let idc ← computeIdentityCommitment
    input.commit.pepper
    input.audOverride.privateAudValue
    performAudChecks
    input.uid.value
    input.uid.name

  -- Public inputs hash verification
  verifyPublicInputsHash idc input.commit input.rsa input.iss.value
    input.extra input.audOverride input.jwtRaw.b64u_jwt_header_w_dot
    input.publicInputsHash

end Keyless

namespace Spec.Keyless

open Keyless Clap Lang Primes Spec

abbrev p := bn254
abbrev F p := ZMod p
abbrev FB p := F p

def muxFString_spec (sel : Bool) (a b : String) : String := if sel then a else b

lemma muxFString_equiv {maxLen : ℕ} (sel : FB p) (a b : FString bn254 maxLen)
  (hsel : FB.valid sel)
  (ha : FString.valid a)
  (ha : FString.valid b) :
  Keyless.muxFString sel a b =
    FString.ofString
      (muxFString_spec
        (FB.toBool sel)
        (FString.toString a)
        (FString.toString b)
      )
:= by
  have h_cond_swap : F.conditionalSwap sel a.len b.len = if FB.toBool sel then a.len else b.len :=
    F.conditionalSwap_equiv sel a.len b.len hsel
  have h_cond_swap_data : a.data.zipWith (F.conditionalSwap sel) b.data = if FB.toBool sel then a.data else b.data := by
    ext i; simp [F.conditionalSwap_equiv, hsel];
    split_ifs <;> rfl;
  have h_ofString_toString : FString.ofString (FString.toString a) = a ∧ FString.ofString (FString.toString b) = b := by
    exact ⟨ Spec.FString.ofString_toString a ‹_›, Spec.FString.ofString_toString b ‹_› ⟩;
  unfold Keyless.muxFString muxFString_spec; aesop;

def assertFieldName_spec
  (name expected : String)
  (guard : Bool := true) :
  Option Unit
:=
  Spec.FB.conditionallyAssert guard (name == expected)

lemma assertFieldName_equiv {n : ℕ}
  (name : FString bn254 n)
  (hname : FString.valid name)
  (expected : String)
  (hchars : ∀ c ∈ expected.toList, c.toNat < 256)
  (hlen : expected.length < bn254)
  (guard : FB bn254)
  (hguard : FB.valid guard):
  Keyless.assertFieldName name expected guard =
    assertFieldName_spec (FString.toString name) expected (FB.toBool guard)
:= by
  convert Spec.FB.conditionallyAssert_equiv guard _ hguard _ using 1;
  rotate_left;
  rotate_left;
  exact FB.ofBool ( FString.toString name == expected );
  · exact Spec.FB.valid_ofBool _;
  · unfold Keyless.assertFieldName;
    rw [ Spec.FString.isPaddedOf_equiv name expected hname hchars ( by native_decide ) hlen ];
    grind;
  · simp +decide [ Spec.FB.left_inv, Spec.FB.conditionallyAssert ];
    unfold assertFieldName_spec; aesop;

end Spec.Keyless
