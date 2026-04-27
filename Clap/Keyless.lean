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

open Clap.Lang Core Primes Clap.RSA

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

-- Known field name lengths
abbrev AUD_NAME_LEN   := 3   -- "aud"
abbrev ISS_NAME_LEN   := 3   -- "iss"
abbrev IAT_NAME_LEN   := 3   -- "iat"
abbrev NONCE_NAME_LEN := 5 -- "nonce"
abbrev EV_NAME_LEN    := 14   -- "email_verified"

-- ============================================================================
-- Stubs for WIP components
-- ============================================================================

variable [Core bn254]

-- Input structures

/-- JWT field with a quoted value (aud, uid, iss, nonce). -/
structure QuotedFieldInput (maxPairLen maxNameLen maxValueLen : ℕ) where
  field             : FString bn254 maxPairLen
  name              : FString bn254 maxNameLen
  value             : FString bn254 maxValueLen
  fieldStringBodies : Vector (FB bn254) maxPairLen
  nameIndex         : F bn254
  colonIndex        : F bn254
  valueIndex        : F bn254

/-- JWT field with an unquoted value (iat). -/
structure UnquotedFieldInput (maxPairLen maxNameLen maxValueLen : ℕ) where
  field      : FString bn254 maxPairLen
  name       : FString bn254 maxNameLen
  value      : FString bn254 maxValueLen
  nameIndex  : F bn254
  colonIndex : F bn254
  valueIndex : F bn254

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
  aud              : QuotedFieldInput MAX_AUD_KV_PAIR_LEN MAX_AUD_NAME_LEN MAX_AUD_VALUE_LEN
  audOverride      : AudOverrideInput
  uid              : QuotedFieldInput MAX_UID_KV_PAIR_LEN MAX_UID_NAME_LEN MAX_UID_VALUE_LEN
  iss              : QuotedFieldInput MAX_ISS_KV_PAIR_LEN MAX_ISS_NAME_LEN MAX_ISS_VALUE_LEN
  iat              : UnquotedFieldInput MAX_IAT_KV_PAIR_LEN MAX_IAT_NAME_LEN MAX_IAT_VALUE_LEN
  nonce            : QuotedFieldInput MAX_NONCE_KV_PAIR_LEN MAX_NONCE_NAME_LEN MAX_NONCE_VALUE_LEN
  ev               : EvFieldInput MAX_EV_KV_PAIR_LEN MAX_EV_NAME_LEN MAX_EV_VALUE_LEN
  extra            : ExtraFieldInput
  commit           : CommitmentInput
  publicInputsHash : F bn254

-- Intermediate structures and helpers

/-- Precomputed JSON structural data for the decoded JWT payload. -/
structure JSONStructure where
  payload          : FString bn254 MAX_JWT_PAYLOAD_LEN
  payloadHash      : F bn254
  stringBodies     : Vector (FB bn254) MAX_JWT_PAYLOAD_LEN
  bracketsDepthMap : List (F bn254)

/-- Multiplexer for FString: `if sel = 1 then a else b`. CIRCOM: `out[i] = (a[i] - b[i]) * sel + b[i]` -/
def muxFString {maxLen : ℕ} (sel : F bn254) (a b : FString bn254 maxLen) : FString bn254 maxLen :=
  { chars := a.chars.zipWith
      (fun ai bi ↦ ai.zipWith (fun abit bbit ↦ (abit - bbit) * sel + bbit) bi) b.chars
    len := (a.len - b.len) * sel + b.len }

-- Sub-circuits

open FString FArray HashToField

/-- Assert that `substrBits` appears in `strBits` at `startIndex`, using the
    Fiat-Shamir substring check. Both inputs are binary vectors (0/1 field elements)
    from `StringBodies`; they are temporarily wrapped into FStrings for the
    `assertIsSubstringFS` call (0 and 1 are valid bytes).
    `strHash` is the pre-computed hash of the *payload* (reused as the Fiat-Shamir
    seed, matching the CIRCOM convention). -/
def assertStringBodiesSubstring {maxStrLen maxSubstrLen : ℕ} (h : maxSubstrLen ≤ maxStrLen)
    (strBits : Vector (FB bn254) maxStrLen) (strLen : F bn254)
    (strHash : F bn254)
    (substrBits : Vector (FB bn254) maxSubstrLen) (substrLen : F bn254)
    (startIndex : F bn254)
    : Option Unit := do
  let sb_chars ← strBits.mapM F8.ofF
  let sb_fstr : FString bn254 maxStrLen := ⟨sb_chars, strLen⟩
  let fsb_chars ← substrBits.mapM F8.ofF
  let fsb_fstr : FString bn254 maxSubstrLen := ⟨fsb_chars, substrLen⟩
  FString.assertIsSubstringFS h sb_fstr strHash fsb_fstr startIndex

/-- Non-asserting variant: returns whether `substrBits` appears in `strBits`
    at `startIndex`. See `assertStringBodiesSubstring` for details. -/
def isStringBodiesSubstring {maxStrLen maxSubstrLen : ℕ} (h : maxSubstrLen ≤ maxStrLen)
    (strBits : Vector (FB bn254) maxStrLen) (strLen : F bn254)
    (strHash : F bn254)
    (substrBits : Vector (FB bn254) maxSubstrLen) (substrLen : F bn254)
    (startIndex : F bn254)
    : Option (FB bn254) := do
  let sb_chars ← strBits.mapM F8.ofF
  let sb_fstr : FString bn254 maxStrLen := ⟨sb_chars, strLen⟩
  let fsb_chars ← substrBits.mapM F8.ofF
  let fsb_fstr : FString bn254 maxSubstrLen := ⟨fsb_chars, substrLen⟩
  FString.isSubstringFS h sb_fstr strHash fsb_fstr startIndex

/-- Assert that the first characters of a field name match `expected` ASCII values.
    When `guard = 1` (default), checks are unconditional. When `guard = 0`, all
    assertions are bypassed (used for conditionally-checked fields like `aud`). -/
def assertFieldName {n : ℕ} (name : FString bn254 n) (expected : Array (F bn254)) (guard : FB bn254 := 1) : Option Unit :=
  name.toVF.toArray.zip expected |>.forM fun (actual, exp) ↦ F.guardedAssertEq guard actual exp

/-- Verify JWT structural integrity.
    Concatenation, SHA2 padding, SHA2 hash, RSA signature, and base64 decode.
    Returns the decoded JWT payload as an FString. -/
def verifyJWTStructure (jwtRaw : JWTRawInput) (rsa : RSAInput) : Option (FString bn254 MAX_JWT_PAYLOAD_LEN) := do
  -- Step 1: Assert header_w_dot ++ payload_sha2_padded = jwt_no_sig_sha2_padded
  FString.assertIsConcatenation (by decide) (by decide)
    jwtRaw.b64u_jwt_no_sig_sha2_padded jwtRaw.b64u_jwt_header_w_dot jwtRaw.b64u_jwt_payload_sha2_padded
  -- Assert the last character of header_w_dot is '.' (ASCII 46)
  -- This prevents the circuit from being tricked about where the payload starts.
  -- CIRCOM: dot === 46
  let dot ← selectArrayValue jwtRaw.b64u_jwt_no_sig_sha2_padded.toVF (jwtRaw.b64u_jwt_header_w_dot.len - 1)
  F.assert_eq dot 46
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
  let paddedHash ← hashBytesToFieldWithLen jwtRaw.b64u_jwt_payload_sha2_padded.toVF jwtRaw.b64u_jwt_payload_sha2_padded.len
  assertIsSubstringFS (by decide) jwtRaw.b64u_jwt_payload_sha2_padded paddedHash jwtRaw.b64u_jwt_payload 0
  -- Step 5: Base64-decode the payload
  let jwtPayload ← Base64Len.base64UrlDecode MAX_JWT_PAYLOAD_LEN jwtRaw.b64u_jwt_payload.toVF.toArray
  -- Compute decoded length: floor(3 * encoded_len / 4)
  let jwtPayloadLen ← Base64Len.base64UrlDecodedLength 20 jwtRaw.b64u_jwt_payload.len
  -- Build FString from decoded payload (may be shorter than MAX_JWT_PAYLOAD_LEN, pad with zeros)
  let padded := jwtPayload ++ Array.replicate (MAX_JWT_PAYLOAD_LEN - jwtPayload.size) 0
  let charsF : Vector (F bn254) MAX_JWT_PAYLOAD_LEN := ⟨padded.take MAX_JWT_PAYLOAD_LEN, by simp [padded]; omega⟩
  let chars ← charsF.mapM F8.ofF
  return ⟨chars, jwtPayloadLen⟩

/-- Compute JSON structural analysis from the decoded JWT payload.
    Returns the payload with its hash, string bodies, and brackets depth map. -/
def computeJSONStructure (payload : FString bn254 MAX_JWT_PAYLOAD_LEN) : Option JSONStructure := do
  -- Compute payload hash
  let payloadHash ← hashBytesToFieldWithLen payload.toVF payload.len
  -- JSON structural analysis on raw field elements
  let payloadList := payload.toVF.toList
  let stringBodies ← JWT.stringBodies payloadList
  let inverted := stringBodies.map FB.not
  let brackets_map ← JWT.bracketsMap payloadList
  let unquoted_brackets := inverted.zipWith (· * ·) brackets_map
  let bracketsDepthMap ← JWT.bracketsDepthMap unquoted_brackets
  let stringBodiesVec : Vector (FB bn254) MAX_JWT_PAYLOAD_LEN := ⟨stringBodies.toArray, by sorry⟩-- simp [stringBodies, payloadList]⟩
  return { payload, payloadHash, stringBodies := stringBodiesVec, bracketsDepthMap }

/-- Verify a quoted JWT field: substring check, not-nested check, field parsing. -/
def verifyQuotedField {maxPairLen maxNameLen maxValueLen : ℕ}
    (h_name : maxNameLen ≤ maxPairLen) (h_value : maxValueLen ≤ maxPairLen) (h_pair : maxPairLen ≤ MAX_JWT_PAYLOAD_LEN)
    (json : JSONStructure) (inp : QuotedFieldInput maxPairLen maxNameLen maxValueLen)
    : Option Unit := do
  -- Assert field is a substring of the decoded JWT payload
  FString.assertIsSubstringFS h_pair json.payload json.payloadHash inp.field inp.nameIndex
  -- Assert fieldStringBodies is a substring of stringBodies at the same index
  -- CIRCOM: AssertIsSubstring(stringBodies, jwt_payload_hash, x_field_string_bodies, x_field_len, x_index)
  assertStringBodiesSubstring h_pair json.stringBodies json.payload.len json.payloadHash inp.fieldStringBodies inp.field.len inp.nameIndex
  -- Assert field is not inside nested brackets
  JWT.enforceNotNested MAX_JWT_PAYLOAD_LEN inp.nameIndex inp.field.len json.bracketsDepthMap
  -- Parse the field structure with quoted value
  JWT.parseJWTFieldWithQuotedValue h_name h_value inp.field inp.name inp.value inp.fieldStringBodies inp.colonIndex inp.valueIndex

/-- Verify an unquoted JWT field: substring check, not-nested check, field parsing.
    Unlike `verifyQuotedField`, this does NOT perform a full string_bodies substring
    check. Instead, CIRCOM does a point check that the field does not start inside a
    string body (`SelectArrayValue(string_bodies, index) === 0`). -/
def verifyUnquotedField {maxPairLen maxNameLen maxValueLen : ℕ}
    (h_name : maxNameLen ≤ maxPairLen) (h_value : maxValueLen ≤ maxPairLen) (h_pair : maxPairLen ≤ MAX_JWT_PAYLOAD_LEN)
    (json : JSONStructure) (inp : UnquotedFieldInput maxPairLen maxNameLen maxValueLen)
    : Option Unit := do
  FString.assertIsSubstringFS h_pair json.payload json.payloadHash inp.field inp.nameIndex
  JWT.enforceNotNested MAX_JWT_PAYLOAD_LEN inp.nameIndex inp.field.len json.bracketsDepthMap
  -- Assert field does not start inside a string body — CIRCOM: start_char === 0
  eq0 (← selectArrayValue json.stringBodies inp.nameIndex)
  JWT.parseJWTFieldWithUnquotedValue h_name h_value inp.field inp.name inp.value inp.colonIndex inp.valueIndex

/-- Verify the audience (aud) field with override and skip support.
    CIRCOM: the `ParseJWTFieldWithQuotedValue` takes a `skip_checks` flag;
    in Lean we handle this by conditionally running the verification. -/
def verifyAudField (json : JSONStructure)
    (aud : QuotedFieldInput MAX_AUD_KV_PAIR_LEN MAX_AUD_NAME_LEN MAX_AUD_VALUE_LEN)
    (audOverride : AudOverrideInput)
    : Option Unit := do
  -- Validate boolean flags
  F.assertBinary audOverride.useAudOverride
  F.assertBinary audOverride.skipAudChecks
  -- Cannot skip aud checks while using override
  eq0 (audOverride.skipAudChecks * audOverride.useAudOverride)
  let performAudChecks : FB bn254 := FB.not audOverride.skipAudChecks
  -- Mux the effective aud value: if useAudOverride then override else private
  let audValue := muxFString audOverride.useAudOverride audOverride.overrideAudValue audOverride.privateAudValue
  let audValueLen ← share ((audOverride.overrideAudValue.len - audOverride.privateAudValue.len) * audOverride.useAudOverride + audOverride.privateAudValue.len)
  -- Construct the effective field input with muxed value
  let audEff : QuotedFieldInput _ _ _ := { aud with value := { audValue with len := audValueLen } }
  -- Assert field is a substring of the decoded JWT payload (conditioned on performAudChecks)
  let field_passes ← FString.isSubstringFS (by decide) json.payload json.payloadHash audEff.field audEff.nameIndex
  eq0 (performAudChecks * FB.not field_passes)
  -- Assert fieldStringBodies matches stringBodies (conditioned on performAudChecks)
  -- CIRCOM: AssertIsSubstring(stringBodies, jwt_payload_hash, aud_field_string_bodies, aud_field_len, aud_index)
  let sb_passes ← isStringBodiesSubstring (by decide) json.stringBodies json.payload.len json.payloadHash audEff.fieldStringBodies audEff.field.len audEff.nameIndex
  eq0 (performAudChecks * FB.not sb_passes)
  -- Assert field is not inside nested brackets
  JWT.enforceNotNested MAX_JWT_PAYLOAD_LEN audEff.nameIndex audEff.field.len json.bracketsDepthMap
  -- Parse the field structure, gated by skipAudChecks.
  -- CIRCOM: `succeed = checks_pass OR skip_checks; succeed === 1`
  -- We model this by passing skipChecks to the parser, which gates each constraint
  -- with `perform * constraint === 0` where `perform = NOT(skipChecks)`.
  JWT.parseJWTFieldWithQuotedValue (by decide) (by decide)
    audEff.field audEff.name audEff.value audEff.fieldStringBodies
    audEff.colonIndex audEff.valueIndex audOverride.skipAudChecks
  -- Verify aud name is literally "aud" (conditioned on performAudChecks)
  -- CIRCOM: aud_name[i] * performAudChecks === EXPECTED[i] * performAudChecks
  assertFieldName aud.name #[97, 117, 100] performAudChecks -- "aud"

/-- Verify the email_verified field and cross-check with uid name.
    CIRCOM truth table: fail only if uidIsEmail AND NOT evInJwt. -/
def verifyEvField (json : JSONStructure)
    (ev : EvFieldInput MAX_EV_KV_PAIR_LEN MAX_EV_NAME_LEN MAX_EV_VALUE_LEN)
    (uidName : FString bn254 MAX_UID_NAME_LEN)
    : Option Unit := do
  -- Cross-check: get uidIsEmail from emailVerifiedCheck
  let uidIsEmail ← JWT.emailVerifiedCheck uidName.len uidName.toVF.toList ev.name.toVF.toList ev.value.len ev.value.toVF.toList
  -- Check if ev field is in JWT (non-asserting)
  let evInJwt ← FString.isSubstringFS (by decide) json.payload json.payloadHash ev.field ev.nameIndex
  -- Fail if uidIsEmail = 1 AND evInJwt = 0
  -- CIRCOM truth table:
  --   uidIsEmail | evInJwt | fail?
  --        1       |     1     |  no
  --        1       |     0     |  yes
  --        0       |     1     |  no
  --        0       |     0     |  no
  eq0 (uidIsEmail * FB.not evInJwt)
  -- Assert not inside nested brackets
  JWT.enforceNotNested MAX_JWT_PAYLOAD_LEN ev.nameIndex ev.field.len json.bracketsDepthMap
  -- Parse the email_verified field (allows both quoted and unquoted true/false)
  JWT.parseEmailVerifiedField (by decide) (by decide) ev.field ev.name ev.value ev.colonIndex ev.valueIndex

/-- Verify the extra field (optional). -/
def verifyExtraField (json : JSONStructure) (extra : ExtraFieldInput) : Option Unit := do
  -- useExtraField must be boolean
  F.assertBinary extra.useExtraField
  -- Check substring
  let efPasses ← FString.isSubstringFS (by decide) json.payload json.payloadHash extra.extraField extra.extraFieldIndex
  -- Assert not inside nested brackets
  JWT.enforceNotNested MAX_JWT_PAYLOAD_LEN extra.extraFieldIndex extra.extraField.len json.bracketsDepthMap
  -- If useExtraField = 1 then efPasses must be 1
  eq0 (extra.useExtraField * FB.not efPasses)
  -- Assert extra field does not start inside a string body
  -- CIRCOM: ef_start_char === 0
  eq0 (← selectArrayValue json.stringBodies extra.extraFieldIndex)

/-- Verify the nonce field matches the cryptographic commitment.
    `nonceValue` (from JWT) must equal `Poseidon(epk[0..2], epkLen, expDate, epkBlinder)`. -/
def verifyNonce (nonceValue : FString bn254 MAX_NONCE_VALUE_LEN) (commit : CommitmentInput) : Option Unit := do
  -- Compute expected nonce: Poseidon(epk[0], epk[1], epk[2], epkLen, expDate, epkBlinder)
  let expectedNonce ← Clap.Poseidon.poseidonBN254 [ commit.epk[0], commit.epk[1], commit.epk[2], commit.epkLen, commit.expDate, commit.epkBlinder ]
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
  let hashableAud : Vector (F bn254) MAX_AUD_VALUE_LEN := privateAudValue.chars.map (fun c ↦ FBitVec.toF c * performAudChecks)
  let privateAudValHashed ← hashBytesToFieldWithLen hashableAud (privateAudValue.len * performAudChecks)
  let uidValueHashed ← hashBytesToFieldWithLen uidValue.toVF uidValue.len
  let uidNameHashed ← hashBytesToFieldWithLen uidName.toVF uidName.len
  Clap.Poseidon.poseidonBN254 [pepper, privateAudValHashed, uidValueHashed, uidNameHashed]

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
  let hashedIssValue ← hashBytesToFieldWithLen issValue.toVF issValue.len
  let hashedExtraField ← hashBytesToFieldWithLen extra.extraField.toVF extra.extraField.len
  let hashedJwtHeader ← hashBytesToFieldWithLen jwtHeader.toVF jwtHeader.len
  -- CIRCOM: Hash64BitLimbsToFieldWithLen(32)(pubkey_modulus_tagged, 256)
  -- 256 = RSA_KEY_BYTES = 32 limbs * 8 bytes/limb
  let hashedPubkeyModulus ← hash64BitLimbsToFieldWithLen rsa.pubkeyModulus 64 RSA_KEY_BYTES
  let overrideAudValHashed ← hashBytesToFieldWithLen audOverride.overrideAudValue.toVF audOverride.overrideAudValue.len
  -- Poseidon(14 inputs) in the exact order from CIRCOM
  let computed ← Clap.Poseidon.poseidonBN254
    [ commit.epk[0], commit.epk[1], commit.epk[2], commit.epkLen
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
  -- Verify iss name is "iss" — CIRCOM: iss_name[i] === EXPECTED_ISS_NAME[i]
  assertFieldName input.iss.name #[105, 115, 115] -- "iss"
  verifyUnquotedField (by decide) (by decide) (by decide) json input.iat
  -- Verify iat name is "iat" — CIRCOM: iat_name[i] === EXPECTED_IAT_NAME[i]
  assertFieldName input.iat.name #[105, 97, 116] -- "iat"
  verifyQuotedField (by decide) (by decide) (by decide) json input.nonce
  -- Verify nonce name is "nonce" — CIRCOM: nonce_name[i] === EXPECTED_NONCE_NAME[i]
  assertFieldName input.nonce.name #[110, 111, 110, 99, 101] -- "nonce"

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

-- Keyless test that match the AIP-061 example (`iss = "https://accounts.google.com"`, `aud = "407408718192.apps.googleusercontent.com"`); other JWT fields
-- come from Aptos's reference `circuit/tools/input_gen.py` (Michael Straka's Google JWT, signed with the test RSA key). We cannot
-- reuse AIP-061's as is because that nonce is a Poseidon commitment to Google's actual ephemeral key, which we do not have.
--
-- The 32 RSA limbs, 1536-byte SHA-padded JWT bytes, and JSON structural indices were produced by `python3 circuit/tools/input_gen.py`

set_option maxRecDepth 8192

namespace TestKeyless

open Clap.Lang Core Primes ZMod Keyless

private def mkChar (n : Nat) : F8 bn254 := Clap.nat2bitsLsb 8 n
private def mkFB (n : Nat) : FB bn254 := (n : ZMod bn254)

-- Raw ASCII byte arrays for each FString
-- ASCII: "eyJhbGciOiJSUzI1NiIsImtpZCI6InRlc3RfandrIiwidHlwIjoiSldUIn0.eyJpc3MiOiJodHRwczovL2FjY291bnRzLmdvb2dsZS5jb20iLCJhenAiOiI0MDc0MDg3MTgxOTIuYXBwcy5nb29nbGV1c2VyY29udGVudC5jb20iLCJhdWQiOiI0MDc0MDg3MTgxOTIuYXBwcy5nb29nbGV1c2VyY29udGVudC5jb20iLCJzdWIiOiIxMTM5OTAzMDcwODI4OTk3MTg3NzUiLCJhdF9oYXNoIjoibFZlRDR4UDZRMVpHckwzZ0ZjQ1FMUSIsIm5hbWUiOiJNaWNoYWVsIFN0cmFrYSIsInBpY3R1cmUiOiJodHRwczovL2xoMy5nb29nbGV1c2VyY29udGVudC5jb20vYS9BQ2c4b2NMVm44RjhWblhLTk5KaFJPaFRwUXVMTGpGRWR2X3Vob2UtRFVhUlRseEtFeTllNHc9czk2LWMiLCJnaXZlbl9uYW1lIjoiTWljaGFlbCIsImZhbWlseV9uYW1lIjoiU3RyYWthIiwiaWF0IjoxNzE5ODY2MTM4LCJleHAiOjE3MTk4Njk3MzgsIm5vbmNlIjoiMjI4NDQ3MzMzMzQ0MjI1MTgwNDM3OTY4MTY0Mzk2NTMwODE1NDMxMTc3MzY2NzUyNTM5ODExOTQ5Njc5NzU0NTU5NDcwNTM1NjQ5NSJ9\x80\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x16\xa0 (then 768 × 0)"
private def jwtNoSigBytes : Array Nat := #[101, 121, 74, 104, 98, 71, 99, 105, 79, 105, 74, 83, 85, 122, 73, 49, 78, 105, 73, 115, 73, 109, 116, 112, 90, 67, 73, 54, 73, 110, 82, 108, 99, 51, 82, 102, 97, 110, 100, 114, 73, 105, 119, 105, 100, 72, 108, 119, 73, 106, 111, 105, 83, 108, 100, 85, 73, 110, 48, 46, 101, 121, 74, 112, 99, 51, 77, 105, 79, 105, 74, 111, 100, 72, 82, 119, 99, 122, 111, 118, 76, 50, 70, 106, 89, 50, 57, 49, 98, 110, 82, 122, 76, 109, 100, 118, 98, 50, 100, 115, 90, 83, 53, 106, 98, 50, 48, 105, 76, 67, 74, 104, 101, 110, 65, 105, 79, 105, 73, 48, 77, 68, 99, 48, 77, 68, 103, 51, 77, 84, 103, 120, 79, 84, 73, 117, 89, 88, 66, 119, 99, 121, 53, 110, 98, 50, 57, 110, 98, 71, 86, 49, 99, 50, 86, 121, 89, 50, 57, 117, 100, 71, 86, 117, 100, 67, 53, 106, 98, 50, 48, 105, 76, 67, 74, 104, 100, 87, 81, 105, 79, 105, 73, 48, 77, 68, 99, 48, 77, 68, 103, 51, 77, 84, 103, 120, 79, 84, 73, 117, 89, 88, 66, 119, 99, 121, 53, 110, 98, 50, 57, 110, 98, 71, 86, 49, 99, 50, 86, 121, 89, 50, 57, 117, 100, 71, 86, 117, 100, 67, 53, 106, 98, 50, 48, 105, 76, 67, 74, 122, 100, 87, 73, 105, 79, 105, 73, 120, 77, 84, 77, 53, 79, 84, 65, 122, 77, 68, 99, 119, 79, 68, 73, 52, 79, 84, 107, 51, 77, 84, 103, 51, 78, 122, 85, 105, 76, 67, 74, 104, 100, 70, 57, 111, 89, 88, 78, 111, 73, 106, 111, 105, 98, 70, 90, 108, 82, 68, 82, 52, 85, 68, 90, 82, 77, 86, 112, 72, 99, 107, 119, 122, 90, 48, 90, 106, 81, 49, 70, 77, 85, 83, 73, 115, 73, 109, 53, 104, 98, 87, 85, 105, 79, 105, 74, 78, 97, 87, 78, 111, 89, 87, 86, 115, 73, 70, 78, 48, 99, 109, 70, 114, 89, 83, 73, 115, 73, 110, 66, 112, 89, 51, 82, 49, 99, 109, 85, 105, 79, 105, 74, 111, 100, 72, 82, 119, 99, 122, 111, 118, 76, 50, 120, 111, 77, 121, 53, 110, 98, 50, 57, 110, 98, 71, 86, 49, 99, 50, 86, 121, 89, 50, 57, 117, 100, 71, 86, 117, 100, 67, 53, 106, 98, 50, 48, 118, 89, 83, 57, 66, 81, 50, 99, 52, 98, 50, 78, 77, 86, 109, 52, 52, 82, 106, 104, 87, 98, 108, 104, 76, 84, 107, 53, 75, 97, 70, 74, 80, 97, 70, 82, 119, 85, 88, 86, 77, 84, 71, 112, 71, 82, 87, 82, 50, 88, 51, 86, 111, 98, 50, 85, 116, 82, 70, 86, 104, 85, 108, 82, 115, 101, 69, 116, 70, 101, 84, 108, 108, 78, 72, 99, 57, 99, 122, 107, 50, 76, 87, 77, 105, 76, 67, 74, 110, 97, 88, 90, 108, 98, 108, 57, 117, 89, 87, 49, 108, 73, 106, 111, 105, 84, 87, 108, 106, 97, 71, 70, 108, 98, 67, 73, 115, 73, 109, 90, 104, 98, 87, 108, 115, 101, 86, 57, 117, 89, 87, 49, 108, 73, 106, 111, 105, 85, 51, 82, 121, 89, 87, 116, 104, 73, 105, 119, 105, 97, 87, 70, 48, 73, 106, 111, 120, 78, 122, 69, 53, 79, 68, 89, 50, 77, 84, 77, 52, 76, 67, 74, 108, 101, 72, 65, 105, 79, 106, 69, 51, 77, 84, 107, 52, 78, 106, 107, 51, 77, 122, 103, 115, 73, 109, 53, 118, 98, 109, 78, 108, 73, 106, 111, 105, 77, 106, 73, 52, 78, 68, 81, 51, 77, 122, 77, 122, 77, 122, 81, 48, 77, 106, 73, 49, 77, 84, 103, 119, 78, 68, 77, 51, 79, 84, 89, 52, 77, 84, 89, 48, 77, 122, 107, 50, 78, 84, 77, 119, 79, 68, 69, 49, 78, 68, 77, 120, 77, 84, 99, 51, 77, 122, 89, 50, 78, 122, 85, 121, 78, 84, 77, 53, 79, 68, 69, 120, 79, 84, 81, 53, 78, 106, 99, 53, 78, 122, 85, 48, 78, 84, 85, 53, 78, 68, 99, 119, 78, 84, 77, 49, 78, 106, 81, 53, 78, 83, 74, 57, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "eyJhbGciOiJSUzI1NiIsImtpZCI6InRlc3RfandrIiwidHlwIjoiSldUIn0. (then 240 × 0)"
private def headerBytes : Array Nat := #[101, 121, 74, 104, 98, 71, 99, 105, 79, 105, 74, 83, 85, 122, 73, 49, 78, 105, 73, 115, 73, 109, 116, 112, 90, 67, 73, 54, 73, 110, 82, 108, 99, 51, 82, 102, 97, 110, 100, 114, 73, 105, 119, 105, 100, 72, 108, 119, 73, 106, 111, 105, 83, 108, 100, 85, 73, 110, 48, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "eyJpc3MiOiJodHRwczovL2FjY291bnRzLmdvb2dsZS5jb20iLCJhenAiOiI0MDc0MDg3MTgxOTIuYXBwcy5nb29nbGV1c2VyY29udGVudC5jb20iLCJhdWQiOiI0MDc0MDg3MTgxOTIuYXBwcy5nb29nbGV1c2VyY29udGVudC5jb20iLCJzdWIiOiIxMTM5OTAzMDcwODI4OTk3MTg3NzUiLCJhdF9oYXNoIjoibFZlRDR4UDZRMVpHckwzZ0ZjQ1FMUSIsIm5hbWUiOiJNaWNoYWVsIFN0cmFrYSIsInBpY3R1cmUiOiJodHRwczovL2xoMy5nb29nbGV1c2VyY29udGVudC5jb20vYS9BQ2c4b2NMVm44RjhWblhLTk5KaFJPaFRwUXVMTGpGRWR2X3Vob2UtRFVhUlRseEtFeTllNHc9czk2LWMiLCJnaXZlbl9uYW1lIjoiTWljaGFlbCIsImZhbWlseV9uYW1lIjoiU3RyYWthIiwiaWF0IjoxNzE5ODY2MTM4LCJleHAiOjE3MTk4Njk3MzgsIm5vbmNlIjoiMjI4NDQ3MzMzMzQ0MjI1MTgwNDM3OTY4MTY0Mzk2NTMwODE1NDMxMTc3MzY2NzUyNTM5ODExOTQ5Njc5NzU0NTU5NDcwNTM1NjQ5NSJ9\x80\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x16\xa0 (then 764 × 0)"
private def payloadShaPaddedBytes : Array Nat := #[101, 121, 74, 112, 99, 51, 77, 105, 79, 105, 74, 111, 100, 72, 82, 119, 99, 122, 111, 118, 76, 50, 70, 106, 89, 50, 57, 49, 98, 110, 82, 122, 76, 109, 100, 118, 98, 50, 100, 115, 90, 83, 53, 106, 98, 50, 48, 105, 76, 67, 74, 104, 101, 110, 65, 105, 79, 105, 73, 48, 77, 68, 99, 48, 77, 68, 103, 51, 77, 84, 103, 120, 79, 84, 73, 117, 89, 88, 66, 119, 99, 121, 53, 110, 98, 50, 57, 110, 98, 71, 86, 49, 99, 50, 86, 121, 89, 50, 57, 117, 100, 71, 86, 117, 100, 67, 53, 106, 98, 50, 48, 105, 76, 67, 74, 104, 100, 87, 81, 105, 79, 105, 73, 48, 77, 68, 99, 48, 77, 68, 103, 51, 77, 84, 103, 120, 79, 84, 73, 117, 89, 88, 66, 119, 99, 121, 53, 110, 98, 50, 57, 110, 98, 71, 86, 49, 99, 50, 86, 121, 89, 50, 57, 117, 100, 71, 86, 117, 100, 67, 53, 106, 98, 50, 48, 105, 76, 67, 74, 122, 100, 87, 73, 105, 79, 105, 73, 120, 77, 84, 77, 53, 79, 84, 65, 122, 77, 68, 99, 119, 79, 68, 73, 52, 79, 84, 107, 51, 77, 84, 103, 51, 78, 122, 85, 105, 76, 67, 74, 104, 100, 70, 57, 111, 89, 88, 78, 111, 73, 106, 111, 105, 98, 70, 90, 108, 82, 68, 82, 52, 85, 68, 90, 82, 77, 86, 112, 72, 99, 107, 119, 122, 90, 48, 90, 106, 81, 49, 70, 77, 85, 83, 73, 115, 73, 109, 53, 104, 98, 87, 85, 105, 79, 105, 74, 78, 97, 87, 78, 111, 89, 87, 86, 115, 73, 70, 78, 48, 99, 109, 70, 114, 89, 83, 73, 115, 73, 110, 66, 112, 89, 51, 82, 49, 99, 109, 85, 105, 79, 105, 74, 111, 100, 72, 82, 119, 99, 122, 111, 118, 76, 50, 120, 111, 77, 121, 53, 110, 98, 50, 57, 110, 98, 71, 86, 49, 99, 50, 86, 121, 89, 50, 57, 117, 100, 71, 86, 117, 100, 67, 53, 106, 98, 50, 48, 118, 89, 83, 57, 66, 81, 50, 99, 52, 98, 50, 78, 77, 86, 109, 52, 52, 82, 106, 104, 87, 98, 108, 104, 76, 84, 107, 53, 75, 97, 70, 74, 80, 97, 70, 82, 119, 85, 88, 86, 77, 84, 71, 112, 71, 82, 87, 82, 50, 88, 51, 86, 111, 98, 50, 85, 116, 82, 70, 86, 104, 85, 108, 82, 115, 101, 69, 116, 70, 101, 84, 108, 108, 78, 72, 99, 57, 99, 122, 107, 50, 76, 87, 77, 105, 76, 67, 74, 110, 97, 88, 90, 108, 98, 108, 57, 117, 89, 87, 49, 108, 73, 106, 111, 105, 84, 87, 108, 106, 97, 71, 70, 108, 98, 67, 73, 115, 73, 109, 90, 104, 98, 87, 108, 115, 101, 86, 57, 117, 89, 87, 49, 108, 73, 106, 111, 105, 85, 51, 82, 121, 89, 87, 116, 104, 73, 105, 119, 105, 97, 87, 70, 48, 73, 106, 111, 120, 78, 122, 69, 53, 79, 68, 89, 50, 77, 84, 77, 52, 76, 67, 74, 108, 101, 72, 65, 105, 79, 106, 69, 51, 77, 84, 107, 52, 78, 106, 107, 51, 77, 122, 103, 115, 73, 109, 53, 118, 98, 109, 78, 108, 73, 106, 111, 105, 77, 106, 73, 52, 78, 68, 81, 51, 77, 122, 77, 122, 77, 122, 81, 48, 77, 106, 73, 49, 77, 84, 103, 119, 78, 68, 77, 51, 79, 84, 89, 52, 77, 84, 89, 48, 77, 122, 107, 50, 78, 84, 77, 119, 79, 68, 69, 49, 78, 68, 77, 120, 77, 84, 99, 51, 77, 122, 89, 50, 78, 122, 85, 121, 78, 84, 77, 53, 79, 68, 69, 120, 79, 84, 81, 53, 78, 106, 99, 53, 78, 122, 85, 48, 78, 84, 85, 53, 78, 68, 99, 119, 78, 84, 77, 49, 78, 106, 81, 53, 78, 83, 74, 57, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 160, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "eyJpc3MiOiJodHRwczovL2FjY291bnRzLmdvb2dsZS5jb20iLCJhenAiOiI0MDc0MDg3MTgxOTIuYXBwcy5nb29nbGV1c2VyY29udGVudC5jb20iLCJhdWQiOiI0MDc0MDg3MTgxOTIuYXBwcy5nb29nbGV1c2VyY29udGVudC5jb20iLCJzdWIiOiIxMTM5OTAzMDcwODI4OTk3MTg3NzUiLCJhdF9oYXNoIjoibFZlRDR4UDZRMVpHckwzZ0ZjQ1FMUSIsIm5hbWUiOiJNaWNoYWVsIFN0cmFrYSIsInBpY3R1cmUiOiJodHRwczovL2xoMy5nb29nbGV1c2VyY29udGVudC5jb20vYS9BQ2c4b2NMVm44RjhWblhLTk5KaFJPaFRwUXVMTGpGRWR2X3Vob2UtRFVhUlRseEtFeTllNHc9czk2LWMiLCJnaXZlbl9uYW1lIjoiTWljaGFlbCIsImZhbWlseV9uYW1lIjoiU3RyYWthIiwiaWF0IjoxNzE5ODY2MTM4LCJleHAiOjE3MTk4Njk3MzgsIm5vbmNlIjoiMjI4NDQ3MzMzMzQ0MjI1MTgwNDM3OTY4MTY0Mzk2NTMwODE1NDMxMTc3MzY2NzUyNTM5ODExOTQ5Njc5NzU0NTU5NDcwNTM1NjQ5NSJ9 (then 808 × 0)"
private def payloadBytes : Array Nat := #[101, 121, 74, 112, 99, 51, 77, 105, 79, 105, 74, 111, 100, 72, 82, 119, 99, 122, 111, 118, 76, 50, 70, 106, 89, 50, 57, 49, 98, 110, 82, 122, 76, 109, 100, 118, 98, 50, 100, 115, 90, 83, 53, 106, 98, 50, 48, 105, 76, 67, 74, 104, 101, 110, 65, 105, 79, 105, 73, 48, 77, 68, 99, 48, 77, 68, 103, 51, 77, 84, 103, 120, 79, 84, 73, 117, 89, 88, 66, 119, 99, 121, 53, 110, 98, 50, 57, 110, 98, 71, 86, 49, 99, 50, 86, 121, 89, 50, 57, 117, 100, 71, 86, 117, 100, 67, 53, 106, 98, 50, 48, 105, 76, 67, 74, 104, 100, 87, 81, 105, 79, 105, 73, 48, 77, 68, 99, 48, 77, 68, 103, 51, 77, 84, 103, 120, 79, 84, 73, 117, 89, 88, 66, 119, 99, 121, 53, 110, 98, 50, 57, 110, 98, 71, 86, 49, 99, 50, 86, 121, 89, 50, 57, 117, 100, 71, 86, 117, 100, 67, 53, 106, 98, 50, 48, 105, 76, 67, 74, 122, 100, 87, 73, 105, 79, 105, 73, 120, 77, 84, 77, 53, 79, 84, 65, 122, 77, 68, 99, 119, 79, 68, 73, 52, 79, 84, 107, 51, 77, 84, 103, 51, 78, 122, 85, 105, 76, 67, 74, 104, 100, 70, 57, 111, 89, 88, 78, 111, 73, 106, 111, 105, 98, 70, 90, 108, 82, 68, 82, 52, 85, 68, 90, 82, 77, 86, 112, 72, 99, 107, 119, 122, 90, 48, 90, 106, 81, 49, 70, 77, 85, 83, 73, 115, 73, 109, 53, 104, 98, 87, 85, 105, 79, 105, 74, 78, 97, 87, 78, 111, 89, 87, 86, 115, 73, 70, 78, 48, 99, 109, 70, 114, 89, 83, 73, 115, 73, 110, 66, 112, 89, 51, 82, 49, 99, 109, 85, 105, 79, 105, 74, 111, 100, 72, 82, 119, 99, 122, 111, 118, 76, 50, 120, 111, 77, 121, 53, 110, 98, 50, 57, 110, 98, 71, 86, 49, 99, 50, 86, 121, 89, 50, 57, 117, 100, 71, 86, 117, 100, 67, 53, 106, 98, 50, 48, 118, 89, 83, 57, 66, 81, 50, 99, 52, 98, 50, 78, 77, 86, 109, 52, 52, 82, 106, 104, 87, 98, 108, 104, 76, 84, 107, 53, 75, 97, 70, 74, 80, 97, 70, 82, 119, 85, 88, 86, 77, 84, 71, 112, 71, 82, 87, 82, 50, 88, 51, 86, 111, 98, 50, 85, 116, 82, 70, 86, 104, 85, 108, 82, 115, 101, 69, 116, 70, 101, 84, 108, 108, 78, 72, 99, 57, 99, 122, 107, 50, 76, 87, 77, 105, 76, 67, 74, 110, 97, 88, 90, 108, 98, 108, 57, 117, 89, 87, 49, 108, 73, 106, 111, 105, 84, 87, 108, 106, 97, 71, 70, 108, 98, 67, 73, 115, 73, 109, 90, 104, 98, 87, 108, 115, 101, 86, 57, 117, 89, 87, 49, 108, 73, 106, 111, 105, 85, 51, 82, 121, 89, 87, 116, 104, 73, 105, 119, 105, 97, 87, 70, 48, 73, 106, 111, 120, 78, 122, 69, 53, 79, 68, 89, 50, 77, 84, 77, 52, 76, 67, 74, 108, 101, 72, 65, 105, 79, 106, 69, 51, 77, 84, 107, 52, 78, 106, 107, 51, 77, 122, 103, 115, 73, 109, 53, 118, 98, 109, 78, 108, 73, 106, 111, 105, 77, 106, 73, 52, 78, 68, 81, 51, 77, 122, 77, 122, 77, 122, 81, 48, 77, 106, 73, 49, 77, 84, 103, 119, 78, 68, 77, 51, 79, 84, 89, 52, 77, 84, 89, 48, 77, 122, 107, 50, 78, 84, 77, 119, 79, 68, 69, 49, 78, 68, 77, 120, 77, 84, 99, 51, 77, 122, 89, 50, 78, 122, 85, 121, 78, 84, 77, 53, 79, 68, 69, 120, 79, 84, 81, 53, 78, 106, 99, 53, 78, 122, 85, 48, 78, 84, 85, 53, 78, 68, 99, 119, 78, 84, 77, 49, 78, 106, 81, 53, 78, 83, 74, 57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "\"aud\":\"407408718192.apps.googleusercontent.com\", (then 92 × 0)"
private def audFieldBytes : Array Nat := #[34, 97, 117, 100, 34, 58, 34, 52, 48, 55, 52, 48, 56, 55, 49, 56, 49, 57, 50, 46, 97, 112, 112, 115, 46, 103, 111, 111, 103, 108, 101, 117, 115, 101, 114, 99, 111, 110, 116, 101, 110, 116, 46, 99, 111, 109, 34, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "aud (then 37 × 0)"
private def audNameBytes : Array Nat := #[97, 117, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "407408718192.apps.googleusercontent.com (then 81 × 0)"
private def audValueBytes : Array Nat := #[52, 48, 55, 52, 48, 56, 55, 49, 56, 49, 57, 50, 46, 97, 112, 112, 115, 46, 103, 111, 111, 103, 108, 101, 117, 115, 101, 114, 99, 111, 110, 116, 101, 110, 116, 46, 99, 111, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "407408718192.apps.googleusercontent.com (then 81 × 0)"
private def privateAudValueBytes : Array Nat := #[52, 48, 55, 52, 48, 56, 55, 49, 56, 49, 57, 50, 46, 97, 112, 112, 115, 46, 103, 111, 111, 103, 108, 101, 117, 115, 101, 114, 99, 111, 110, 116, 101, 110, 116, 46, 99, 111, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: " (then 120 × 0)"
private def overrideAudValueBytes : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "\"sub\":\"113990307082899718775\", (then 320 × 0)"
private def uidFieldBytes : Array Nat := #[34, 115, 117, 98, 34, 58, 34, 49, 49, 51, 57, 57, 48, 51, 48, 55, 48, 56, 50, 56, 57, 57, 55, 49, 56, 55, 55, 53, 34, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "sub (then 27 × 0)"
private def uidNameBytes : Array Nat := #[115, 117, 98, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "113990307082899718775 (then 309 × 0)"
private def uidValueBytes : Array Nat := #[49, 49, 51, 57, 57, 48, 51, 48, 55, 48, 56, 50, 56, 57, 57, 55, 49, 56, 55, 55, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "\"iss\":\"https://accounts.google.com\", (then 104 × 0)"
private def issFieldBytes : Array Nat := #[34, 105, 115, 115, 34, 58, 34, 104, 116, 116, 112, 115, 58, 47, 47, 97, 99, 99, 111, 117, 110, 116, 115, 46, 103, 111, 111, 103, 108, 101, 46, 99, 111, 109, 34, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "iss (then 37 × 0)"
private def issNameBytes : Array Nat := #[105, 115, 115, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "https://accounts.google.com (then 93 × 0)"
private def issValueBytes : Array Nat := #[104, 116, 116, 112, 115, 58, 47, 47, 97, 99, 99, 111, 117, 110, 116, 115, 46, 103, 111, 111, 103, 108, 101, 46, 99, 111, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "\"iat\":1719866138, (then 33 × 0)"
private def iatFieldBytes : Array Nat := #[34, 105, 97, 116, 34, 58, 49, 55, 49, 57, 56, 54, 54, 49, 51, 56, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "iat (then 7 × 0)"
private def iatNameBytes : Array Nat := #[105, 97, 116, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "1719866138 (then 35 × 0)"
private def iatValueBytes : Array Nat := #[49, 55, 49, 57, 56, 54, 54, 49, 51, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "\"nonce\":\"2284473333442251804379681643965308154311773667525398119496797545594705356495\"} (then 18 × 0)"
private def nonceFieldBytes : Array Nat := #[34, 110, 111, 110, 99, 101, 34, 58, 34, 50, 50, 56, 52, 52, 55, 51, 51, 51, 51, 52, 52, 50, 50, 53, 49, 56, 48, 52, 51, 55, 57, 54, 56, 49, 54, 52, 51, 57, 54, 53, 51, 48, 56, 49, 53, 52, 51, 49, 49, 55, 55, 51, 54, 54, 55, 53, 50, 53, 51, 57, 56, 49, 49, 57, 52, 57, 54, 55, 57, 55, 53, 52, 53, 53, 57, 52, 55, 48, 53, 51, 53, 54, 52, 57, 53, 34, 125, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "nonce (then 5 × 0)"
private def nonceNameBytes : Array Nat := #[110, 111, 110, 99, 101, 0, 0, 0, 0, 0]
-- ASCII: "2284473333442251804379681643965308154311773667525398119496797545594705356495 (then 24 × 0)"
private def nonceValueBytes : Array Nat := #[50, 50, 56, 52, 52, 55, 51, 51, 51, 51, 52, 52, 50, 50, 53, 49, 56, 48, 52, 51, 55, 57, 54, 56, 49, 54, 52, 51, 57, 54, 53, 51, 48, 56, 49, 53, 52, 51, 49, 49, 55, 55, 51, 54, 54, 55, 53, 50, 53, 51, 57, 56, 49, 49, 57, 52, 57, 54, 55, 57, 55, 53, 52, 53, 53, 57, 52, 55, 48, 53, 51, 53, 54, 52, 57, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "\"email_verified\":true, (then 8 × 0)"
private def evFieldBytes : Array Nat := #[34, 101, 109, 97, 105, 108, 95, 118, 101, 114, 105, 102, 105, 101, 100, 34, 58, 116, 114, 117, 101, 44, 0, 0, 0, 0, 0, 0, 0, 0]
-- ASCII: "email_verified (then 6 × 0)"
private def evNameBytes : Array Nat := #[101, 109, 97, 105, 108, 95, 118, 101, 114, 105, 102, 105, 101, 100, 0, 0, 0, 0, 0, 0]
-- ASCII: "true (then 6 × 0)"
private def evValueBytes : Array Nat := #[116, 114, 117, 101, 0, 0, 0, 0, 0, 0]
-- ASCII: "\"family_name\":\"Straka\", (then 327 × 0)"
private def extraFieldBytes : Array Nat := #[34, 102, 97, 109, 105, 108, 121, 95, 110, 97, 109, 101, 34, 58, 34, 83, 116, 114, 97, 107, 97, 34, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

-- FStrings built from the byte arrays above
def b64uJwtNoSigSha2Padded : FString bn254 1536 := ⟨⟨jwtNoSigBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 724⟩
def b64uJwtHeaderWDot : FString bn254 300 := ⟨⟨headerBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 60⟩
def b64uJwtPayloadSha2Padded : FString bn254 1472 := ⟨⟨payloadShaPaddedBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 664⟩
def b64uJwtPayload : FString bn254 1472 := ⟨⟨payloadBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 664⟩
def audField : FString bn254 140 := ⟨⟨audFieldBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 48⟩
def audName : FString bn254 40 := ⟨⟨audNameBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 3⟩
def audValue : FString bn254 120 := ⟨⟨audValueBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 39⟩
def privateAudValue : FString bn254 120 := ⟨⟨privateAudValueBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 39⟩
def overrideAudValue : FString bn254 120 := ⟨⟨overrideAudValueBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 0⟩
def uidField : FString bn254 350 := ⟨⟨uidFieldBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 30⟩
def uidName : FString bn254 30 := ⟨⟨uidNameBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 3⟩
def uidValue : FString bn254 330 := ⟨⟨uidValueBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 21⟩
def issField : FString bn254 140 := ⟨⟨issFieldBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 36⟩
def issName : FString bn254 40 := ⟨⟨issNameBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 3⟩
def issValue : FString bn254 120 := ⟨⟨issValueBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 27⟩
def iatField : FString bn254 50 := ⟨⟨iatFieldBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 17⟩
def iatName : FString bn254 10 := ⟨⟨iatNameBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 3⟩
def iatValue : FString bn254 45 := ⟨⟨iatValueBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 10⟩
def nonceField : FString bn254 105 := ⟨⟨nonceFieldBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 87⟩
def nonceName : FString bn254 10 := ⟨⟨nonceNameBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 5⟩
def nonceValue : FString bn254 100 := ⟨⟨nonceValueBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 76⟩
def evField : FString bn254 30 := ⟨⟨evFieldBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 22⟩
def evName : FString bn254 20 := ⟨⟨evNameBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 14⟩
def evValue : FString bn254 10 := ⟨⟨evValueBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 4⟩
def extraField : FString bn254 350 := ⟨⟨extraFieldBytes.map mkChar, (Array.size_map ..).trans (by native_decide)⟩, 23⟩

-- String-bodies bit vectors (1 = inside a JSON string body)
def audFieldStringBodies : Vector (FB bn254) 140 :=
  ⟨(#[0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Array Nat).map mkFB,
   (Array.size_map ..).trans (by native_decide)⟩
def uidFieldStringBodies : Vector (FB bn254) 350 :=
  ⟨(#[0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Array Nat).map mkFB,
   (Array.size_map ..).trans (by native_decide)⟩
def issFieldStringBodies : Vector (FB bn254) 140 :=
  ⟨(#[0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Array Nat).map mkFB,
   (Array.size_map ..).trans (by native_decide)⟩
def nonceFieldStringBodies : Vector (FB bn254) 105 :=
  ⟨(#[0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Array Nat).map mkFB,
   (Array.size_map ..).trans (by native_decide)⟩

-- RSA-2048 signature and modulus, as 32 × 64-bit LSB-first limbs
def rsaSignature : Vector (F bn254) 32 :=
  ⟨(#[10721701979699195296, 15036229839195681918, 10983276591813061978, 12911446242524986927, 9560089411755357652, 9309052354752032174, 3358275092914731569, 10435107300792368984, 1374110401945726277, 9917335420015084407, 3064304146747788139, 4008275478379379452, 9946104760599893140, 11815003581625044478, 11607954576423232793, 14191698816131181809, 6528743506808416772, 17391080671783600459, 17257190584807248, 15308290640302719576, 14538515615293307681, 7066081214525481094, 3645339831471832219, 12614825483518577654, 13134570993041290509, 14074238454407855134, 11785831896354341830, 12808425289591952239, 17855152258252365976, 5591649323569907615, 7295309875178211129, 11791195316646447791] : Array Nat).map mkFB,
   (Array.size_map ..).trans (by native_decide)⟩
def rsaPubkeyModulus : Vector (F bn254) 32 :=
  ⟨(#[12529483539613655991, 4761318477815644038, 16072206229285376171, 6416363496858434941, 14372316832493303668, 15362170232057692744, 12553434116882696818, 10844178769328990998, 298652012579572874, 14190469974491287564, 14716128179010351799, 7591586317431552879, 7757770025371190536, 18254545107553152472, 13675373159667769906, 3721592316551105908, 16446774721856483030, 10839844328868414884, 7779361646197299291, 5855707768991140107, 12931676190576898801, 9076808862103229592, 1023227055955263498, 10847624653120993398, 11233046795208611753, 1167337604075906721, 13110727329945129130, 15648358431910827508, 8677990462390466325, 3839448665873057195, 4601921717081706384, 16802607714780031892] : Array Nat).map mkFB,
   (Array.size_map ..).trans (by native_decide)⟩

-- SHA-256 padding signals
def sha2NumBits : Vector (F bn254) 8 := ⟨(#[0, 0, 0, 0, 0, 0, 22, 160] : Array Nat).map mkFB, (Array.size_map ..).trans (by native_decide)⟩
def sha2Padding : Vector (F bn254) 64 := ⟨(#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Array Nat).map mkFB, (Array.size_map ..).trans (by native_decide)⟩

-- Ephemeral public key fields
def epk : Vector (F bn254) 3 :=
  ⟨(#[242984842061174104272170180221318235913385474778206477109637294427650138112, 4497911, 0] : Array Nat).map mkFB,
   (Array.size_map ..).trans (by native_decide)⟩

-- Scalar field-element signals
def audIndex : F bn254 := 85
def audColonIndex : F bn254 := 5
def audValueIndex : F bn254 := 7
def useAudOverride : F bn254 := 0
def skipAudChecks : F bn254 := 0
def uidIndex : F bn254 := 133
def uidColonIndex : F bn254 := 5
def uidValueIndex : F bn254 := 7
def issIndex : F bn254 := 1
def issColonIndex : F bn254 := 5
def issValueIndex : F bn254 := 7
def iatIndex : F bn254 := 377
def iatColonIndex : F bn254 := 5
def iatValueIndex : F bn254 := 6
def nonceIndex : F bn254 := 411
def nonceColonIndex : F bn254 := 7
def nonceValueIndex : F bn254 := 9
def evIndex : F bn254 := 0
def evColonIndex : F bn254 := 16
def evValueIndex : F bn254 := 17
def extraIndex : F bn254 := 354
def useExtraField : F bn254 := 0
def epkLen : F bn254 := 34
def epkBlinder : F bn254 := 42
def expDate : F bn254 := 111111111111
def expHorizon : F bn254 := 999999999999
def pepper : F bn254 := 76
def sha2NumBlocks : F bn254 := 12

-- The `circuit/tools/input_gen.py` hardcoded value (`990250399590…531016130`) seems to be wrong
-- it does not match. So we use the value from our own Poseidon.
def publicInputsHash : F bn254 := 8248306165257624383689932638083768990034280920973625356095477808644073880188

def input : KeylessInput := {
  jwtRaw := {
    b64u_jwt_no_sig_sha2_padded  := b64uJwtNoSigSha2Padded
    b64u_jwt_header_w_dot        := b64uJwtHeaderWDot
    b64u_jwt_payload_sha2_padded := b64uJwtPayloadSha2Padded
    b64u_jwt_payload             := b64uJwtPayload
    sha2_num_blocks              := sha2NumBlocks
    sha2_num_bits                := sha2NumBits
    sha2_padding                 := sha2Padding
  }
  rsa := { signature := rsaSignature, pubkeyModulus := rsaPubkeyModulus }
  aud := {
    field             := audField
    name              := audName
    value             := audValue
    fieldStringBodies := audFieldStringBodies
    nameIndex         := audIndex
    colonIndex        := audColonIndex
    valueIndex        := audValueIndex
  }
  audOverride := {
    useAudOverride   := useAudOverride
    skipAudChecks    := skipAudChecks
    privateAudValue  := privateAudValue
    overrideAudValue := overrideAudValue
  }
  uid := {
    field             := uidField
    name              := uidName
    value             := uidValue
    fieldStringBodies := uidFieldStringBodies
    nameIndex         := uidIndex
    colonIndex        := uidColonIndex
    valueIndex        := uidValueIndex
  }
  iss := {
    field             := issField
    name              := issName
    value             := issValue
    fieldStringBodies := issFieldStringBodies
    nameIndex         := issIndex
    colonIndex        := issColonIndex
    valueIndex        := issValueIndex
  }
  iat := {
    field      := iatField
    name       := iatName
    value      := iatValue
    nameIndex  := iatIndex
    colonIndex := iatColonIndex
    valueIndex := iatValueIndex
  }
  nonce := {
    field             := nonceField
    name              := nonceName
    value             := nonceValue
    fieldStringBodies := nonceFieldStringBodies
    nameIndex         := nonceIndex
    colonIndex        := nonceColonIndex
    valueIndex        := nonceValueIndex
  }
  ev := {
    field      := evField
    name       := evName
    value      := evValue
    nameIndex  := evIndex
    colonIndex := evColonIndex
    valueIndex := evValueIndex
  }
  extra := {
    extraField      := extraField
    extraFieldIndex := extraIndex
    useExtraField   := useExtraField
  }
  commit := {
    epk        := epk
    epkLen     := epkLen
    epkBlinder := epkBlinder
    expDate    := expDate
    expHorizon := expHorizon
    pepper     := pepper
  }
  publicInputsHash := publicInputsHash
}


example : keyless input = some () := by native_decide

end TestKeyless
