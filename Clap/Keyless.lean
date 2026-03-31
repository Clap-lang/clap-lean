import Clap.Lang
import Clap.Wheels
import Clap.Array
import Clap.FString
import Clap.HashToField
import Clap.JWT
import Clap.Poseidon.Poseidon
import Clap.Base64Len

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

open Clap.Lang Core Primes

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

/-- Stub for SHA2-256 padding verification. WIP. -/
def SHA2_256_PaddingVerify
    (_data : FString bn254 MAX_B64U_JWT_NO_SIG_LEN)
    (_sha2_num_blocks : F bn254)
    (_sha2_num_bits : Vector (F bn254) SHA2_NUM_BITS_LEN)
    (_sha2_padding : Vector (F bn254) SHA2_PADDING_LEN)
    : Option Unit :=
  pure ()

/-- Stub for SHA2-256 hash of pre-padded data. WIP.
    Returns the SHA2-256 hash as 4 × 64-bit limbs. -/
def SHA2_256_Prepadded_Hash
    (_data : FString bn254 MAX_B64U_JWT_NO_SIG_LEN)
    (_sha2_num_blocks : F bn254)
    : Option (Vector (F bn254) 4) :=
  pure (Vector.replicate 4 0)

/-- Stub for RSA-2048 PKCS#1 v1.5 signature verification. WIP. -/
def RSA_2048_e_65537_PKCS1_V1_5_Verify
    (_sha2_hash : Vector (F bn254) 4)
    (_signature : Vector (F bn254) RSA_NUM_LIMBS)
    (_pubkey_modulus : Vector (F bn254) RSA_NUM_LIMBS)
    : Option Unit :=
  pure ()

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
  NameIndex  : F bn254
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
  signature      : Vector (F bn254) RSA_NUM_LIMBS
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
  epk         : Vector (F bn254) EPK_NUM_FIELDS
  epkLen      : F bn254
  epkBlinder : F bn254
  expDate    : F bn254
  expHorizon : F bn254
  pepper      : F bn254

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
  payload            : FString bn254 MAX_JWT_PAYLOAD_LEN
  payload_hash       : F bn254
  string_bodies      : Vector (FB bn254) MAX_JWT_PAYLOAD_LEN
  brackets_depth_map : List (F bn254)

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

/-- Verify JWT structural integrity.
    Concatenation, SHA2 padding, SHA2 hash, RSA signature, and base64 decode.
    Returns the decoded JWT payload as an FString. -/
def verifyJWTStructure (jwtRaw : JWTRawInput) (rsa : RSAInput)
    : Option (FString bn254 MAX_JWT_PAYLOAD_LEN) := do
  -- Step 1: Assert header_w_dot ++ payload_sha2_padded = jwt_no_sig_sha2_padded
  FString.assertIsConcatenation (by decide) (by decide)
    jwtRaw.b64u_jwt_no_sig_sha2_padded jwtRaw.b64u_jwt_header_w_dot jwtRaw.b64u_jwt_payload_sha2_padded
  -- Assert the last character of header_w_dot is '.' (ASCII 46)
  -- This prevents the circuit from being tricked about where the payload starts.
  -- CIRCOM: dot === 46
  let dot ← selectArrayValue (jwtRaw.b64u_jwt_no_sig_sha2_padded.chars.map FBitVec.toF) (jwtRaw.b64u_jwt_header_w_dot.len - 1)
  F.assert_eq dot 46
  -- Step 2: SHA2-256 padding verification
  SHA2_256_PaddingVerify jwtRaw.b64u_jwt_no_sig_sha2_padded jwtRaw.sha2_num_blocks jwtRaw.sha2_num_bits jwtRaw.sha2_padding
  -- Step 3: SHA2-256 hash (STUB)
  let sha2Hash ← SHA2_256_Prepadded_Hash jwtRaw.b64u_jwt_no_sig_sha2_padded jwtRaw.sha2_num_blocks
  -- Step 4: RSA signature verification (STUB)
  RSA_2048_e_65537_PKCS1_V1_5_Verify sha2Hash rsa.signature rsa.pubkeyModulus
  -- Step 4b: Assert b64u_jwt_payload is a valid prefix of b64u_jwt_payload_sha2_padded
  -- This removes SHA2 padding and ensures consistency.
  -- CIRCOM: AssertIsSubstring(b64u_jwt_payload_sha2_padded, ..., b64u_jwt_payload, ..., 0)
  let paddedHash ← hashBytesToFieldWithLen (jwtRaw.b64u_jwt_payload_sha2_padded.chars.map FBitVec.toF) jwtRaw.b64u_jwt_payload_sha2_padded.len
  assertIsSubstringFS (by decide) jwtRaw.b64u_jwt_payload_sha2_padded paddedHash jwtRaw.b64u_jwt_payload 0
  -- Step 5: Base64-decode the payload
  let b64uPayloadArr := (jwtRaw.b64u_jwt_payload.chars.map FBitVec.toF).toArray
  let jwtPayload ← Base64Len.base64UrlDecode MAX_JWT_PAYLOAD_LEN b64uPayloadArr
  -- Compute decoded length: floor(3 * encoded_len / 4)
  let jwtPayloadLen ← Base64Len.base64UrlDecodedLength 20 jwtRaw.b64u_jwt_payload.len
  -- Build FString from decoded payload (may be shorter than MAX_JWT_PAYLOAD_LEN, pad with zeros)
  let padded := jwtPayload ++ Array.replicate (MAX_JWT_PAYLOAD_LEN - jwtPayload.size) 0
  let chars_f : Vector (F bn254) MAX_JWT_PAYLOAD_LEN := ⟨padded.take MAX_JWT_PAYLOAD_LEN, by simp [padded]; omega⟩
  let chars ← chars_f.mapM F8.ofF
  return ⟨chars, jwtPayloadLen⟩

/-- Phase 2: Compute JSON structural analysis from the decoded JWT payload.
    Returns the payload with its hash, string bodies, and brackets depth map. -/
def computeJSONStructure
    (payload : FString bn254 MAX_JWT_PAYLOAD_LEN)
    : Option JSONStructure := do
  -- Compute payload hash
  let payload_hash ← hashBytesToFieldWithLen (payload.chars.map FBitVec.toF) payload.len
  -- JSON structural analysis on raw field elements
  let payload_list := (payload.chars.map FBitVec.toF).toList
  let string_bodies := JWT.stringBodies payload_list
  let inverted := string_bodies.map FB.not
  let brackets_map := JWT.bracketsMap payload_list
  let unquoted_brackets := inverted.zipWith (· * ·) brackets_map
  let brackets_depth_map := JWT.bracketsDepthMap unquoted_brackets
  let string_bodies_vec : Vector (FB bn254) MAX_JWT_PAYLOAD_LEN :=
    ⟨string_bodies.toArray, by simp [string_bodies, payload_list]⟩
  return { payload, payload_hash, string_bodies := string_bodies_vec, brackets_depth_map }


-- Top-level circuit

/-- The Aptos Keyless circuit. Verifies a JWT-based identity claim in zero knowledge. -/
def keyless (input : KeylessInput) : Option Unit := do
  -- Phase 1: JWT structural verification (concatenation, base64, SHA2, RSA)
  let jwtPayload ← verifyJWTStructure input.jwtRaw input.rsa

  -- Phase 2: Compute JSON structure for field parsing
  let json ← computeJSONStructure jwtPayload

  pure ()

end Keyless
