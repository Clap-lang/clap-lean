import Clap.Lang
import Clap.Array
import Clap.FString
import Clap.HashToField
import Clap.Base64Len
import Clap.JWT

namespace Keyless

open Clap.Lang Core Primes FString FArray Base64Len HashToField JWT

abbrev p := Primes.bn254

variable [Core p]

/-- From keyless.circom.
  The main Aptos Keyless circuit.

  Max lengths:
  `max_B64U_JWT_no_sig_len` -
    Max lenght in bytesfor the full base64url JWT without the signature, but with SHA2 padding
  `max_B64U_JWT_header_w_dot_len` -
    Max lenght in bytes for the full base64url JWT header with a dot at the end
  `max_B64U_JWT_payload_SHA2_padded_len` -
    Max lenght in bytes for the full base64url JWT payload with SHA2 padding
  `max_AUD_KV_pair_len` -
    Max lenght in bytes for the ASCII aud field
  `max_AUD_name_len` -
    Max lenght in bytes for the ASCII aud name
  `max_AUD_value_len` -
    Max lenght in bytes for the ASCII aud value
  `max_ISS_KV_pair_len` -
    Max lenght in bytes for the ASCII iss field
  `max_ISS_name_len` -
    Max lenght in bytes for the ASCII iss name
  `max_ISS_value_len` -
    Max lenght in bytes for the ASCII iss value
  `max_IAT_KV_pair_len` -
    Max lenght in bytes for the ASCII iat field
  `max_IAT_name_len` -
    Max lenght in bytes for the ASCII iat name
  `max_IAT_value_len` -
    Max lenght in bytes for the ASCII iat value
  `max_Nonce_KV_pair_len` -
    Max lenght in bytes for the ASCII nonce field
  `max_Nonce_name_len` -
    Max lenght in bytes for the ASCII nonce name
  `max_Nonce_value_len` -
    Max lenght in bytes for the ASCII nonce value
  `max_Email_verified_KV_pair_len` -
    Max lenght in bytes for the ASCII email verified field
  `max_Email_verified_name_len` -
    Max lenght in bytes for the ASCII email verified name
  `max_Email_verified_value_len` -
    Max lenght in bytes for the ASCII email verified value
  `max_UID_KV_pair_len` -
    Max lenght in bytes for the ASCII uid field
  `max_UID_name_len` -
    Max lenght in bytes for the ASCII uid name
  `max_UID_value_len` -
    Max lenght in bytes for the ASCII uid value
  `max_Extra_Field_KV_pair_len` -
    Max lenght in bytes for the ASCII extra field

  JWT splitting into header and payload:
  `b64u_jwt_no_sig_sha2_padded` -
    Base64url-encoded JWT header + payload + SHA2 padding, but without RSA signature
  `b64u_jwt_header_w_dot` -
    Base64url-encoded JWT header + the ASCII dot following it
  `b64u_jwt_header_w_dot_len`

  `b64u_jwt_payload_sha2_padded` -
    Base64url-encoded JWT payload with SHA2 padding
  `b64u_jwt_payload_sha2_padded_len`

-/
def keyless
  (max_B64U_JWT_no_sig_len : ℕ)
  (max_B64U_JWT_header_w_dot_len : ℕ)
  (max_B64U_JWT_payload_SHA2_padded_len : ℕ)
  (max_AUD_KV_pair_len : ℕ)
  (max_AUD_name_len : ℕ)
  (max_AUD_value_len : ℕ)
  (max_ISS_KV_pair_len : ℕ)
  (max_ISS_name_len : ℕ)
  (max_ISS_value_len : ℕ)
  (max_IAT_KV_pair_len : ℕ)
  (max_IAT_name_len : ℕ)
  (max_IAT_value_len : ℕ)
  (max_Nonce_KV_pair_len : ℕ)
  (max_Nonce_name_len : ℕ)
  (max_Nonce_value_len : ℕ)
  (max_Email_verified_KV_pair_len : ℕ)
  (max_Email_verified_name_len : ℕ)
  (max_Email_verified_value_len : ℕ)
  (max_UID_KV_pair_len : ℕ)
  (max_UID_name_len : ℕ)
  (max_UID_value_len : ℕ)
  (max_Extra_Field_KV_pair_len : ℕ)
  --
  (b64u_jwt_no_sig_sha2_padded : FString p max_B64U_JWT_no_sig_len)
  (b64u_jwt_header_w_dot : FString p max_B64U_JWT_header_w_dot_len)
  -- (b64u_jwt_header_w_dot_len : F p)
  (b64u_jwt_payload_sha2_padded : FString p max_B64U_JWT_payload_SHA2_padded_len)
  (b64u_jwt_payload : FString p max_B64U_JWT_payload_SHA2_padded_len)
  (aud_field : FString p max_AUD_KV_pair_len)
  (aud_field_string_bodies : FString p max_AUD_KV_pair_len)
  (aud_field_len aud_index use_aud_override : F p)
  (aud_value private_aud_value override_aud_value : FString p max_AUD_value_len)
  (aud_name : FString p max_AUD_name_len)
  (private_aud_value_len override_aud_value_len skip_aud_checks aud_colon_index : F p)
  -- (b64u_jwt_payload_sha2_padded_len : F p)
 : Option Unit
:= do
  /- From keyless.circom.
    Several templates (e.g., Poseidon-BN254 templates, LessThan) assume the
    BN254 curve is used, whose scalar field can represent any 253-bit number
    (but not necessarily any 254-bit one). Here, we check that the scalar
    field satisfies this assumption. -/
  assert! Primes.fits p 253

  --  1. Global variables

  --  1.1 RSA-2048 signatures and pubkeys are stored as 32 limbs of 64 bits (8 bytes) each
  let signatureNumLimbs := 32

  --  1.2 The maximum length of a base64url-decoded JWT payload.
  let max_JWT_payload_Len := 3 * max_B64U_JWT_payload_SHA2_padded_len / 4;

  /- From keyless.circom.
    Checks that the base64url-encoded JWT payload & header are correctly concatenated:
    i.e., that `b64u_jwt_no_sig_sha2_padded` is the concatenation of
    `b64u_jwt_header_w_dot` with` b64u_jwt_payload_sha2_padded`
  -/
  if
    h_len :
      max_B64U_JWT_header_w_dot_len ≤ max_B64U_JWT_no_sig_len ∧
        max_B64U_JWT_payload_SHA2_padded_len ≤ max_B64U_JWT_no_sig_len
  then
    assertIsConcatenation h_len.1 h_len.2
      b64u_jwt_no_sig_sha2_padded
      b64u_jwt_header_w_dot
      b64u_jwt_payload_sha2_padded
  else .none

  /- TODO?
    `b64u_jwt_no_sig_sha2_padded` is converted to `Vector (F p)` both in
    `assertIsConcatenation` and below, before being passed to `selectArrayValue`.
    Could this be optimized?
  -/

  let b64u_jwt_no_sig_sha2_padded :=
    b64u_jwt_no_sig_sha2_padded.chars.map FBitVec.toF
  let dot ←
    selectArrayValue (p := p) b64u_jwt_no_sig_sha2_padded b64u_jwt_header_w_dot.len
  F.assert_eq dot 46

  assertIsSubstring
    b64u_jwt_payload_sha2_padded
    b64u_jwt_payload
    b64u_jwt_payload_sha2_padded.len

  /-
    SHA2-256 hashing
  -/

  -- SHA2_256_PaddingVerify
  -- SHA2_256_Prepadded_Hash


  /-
    JWT RSA signature verification
  -/

  -- RSA_2048_e_65537_PKCS1_V1_5_Verify

  /-
    Decoding the base64url-encoded JWT
  -/
  let b64u_jwt_payload :=
    b64u_jwt_payload.chars.map FBitVec.toF |>.toArray
  let jwt_payload ←
    base64UrlDecode max_B64U_JWT_payload_SHA2_padded_len b64u_jwt_payload
  let jwt_payload_len ←
    base64UrlDecodedLength
      max_B64U_JWT_payload_SHA2_padded_len
      b64u_jwt_payload_sha2_padded.len
  -- Is this actually needed?
  let jwt_payload_hash ←
    hashBytesToFieldWithLen jwt_payload.toVector jwt_payload_len

  /-
    Computing hints for securing our JWT parsing
  -/

  /- From keyless.circom.
    Contains 1s between unescaped quotes, and 0s everywhere else. Used to
    prevent a fake field inside quotes from being accepted as valid
  -/
  let string_bodies := stringBodies jwt_payload.toList


  /- From keyless.circom.
  To prevent attacks involving fields inside nested brackets, we perform the
    following steps:
  1. Take the inverse of the string bodies array, turning each `1` into `0`,
    and each `0` into `1`
  2. Create an array marking open brackets (1) and closed brackets (-1) in
    the ASCII JWT payload, with 0 elsewhere
  3. Use the array from 1 to eliminate quoted brackets in 2 with element-wise
    multiplication
  4. Use the array from 3 to make an array with 1+ inside brackets and 0
    everywhere else, not including the outermost brackets of the JWT payload
  5. Use the array from 4 to check there are no characters of a given field
    (such as aud) inside of nested brackets. This is done per field
  -/
  let inverted_string_bodies := string_bodies.map FB.not
  let brackets_map := bracketsMap jwt_payload.toList
  let unquoted_brackets_map :=
    inverted_string_bodies.zipWith (· * ·) brackets_map
  let unquoted_brackets_depth_map := bracketsMap unquoted_brackets_map

  /-
    JWT field matching
  -/

  --  Check aud field is in the JWT
  let jwt_payload_chars : Array (FChar p) ← jwt_payload.mapM (fun a ↦ F8.ofF a)
  let jwt_payloadStr : FString p _ :=
    {
      /- If `max_JWT_payload_Len` is greater than the actual size of
        `jwt_payload`, we don't need to add trailing zeros. They wouldn't matter
        for the result of `assertIsSubstring jwt_payloadStr`.
      -/
      chars := jwt_payload_chars.toVector.take max_JWT_payload_Len
      len := jwt_payload_len
    }
  -- `jwt_payload_hash` supposed to be used here, but probably not needed
  assertIsSubstring jwt_payloadStr aud_field aud_index
  assertIsSubstring jwt_payloadStr aud_field_string_bodies aud_index
  enforceNotNested max_JWT_payload_Len aud_index aud_field_len
    unquoted_brackets_depth_map

  --  Perform necessary checks on aud field
  let AUD_NAME_LEN := 3
  let aud_name := {aud_name with len := AUD_NAME_LEN}

  eq0 <| use_aud_override * (1 - use_aud_override)

  /- From keyless.circom
    We never want to skip aud checks in the JWT while using aud override -
    the aud override value should always be checked against the JWT when
    `use_aud_override` is equal to 1.
  -/
  let skip_aud_checks_and_use_aud_override :=
    FB.and skip_aud_checks use_aud_override
  eq0 skip_aud_checks_and_use_aud_override

  eq0 <| skip_aud_checks * (skip_aud_checks - 1)

  let aud_value : FString p max_AUD_value_len :=
    { chars :=
        override_aud_value.chars.zipWith
          (fun override_aud_valueᵢ private_aud_valueᵢ ↦
            -- if use_aud_override then override_aud_valueᵢ else private_aud_valueᵢ
            -- Both should be 8 bits, so xor should be safe.
            (FBitVec.xor override_aud_valueᵢ private_aud_valueᵢ).map (· * use_aud_override)
              |> FBitVec.xor private_aud_valueᵢ
          )
          private_aud_value.chars

      len :=
        -- if use_aud_override then override_aud_value_len else private_aud_value_len
        (override_aud_value_len - private_aud_value_len) * use_aud_override
          + private_aud_value_len
    }
  let aud_field_string_bodies := aud_field_string_bodies.chars.map FBitVec.toF
  if
    h_len :
      max_AUD_name_len ≤ max_AUD_KV_pair_len ∧
        max_AUD_value_len ≤ max_AUD_KV_pair_len
  then
    parseJWTFieldWithQuotedValue h_len.1 h_len.2 aud_field aud_name aud_value
      aud_field_string_bodies
      aud_colon_index skip_aud_checks
  else .none

  let perform_aud_checks := FB.not skip_aud_checks;
  -- a * performCheck = b * performCheck;
  let conditionallyAssertEq (performCheck : FB p) (a b : F8 p) : Option Unit :=
    let different := a.zipWith (fun aᵢ bᵢ ↦ performCheck * FB.xor aᵢ bᵢ) b
    FB.assert (F8.eq F8.zero different)

  if _ : aud_name.chars.size > 2 then
    -- aud_name[0] = F8.ofF 'a'.toNat
    conditionallyAssertEq perform_aud_checks aud_name.chars[0] [1, 0, 0, 0, 0, 1, 1, 0]
    -- aud_name[1] = F8.ofF 'u'.toNat
    conditionallyAssertEq perform_aud_checks aud_name.chars[1] [1, 0, 1, 0, 1, 1, 1, 0]
    -- aud_name[2] = F8.ofF 'd'.toNat
    conditionallyAssertEq perform_aud_checks aud_name.chars[2] [0, 0, 1, 0, 0, 1, 1, 0]
  else .none

end Keyless

namespace TestKeyless

open Clap.Lang Core Clap.Spec ZMod
open FChar FString

abbrev p := Primes.bn254

end TestKeyless
