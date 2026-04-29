import Clap.Keyless
import Clap.Test.KeylessFixture

/-!
# End-to-end tests for `Keyless.keyless`

Each test feeds a concrete `KeylessInput` from `KeylessTestFixture` (built
from the canonical `circuit/tools/input_gen.py` output via
`scripts/input_json_to_lean.py`) into the top-level `keyless` circuit and
asserts the expected accept (`some ()`) or reject (`none`). Scenarios are
modeled after the Rust prover-service test suite at
`doc/keyless-zk-proofs/prover-service/src/tests/prover_handler.rs`.

WARNING: each `native_decide` runs SHA-256 over the full 1536-byte JWT,
RSA-2048 PKCS#1 v1.5 verify, Poseidon hashes, base64 decode, and JSON
structural checks. Compile time is on the order of 90–120 s per positive
end-to-end test.
-/

namespace TestKeyless
open Clap.Lang Core Primes ZMod Keyless KeylessTestFixture
open HashToField FString FArray Clap.RSA

-- ---------------------------------------------------------------------------
-- Per-stage tests on the canonical Google JWT fixture (Happy)
-- These run sub-circuits in isolation; cheaper to compile than the full
-- pipeline and useful for bisecting if a regression appears.
-- ---------------------------------------------------------------------------

/-- Length consistency: `jwt.len = header.len + payload.len`. -/
example : Happy.input.jwtRaw.b64u_jwt_no_sig_sha2_padded.len = 724 := by native_decide
example : Happy.input.jwtRaw.b64u_jwt_header_w_dot.len = 60 := by native_decide
example : Happy.input.jwtRaw.b64u_jwt_payload_sha2_padded.len = 664 := by native_decide

/-- The dot character (ASCII 46) sits at `header_w_dot.len - 1` (= byte 59). -/
example : (do
    let dot ← selectArrayValue Happy.input.jwtRaw.b64u_jwt_no_sig_sha2_padded.toVF
              (Happy.input.jwtRaw.b64u_jwt_header_w_dot.len - 1)
    F.assert_eq dot 46) = some () := by native_decide

/-- SHA-256 verified digest accepts the canonical padded JWT. -/
example : (Clap.Sha2.Keyless.sha256VerifiedDigest
    Happy.input.jwtRaw.b64u_jwt_no_sig_sha2_padded
    (Happy.input.jwtRaw.b64u_jwt_header_w_dot.len + Happy.input.jwtRaw.b64u_jwt_payload_sha2_padded.len)
    Happy.input.jwtRaw.sha2_num_blocks
    Happy.input.jwtRaw.sha2_num_bits
    Happy.input.jwtRaw.sha2_padding).isSome = true := by native_decide

/-- The `b64u_jwt_payload` is a prefix of `b64u_jwt_payload_sha2_padded` (substring check). -/
example : (do
    let h ← hashBytesToFieldWithLen Happy.input.jwtRaw.b64u_jwt_payload_sha2_padded.toVF
              Happy.input.jwtRaw.b64u_jwt_payload_sha2_padded.len
    assertIsSubstringFS (by decide) Happy.input.jwtRaw.b64u_jwt_payload_sha2_padded h
      Happy.input.jwtRaw.b64u_jwt_payload 0) = some () := by native_decide

/-- Base64url decoding of the unsigned payload succeeds. -/
example : (do
    let _ ← Base64Len.base64UrlDecode MAX_JWT_PAYLOAD_LEN Happy.input.jwtRaw.b64u_jwt_payload.toVF.toArray
    let _ ← Base64Len.base64UrlDecodedLength 20 Happy.input.jwtRaw.b64u_jwt_payload.len
    pure ()).isSome = true := by native_decide

-- ---------------------------------------------------------------------------
-- End-to-end positive scenarios
-- ---------------------------------------------------------------------------

/-- `prove_default_request` analog: canonical Aptos test JWT (issuer
    `https://accounts.google.com`, the same OIDC provider AIP-061 uses),
    `uid_key = "sub"`, `extra_field = "family_name"` (use_extra=0). -/
example : keyless Happy.input = some () := by native_decide

/-- `prove_request_with_aud_recovery` analog: same JWT, but the verifier-facing
    aud is presented through the override path (`useAudOverride = 1`,
    `overrideAudValue = JWT-aud`). The `private_aud_value` (= original aud
    used to derive the registered IDC) still flows into the IDC computation
    via `computeIdentityCommitment`. -/
example : keyless AudOverride.input = some () := by native_decide

/-- IDC-migration / aud-skip path: `skipAudChecks = 1` zeroes out the IDC's
    aud contribution and bypasses every aud-related constraint
    (`useAudOverride` must remain 0 for the binary-conjunction guard
    `eq0 (skipAudChecks * useAudOverride)`). -/
example : keyless SkipAudChecks.input = some () := by native_decide

-- ---------------------------------------------------------------------------
-- Negative tests: mutated inputs must be rejected
-- These exercise the soundness side of `keyless` — every mutation flips a
-- single field of the `Happy` input and asserts the circuit returns `none`.
-- ---------------------------------------------------------------------------

/-- Tampered RSA signature (every limb doubled, mod p) → RSA verify fails →
    `keyless = none`. Doubling is convenient because it preserves the Vector
    type without needing index-bound proofs. -/
example :
  let bad : KeylessInput := { Happy.input with
    rsa := { Happy.input.rsa with
      signature := Happy.input.rsa.signature.map (· * 2) } }
  keyless bad = none := by native_decide

/-- Wrong `publicInputsHash` (set to 0) → final Poseidon-14 equality fails →
    `keyless = none`. Runs the full pipeline so it's the slowest negative test. -/
example :
  let bad : KeylessInput := { Happy.input with publicInputsHash := 0 }
  keyless bad = none := by native_decide

end TestKeyless
