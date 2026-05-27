import Clap.Lang
import Clap.Sha2.Basic
import Clap.Sha2.Circuit
import Clap.Packing
import Clap.FString
import Clap.HashToField

namespace Clap.Sha2.Keyless

open Clap.Lang Primes
open Clap.Sha2

-- Re-export the Keyless constants we need (avoids circular import with Keyless.lean)
abbrev MAX_B64U_JWT_NO_SIG_LEN := 1536
abbrev SHA2_PADDING_LEN  := 64
abbrev SHA2_NUM_BITS_LEN := 8

/-- Convert 8 × F32 SHA2-256 hash words to 4 × 64-bit limbs for RSA verification.

    SHA2-256 outputs 8 × 32-bit words (most significant first):
      H = word[0] ‖ word[1] ‖ ... ‖ word[7]   (256 bits, word[0] most significant)

    RSA expects 4 × 64-bit limbs in little-endian limb order (limb 0 = least
    significant 64 bits), where each 64-bit limb is formed by pairing two
    adjacent 32-bit words:
      limb[0] = word[6] * 2^32 + word[7]   (least significant 64 bits of hash)
      limb[1] = word[4] * 2^32 + word[5]
      limb[2] = word[2] * 2^32 + word[3]
      limb[3] = word[0] * 2^32 + word[1]   (most significant 64 bits of hash)

    Each F32 is stored LSB-first, but `FBitVec.toF` (= `bits2num`) interprets
    LSB-first bits and produces the correct scalar value of the 32-bit integer.
    So `FBitVec.toF word[i]` already gives us the integer value of that word —
    no bit-level reversal is needed.

    Once we have the 8 words as scalars, combining them into 64-bit limbs is
    pure field arithmetic: `limb = wHi * 2^32 + wLo`.

    Equivalence to the CIRCOM pipeline:

    CIRCOM (keyless.circom):
      signal message_limbs[4] <== BigEndianBitsToScalars(256, 64)(message_bits);
      for (var i = 0; i < 4; i++) { message_limbs_le[i] = message_limbs[3 - i]; }
-/
def hashToRSALimbs (hash : Array (F32 bn254)) : Vector (F bn254) 4 :=
  -- Convert each F32 (LSB-first bits) directly to its scalar value.
  let w := hash.map FBitVec.toF
  -- Combine adjacent 32-bit words into 64-bit limbs via field arithmetic.
  -- SHA output: word[0] is the MSB 32 bits of the hash, word[7] is the LSB 32 bits.
  -- RSA: limb[0] must be the LSB 64 bits of the hash, limb[3] the MSB 64 bits.
  let limb0 := w[6]! * (2^32 : F bn254) + w[7]!  -- bytes 24-31 of hash (least significant)
  let limb1 := w[4]! * (2^32 : F bn254) + w[5]!  -- bytes 16-23
  let limb2 := w[2]! * (2^32 : F bn254) + w[3]!  -- bytes  8-15
  let limb3 := w[0]! * (2^32 : F bn254) + w[1]!  -- bytes  0- 7 (most significant)
  #v[limb0, limb1, limb2, limb3]

/-- Process all SHA2-256 blocks and collect every intermediate hash state.
    Returns an array where `result[i]` is the hash state after processing blocks 0..i.

    This mirrors CIRCOM's `SHA2_256_Prepadded_Hash`, which instantiates `Sha256compression`
    for ALL MAX_NUM_BLOCKS and then uses `SingleOneArray(tBlock)` to select the output
    at the terminating block. We collect all states and let the caller select via
    `selectArrayValue`. -/
private def processAllBlocks
    (blocks : Array (Block (F32 bn254))) (acc : Hash (F32 bn254))
    (i : Nat) (states : Array (Hash (F32 bn254))) : Option (Array (Hash (F32 bn254))) := do
  if i >= blocks.size then pure states else
  let acc ← @compress Option _ (Circuit.t bn254) Circuit.instSha Circuit.instU32Monadic acc blocks[i]!
  processAllBlocks blocks acc (i + 1) (states.push acc)

open FString FArray HashToField

/-- Validate K (number of zero bits in SHA2 padding) and return (K+1)/8.

    `K` is computed by the caller as `num_blocks*512 - padding_start*8 - 1 - 64`.
    This function enforces two constraints and returns the derived byte count:

    1. **Range check:** K < 512 (fits in 9 bits, per RFC 4634). This ensures
       the padding fits within one block boundary. Matches CIRCOM: `_ <== Num2Bits(9)(K);`

    2. **Byte-alignment check:** K mod 8 = 7. This is an invariant that always
       holds for byte-aligned messages: `K ≡ 447 - 8B (mod 512) ⇒ K mod 8 = 7`.
       CIRCOM does not assert this explicitly, it writes `(1+K)/8` as field
       division, which silently fails in downstream substring checks when the
       invariant is violated.

    Returns `(K+1)/8` = the number of "padding without length" bytes (the 0x80
    byte plus K/8 zero bytes). Computed as `K/8 + 1` from the upper 6 bits of
    the 9-bit decomposition of K — no field division needed.

    CIRCOM use sites:
      `AssertIsSubstring(..., padding_without_len, (1+K)/8, padding_start)`
      `AssertIsSubstring(..., L_byte_encoded, 8, padding_start + (K+1)/8)`
-/
def kPlus1Div8 (K : F bn254) : Option (F bn254) := do
  -- Range check (K < 512) + reuse the bit decomposition below.
  let Kbits ← FBitVec.ofF 9 K
  -- Assert K mod 8 = 7 (low 3 bits = [1, 1, 1], value 7).
  F.assert_eq (FBitVec.toF (Kbits.take 3)) 7
  -- K / 8 = upper 6 bits interpreted as a field element.
  -- (K + 1) / 8 = K/8 + 1  (valid because K + 1 is divisible by 8).
  pure (FBitVec.toF (Kbits.drop 3) + 1)

/-- SHA2-256 verified digest: verifies RFC 4634 padding and computes the hash.

    Replaces both CIRCOM stubs:
    - `SHA2_256_PaddingVerify(MAX_INPUT_LEN)`: padding verification
    - `SHA2_256_Prepadded_Hash(MAX_NUM_BLOCKS)`: hash computation

    The prover provides the padded message and metadata as witnesses. This function
    verifies the padding is RFC 4634 §4.1 compliant, then hashes the padded data
    using our SHA2-256 implementation and returns 4 × 64-bit limbs for RSA.

    Arguments:
    - `data`: The full SHA2-padded JWT byte array (FString)
    - `paddingStart`: Byte offset where real data ends / SHA2 padding begins. In keyless.circom this is `b64u_jwt_header_w_dot_len + b64u_jwt_payload_sha2_padded_len`.
    - `sha2NumBlocks`: Number of 512-bit (64-byte) SHA2 blocks in the padded data.
    - `sha2NumBits`: 8-byte big-endian encoding of L (message length in bits = 8 * paddingStart). CIRCOM signal: `sha2_num_bits[8]`.
    - `sha2Padding`: 64-byte padding witness: sha2Padding[0] = 0x80, rest zeros. CIRCOM signal: `sha2_padding[64]`.

    Returns:
    SHA2-256 hash as 4 × 64-bit limbs in little-endian limb order (ready for RSA).

    CIRCOM reference:
    keyless.circom calls:
      SHA2_256_PaddingVerify(MAX_B64U_JWT_NO_SIG_LEN)(
          b64u_jwt_no_sig_sha2_padded, sha2_num_blocks,
          b64u_jwt_header_w_dot_len + b64u_jwt_payload_sha2_padded_len,
          sha2_num_bits, sha2_padding);
      signal jwt_hash[256] <== SHA2_256_Prepadded_Hash(SHA2_MAX_NUM_BLOCKS)(
          in <== Bytes2BigEndianBits(...)(b64u_jwt_no_sig_sha2_padded),
          tBlock <== sha2_num_blocks - 1);
-/
def sha256VerifiedDigest
    (data : FString bn254 MAX_B64U_JWT_NO_SIG_LEN)
    (paddingStart : F bn254)
    (sha2NumBlocks : F bn254)
    (sha2NumBits : Vector (F bn254) SHA2_NUM_BITS_LEN)
    (sha2Padding : Vector (F bn254) SHA2_PADDING_LEN)
    : Option (Vector (F bn254) 4) := do

  -- Padding verification (RFC 4634 §4.1)

  -- K = number of zero bits between the leading 1-bit and the 64-bit length field.
  -- CIRCOM (PaddingVerify.circom):
  --   var len_bits = num_blocks * 512;
  --   var padding_start_bits = padding_start * 8;
  --   var K = len_bits - padding_start_bits - 1 - 64;
  let K := sha2NumBlocks * 512 - paddingStart * 8 - 1 - 64

  -- Validate K and compute (K+1)/8 = number of padding bytes before the length field.
  -- Encapsulates the range check (K < 512) and byte-alignment (K mod 8 = 7).
  -- See `kPlus1Div8` for details.
  let KPlus1Div8 ← kPlus1Div8 K

  -- Compute the Fiat-Shamir hash seed for substring checks.
  -- CIRCOM (PaddingVerify.circom):
  --   signal in_hash <== HashBytesToFieldWithLen(MAX_INPUT_LEN)(in, num_blocks*64);
  -- The length argument is the total padded byte count (= num_blocks * 64 bytes).
  let dataHash ← hashBytesToFieldWithLen data.chars (sha2NumBlocks * 64)

  -- RFC 4634 §4.1.a: The padding bytes (0x80 followed by K/8 zero bytes) appear
  -- at position `paddingStart` in the data.
  -- CIRCOM (PaddingVerify.circom):
  --   AssertIsSubstring(MAX_INPUT_LEN, 64)(in, in_hash, padding_without_len, (1+K)/8, padding_start);
  -- We wrap sha2Padding as an FString for the substring check.
  let paddingFStr : FString bn254 SHA2_PADDING_LEN := ⟨sha2Padding, KPlus1Div8⟩
  assertIsSubstringFS (by decide) data dataHash paddingFStr paddingStart

  -- RFC 4634 §4.1.a: First padding byte must be 0x80 (binary: 10000000).
  -- CIRCOM (PaddingVerify.circom): padding_without_len[0] === 128;
  F.assert_eq sha2Padding[0]! 128

  -- RFC 4634 §4.1.b: All remaining padding bytes (indices 1..63) must be zero.
  -- CIRCOM (PaddingVerify.circom):
  --   for (var i = 1; i < 64; i++) { padding_without_len[i] === 0; }
  for h : i in [1:64] do F.assert_eq sha2Padding[i] 0

  -- RFC 4634 §4.1.c: The 8-byte big-endian length encoding appears immediately
  -- after the zero-padded bytes.
  -- CIRCOM (PaddingVerify.circom):
  --   AssertIsSubstring(MAX_INPUT_LEN, 8)(in, in_hash, L_byte_encoded, 8, padding_start+(K+1)/8);
  let numBitsFStr : FString bn254 SHA2_NUM_BITS_LEN := ⟨sha2NumBits, 8⟩
  assertIsSubstringFS (by decide) data dataHash numBitsFStr (paddingStart + KPlus1Div8)

  -- RFC 4634 §4.1.c: The decoded length must equal 8 * paddingStart (message length in bits).
  -- CIRCOM (PaddingVerify.circom):
  --   signal L_bits[64] <== Bytes2BigEndianBits(8)(L_byte_encoded);
  --   signal L_decoded <== BigEndianBits2Num(64)(L_bits);
  --   L_decoded === 8*padding_start;
  let lBits ← Packing.bytes2BigEndianBits sha2NumBits
  let lDecoded := Packing.bigEndianBits2Num lBits
  F.assert_eq lDecoded (8 * paddingStart)

  -- SHA2-256 hash computation (SHA2_256_Prepadded_Hash.circom)
  --
  -- CIRCOM instantiates Sha256compression for ALL MAX_NUM_BLOCKS blocks, then uses
  -- a one-hot selector (SingleOneArray) to pick the output at `tBlock = numBlocks - 1`.
  --
  -- CIRCOM reference (keyless.circom):
  --   var SHA2_MAX_NUM_BLOCKS = (MAX_B64U_JWT_NO_SIG_LEN * 8) \ 512;
  --   signal jwt_hash[256] <== SHA2_256_Prepadded_Hash(SHA2_MAX_NUM_BLOCKS)(
  --       in <== Bytes2BigEndianBits(MAX_B64U_JWT_NO_SIG_LEN)(b64u_jwt_no_sig_sha2_padded),
  --       tBlock <== sha2_num_blocks - 1);

  -- TODO can we get rid of this conversion?
  let data_as_vec : FByteArray p MAX_B64U_JWT_NO_SIG_LEN ← data.chars.mapM FBV8.ofF
  let blocks := (@parse_blocks (Circuit.t bn254) Circuit.instSha 24 data_as_vec).toArray
  -- Process all blocks and collect intermediate hash states.
  let allStates ← processAllBlocks blocks (@initial_hash (Circuit.t bn254) Circuit.instSha) 0 #[]
  let tBlock := sha2NumBlocks - 1
  let mut hash : Array (F32 bn254) := #[]
  for wordIdx in [:8] do
    -- Build an array of the wordIdx-th word from each state
    let wordAcrossStates : Vector (F bn254) allStates.size := ⟨allStates.map (fun state => FBitVec.toF state[wordIdx]!), by simp⟩
    let selectedWord ← selectArrayValue wordAcrossStates tBlock
    let selectedBits ← F32.ofF selectedWord
    hash := hash.push selectedBits

  -- Output conversion (8 × F32 → 4 × 64-bit limbs)
  -- BigEndianBitsToScalars(256, 64) + limb reversal in keyless.circom
  pure (hashToRSALimbs hash)

end Clap.Sha2.Keyless

-- Tests

open Clap.Sha2.Keyless
open Clap.Sha2
open Clap.Lang Primes

def FBV8.ofF! {p:ℕ} [Fact (Nat.Prime p)] [Fact (Primes.fits p 8)] : F p → FBV8 p := Clap.num2bitsLsbPureV 8

namespace TestKPlus1Div8

open Clap.Sha2.Keyless
open Clap.Lang Primes

-- Expected behavior:
--   K ∈ [0, 512) with K mod 8 = 7  →  some ((K+1)/8)   (valid byte-aligned K)
--   K ∈ [0, 512) with K mod 8 ≠ 7  →  none             (byte-alignment fails)
--   K ≥ 512                        →  none             (range check fails)
-- Valid K values for byte-aligned SHA2 padding: {7, 15, 23, ..., 511} (64 values).
example : (List.range 512).all (fun k ↦
    kPlus1Div8 k = (if k % 8 = 7 then some (((k + 1) / 8) : F bn254) else none))
  := by native_decide

-- Spot-check out-of-range values: all should return none.
example : kPlus1Div8 (512 : F bn254) = none := by native_decide
example : kPlus1Div8 (519 : F bn254) = none := by native_decide  -- the "55-byte bug" K value
example : kPlus1Div8 (1000 : F bn254) = none := by native_decide
example : kPlus1Div8 (2^20 : F bn254) = none := by native_decide

end TestKPlus1Div8

namespace TestHashToRSALimbs

-- SHA-256("abc") = ba7816bf 8f01cfea 414140de 5dae2223 b00361a3 96177a9c b410ff61 f20015ad
-- As 4 × 64-bit limbs (big-endian limb order):
--   limb[0] = 0xba7816bf_8f01cfea (most significant)
--   limb[1] = 0x414140de_5dae2223
--   limb[2] = 0xb00361a3_96177a9c
--   limb[3] = 0xb410ff61_f20015ad (least significant)
-- After reversal (little-endian limb order for RSA):
--   limb[0] = 0xb410ff61_f20015ad
--   limb[1] = 0xb00361a3_96177a9c
--   limb[2] = 0x414140de_5dae2223
--   limb[3] = 0xba7816bf_8f01cfea

private instance : Clap.Sha2.Sha (Clap.Sha2.Circuit.t bn254) := Clap.Sha2.Circuit.instSha
private instance : Clap.Sha2.U32Monadic Option (F32 bn254) := Clap.Sha2.Circuit.instU32Monadic

private def abcHash : Option (Hash (F32 bn254)) :=
  let bytes : Array (FBV8 bn254) := (#[97, 98, 99] : Array Nat).map (fun (n : Nat) => FBV8.ofF! (n : F bn254))
  Clap.Sha2.digest (t := Clap.Sha2.Circuit.t bn254) ⟨bytes, rfl⟩

example : (do
  let hash ← abcHash
  pure (hashToRSALimbs hash.toArray)) =
  some #v[0xb410ff61f20015ad, 0xb00361a396177a9c, 0x414140de5dae2223, 0xba7816bf8f01cfea]
:= by native_decide

end TestHashToRSALimbs

namespace TestSha256VerifiedDigest

-- Construct a valid SHA2-padded version of "abc" (3 bytes → 1 block = 64 bytes).
-- Padding: [97, 98, 99, 128, 0×52, 0, 0, 0, 0, 0, 0, 24]
-- (0x80 at position 3, then 52 zero bytes, then 8-byte big-endian length = 24 bits)
-- Remaining bytes up to MAX_B64U_JWT_NO_SIG_LEN (1536) are zeros.

private def mkTestData : FString bn254 MAX_B64U_JWT_NO_SIG_LEN :=
  let msgBytes : Array (F bn254) := #[97, 98, 99]  -- "abc"
  let paddingByte : Array (F bn254) := #[128]       -- 0x80
  let zeros52 : Array (F bn254) := Array.replicate 52 0
  let lenBytes : Array (F bn254) := #[0, 0, 0, 0, 0, 0, 0, 24]  -- 24 bits = 3 bytes
  let padded := msgBytes ++ paddingByte ++ zeros52 ++ lenBytes
  let chars := padded ++ Array.replicate (MAX_B64U_JWT_NO_SIG_LEN - padded.size) 0
  ⟨⟨chars, by native_decide⟩, 64⟩

private def testPaddingStart : F bn254 := 3
private def testNumBlocks : F bn254 := 1
private def testNumBits : Vector (F bn254) 8 := #v[0, 0, 0, 0, 0, 0, 0, 24]
private def testPadding : Vector (F bn254) 64 :=
  ⟨#[128] ++ Array.replicate 63 0, by native_decide⟩

example : sha256VerifiedDigest mkTestData testPaddingStart testNumBlocks testNumBits testPadding =
  some #v[0xb410ff61f20015ad, 0xb00361a396177a9c, 0x414140de5dae2223, 0xba7816bf8f01cfea]
:= by native_decide

end TestSha256VerifiedDigest

namespace TestMultiBlock

-- "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" (56 bytes)
-- SHA-256 = 248d6a61 d20638b8 e5c02693 0c3e6039 a33ce459 64ff2167 f6ecedd4 19db06c1
-- This message requires 2 SHA2 blocks (56 + 1 + 0 + 8 > 64, so padding pushes to 128 bytes).
-- Padding: msg(56) ++ [0x80] ++ zeros(63) ++ length(8) = 128 bytes = 2 blocks
-- Length = 56 * 8 = 448 bits = 0x01C0

private def msg56 : Array (F bn254) :=
  "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8.data.map (·.toNat)

private def mkTestData56 : FString bn254 MAX_B64U_JWT_NO_SIG_LEN :=
  let paddingByte : Array (F bn254) := #[128]
  let zeros63 : Array (F bn254) := Array.replicate 63 0
  let lenBytes : Array (F bn254) := #[0, 0, 0, 0, 0, 0, 1, 0xC0]
  let padded : Array (F bn254) := msg56 ++ paddingByte ++ zeros63 ++ lenBytes
  let chars := padded ++ Array.replicate (MAX_B64U_JWT_NO_SIG_LEN - padded.size) 0
  ⟨⟨chars, by native_decide⟩, 128⟩

private def testPaddingStart56 : F bn254 := 56
private def testNumBlocks56 : F bn254 := 2
private def testNumBits56 : Vector (F bn254) 8 := #v[0, 0, 0, 0, 0, 0, 1, 0xC0]
private def testPadding56 : Vector (F bn254) 64 :=
  ⟨#[128] ++ Array.replicate 63 0, by native_decide⟩

-- Expected limbs (little-endian limb order):
-- SHA-256 = 248d6a61 d20638b8 e5c02693 0c3e6039 a33ce459 64ff2167 f6ecedd4 19db06c1
-- BE limbs: [0x248d6a61d20638b8, 0xe5c026930c3e6039, 0xa33ce45964ff2167, 0xf6ecedd419db06c1]
-- LE limbs (reversed): [0xf6ecedd419db06c1, 0xa33ce45964ff2167, 0xe5c026930c3e6039, 0x248d6a61d20638b8]

example : sha256VerifiedDigest mkTestData56 testPaddingStart56 testNumBlocks56 testNumBits56 testPadding56 =
  some #v[0xf6ecedd419db06c1, 0xa33ce45964ff2167, 0xe5c026930c3e6039, 0x248d6a61d20638b8]
:= by native_decide

end TestMultiBlock

namespace TestCrossCheck

/-!
`digest` vs `sha256VerifiedDigest`

These tests verify the new `sha256VerifiedDigest` (padding verification + hash via
`processAllBlocks` + state selection + limb conversion) produces the same result as
`hashToRSALimbs (digest msg)`, the original `digest` function followed by limb packing.

This confirms that:
The padding verification does not corrupt or alter the hash computation.
The `processAllBlocks` + `selectArrayValue` pattern (mirroring CIRCOM's one-hot selector) yields the same hash state as `digest`'s direct sequential compression.
The output conversion chain (F32 → big-endian bits → 64-bit limbs → LE order) is consistent between both paths.
-/

private instance : Sha (Circuit.t bn254) := Circuit.instSha
private instance : U32Monadic Option (F32 bn254) := Circuit.instU32Monadic

-- Helper: run digest on raw bytes and convert to RSA limbs (Path A)
private def digestToLimbs (msg : Array (F bn254)) : Option (Vector (F bn254) 4) := do
  let f8Msg : Array (FBV8 bn254) ← msg.mapM FBV8.ofF
  let hash ← Clap.Sha2.digest (t := Circuit.t bn254) ⟨f8Msg, rfl⟩
  pure (hashToRSALimbs hash.toArray)

-- (1) "abc" (3 bytes, 1 block)

-- digest on raw "abc"
private def pathA_abc := digestToLimbs #[97, 98, 99]

-- sha256VerifiedDigest on padded "abc" (reusing the test data from TestSha256VerifiedDigest)
private def mkPaddedAbc : FString bn254 MAX_B64U_JWT_NO_SIG_LEN :=
  let padded := #[97, 98, 99, 128] ++ Array.replicate 52 0 ++ #[0, 0, 0, 0, 0, 0, 0, 24]
  let fullPadded := padded ++ Array.replicate (MAX_B64U_JWT_NO_SIG_LEN - padded.size) 0
  ⟨⟨fullPadded, by native_decide⟩, 64⟩

private def pathB_abc :=
  sha256VerifiedDigest mkPaddedAbc 3 1 #v[0, 0, 0, 0, 0, 0, 0, 24]
    ⟨#[128] ++ Array.replicate 63 0, by native_decide⟩

-- Both produce the same result
example : pathA_abc = pathB_abc := by native_decide

-- (2): 56-byte message (2 blocks)

private def msg56Bytes  : Array (F bn254) :=
  "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8.data.map (·.toNat)

-- digest on raw 56-byte message
private def pathA_56 := digestToLimbs msg56Bytes

-- sha256VerifiedDigest on padded 56-byte message
private def mkPadded56 : FString bn254 MAX_B64U_JWT_NO_SIG_LEN :=
  let padded : Array (F bn254) := msg56Bytes ++ #[(128 : F bn254)] ++ Array.replicate 63 (0 : F bn254) ++ #[(0 : F bn254), 0, 0, 0, 0, 0, 1, 0xC0]
  let fullPadded : Array (F bn254) := padded ++ Array.replicate (MAX_B64U_JWT_NO_SIG_LEN - padded.size) 0
  ⟨⟨fullPadded, by native_decide⟩, 128⟩

private def pathB_56 :=
  sha256VerifiedDigest mkPadded56 56 2 #v[0, 0, 0, 0, 0, 0, 1, 0xC0]
    ⟨#[128] ++ Array.replicate 63 0, by native_decide⟩

-- Both produce the same result
example : pathA_56 = pathB_56 := by native_decide

end TestCrossCheck
