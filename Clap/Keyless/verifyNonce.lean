import Clap.RandomOracle.HashFn
import Clap.Lang.Poseidon.Computes
import Clap.Lang.Data.FString.asciiDigitsToScalar
import Clap.Keyless.Input
import Clap.Lang.Poseidon.Poseidon

open Clap Lang FString Primes

/-- Verify the nonce field matches the cryptographic commitment.
    `nonceValue` (from JWT) must equal `Poseidon(epk[0..2], epkLen, expDate, epkBlinder)`. -/
def verifyNonce (nonceValue : FString bn254 MAX_NONCE_VALUE_LEN)
  (commit : CommitmentInput bn254) :
  ClapM bn254 Unit
:= do
  -- Compute expected nonce: Poseidon(epk[0], epk[1], epk[2], epkLen, expDate, epkBlinder)
  let expectedNonce ←
    Poseidon.poseidonBN254
      #v[ commit.epk[0], commit.epk[1], commit.epk[2], commit.epkLen, commit.expDate, commit.epkBlinder ]
  -- Convert nonce value (ASCII digits) to scalar
  let nonceScalar ← FString.asciiDigitsToScalar nonceValue
  -- Assert equality
  assert_eq nonceScalar expectedNonce

namespace verifyNonce

open Poseidon RandomOracle

lemma convertsM {H : HashFn} (h_H : Computes H) {state : ClapMState bn254}
  {commit : CommitmentInput bn254}
  {nonce : FString bn254 MAX_NONCE_VALUE_LEN}
  -- Ideal values
  {nonceValues_vals : Vector (ZMod bn254) MAX_NONCE_VALUE_LEN}
  {nonceLen_val : ZMod bn254}
  {epk_vals : Vector (ZMod bn254) EPK_NUM_FIELDS}
  {epkLen_val epkBlinder_val expDate_val : ZMod bn254}
  -- Separate `Converts` hypotheses for `data` and `len`
  -- as in `asciiDigitsToScalar.convertsM`
  (h_input      : Converts FVec.conversion state nonce.data nonceValues_vals)
  (h_len        : Converts F.conversion    state nonce.len nonceLen_val)
  (h_epk        : Converts FVec.conversion state commit.epk epk_vals)
  (h_epkLen     : Converts F.conversion    state commit.epkLen epkLen_val)
  (h_epkBlinder : Converts F.conversion    state commit.epkBlinder epkBlinder_val)
  (h_expDate    : Converts F.conversion    state commit.expDate expDate_val)
  :
  ConvertsM FUnit.conversion (verifyNonce nonce commit) state ()
    ( asciiDigitsToScalar.value nonceValues_vals nonceLen_val.val =
        H #v[ epk_vals[0], epk_vals[1], epk_vals[2], epkLen_val, expDate_val, epkBlinder_val ]
        ∧
      (∀ i : Fin MAX_NONCE_VALUE_LEN,
        i.val < nonceLen_val.val →
          48 ≤ nonceValues_vals[i].val ∧ nonceValues_vals[i].val ≤ 57
      ) ∧
      0 < nonceLen_val.val ∧
      nonceLen_val.val ≤ MAX_NONCE_VALUE_LEN - 1 ∧
      ∀ i : Fin MAX_NONCE_VALUE_LEN, nonceValues_vals[i].val < 2 ^ 8
    )
:= by
  unfold verifyNonce
  have h_epk0 := FVec.converts_getElem h_epk (show (0 : ℕ) < EPK_NUM_FIELDS by decide)
  have h_epk1 := FVec.converts_getElem h_epk (show (1 : ℕ) < EPK_NUM_FIELDS by decide)
  have h_epk2 := FVec.converts_getElem h_epk (show (2 : ℕ) < EPK_NUM_FIELDS by decide)
  have h_inputVec := FVec.converts_push (FVec.converts_push (FVec.converts_push
    (FVec.converts_push (FVec.converts_push (FVec.converts_push
      FVec.converts_empty h_epk0) h_epk1) h_epk2) h_epkLen) h_expDate) h_epkBlinder
  step (h_H (by decide) (by decide) h_inputVec) as expectedNonce
  have hAsc := asciiDigitsToScalar.convertsM h_input h_len (by decide) (by decide) (by decide)
  have h_expectedNonce1 := converts_skip hAsc h_expectedNonce
  refine convertsM_of_convertsM
    (convertsM_bind_and hAsc (assert_eq.convertsM hAsc.result h_expectedNonce1)) rfl ?_
  simp only [true_implies]
  constructor
  · rintro ⟨⟨h_digits, h_len0, h_lenw, h_bytes⟩, h_eq⟩
    exact ⟨h_eq, h_digits, h_len0, by omega, h_bytes⟩
  · rintro ⟨h_eq, h_digits, h_len0, h_lenw, h_bytes⟩
    exact ⟨⟨h_digits, h_len0, by omega, h_bytes⟩, h_eq⟩

lemma convertsM_string {H : HashFn} (h_H : Computes H) {state : ClapMState bn254}
  {nonce : FString bn254 MAX_NONCE_VALUE_LEN}
  {commit : CommitmentInput bn254}
  -- Ideal values
  {nonce_val : String}
  {epk_vals : Vector (ZMod bn254) EPK_NUM_FIELDS}
  {epkLen_val epkBlinder_val expDate_val : ZMod bn254}
  -- Conversion hypotheses
  (h_iat        : Converts FString.conversion state nonce nonce_val)
  (h_epk        : Converts FVec.conversion state commit.epk epk_vals)
  (h_epkLen     : Converts F.conversion state commit.epkLen epkLen_val)
  (h_epkBlinder : Converts F.conversion state commit.epkBlinder epkBlinder_val)
  (h_expDate    : Converts F.conversion state commit.expDate expDate_val)
  -- Required
  (h_s_len : nonce_val.length ≤ MAX_NONCE_VALUE_LEN)
  (h_chars : ∀ c ∈ nonce_val.toList, c.toNat < 256)
:
  ConvertsM FUnit.conversion (verifyNonce nonce commit) state ()
    ( asciiDigitsToScalar.value (encodeV MAX_NONCE_VALUE_LEN nonce_val) nonce_val.length =
        H #v[ epk_vals[0], epk_vals[1], epk_vals[2], epkLen_val, expDate_val, epkBlinder_val ]
        ∧
      (∀ c ∈ nonce_val.toList, 48 ≤ c.toNat ∧ c.toNat ≤ 57) ∧
      0 < nonce_val.length ∧ nonce_val.length < MAX_NONCE_VALUE_LEN
    )
:= by
  unfold verifyNonce
  have h_epk0 := FVec.converts_getElem h_epk (show (0 : ℕ) < EPK_NUM_FIELDS by decide)
  have h_epk1 := FVec.converts_getElem h_epk (show (1 : ℕ) < EPK_NUM_FIELDS by decide)
  have h_epk2 := FVec.converts_getElem h_epk (show (2 : ℕ) < EPK_NUM_FIELDS by decide)
  have h_inputVec := FVec.converts_push (FVec.converts_push (FVec.converts_push
    (FVec.converts_push (FVec.converts_push (FVec.converts_push
      FVec.converts_empty h_epk0) h_epk1) h_epk2) h_epkLen) h_expDate) h_epkBlinder
  step (h_H (by decide) (by decide) h_inputVec) as expectedNonce
  have hAsc := asciiDigitsToScalar.convertsM_string h_iat h_s_len h_chars (by decide) (by decide)
    (by decide)
  have h_expectedNonce1 := converts_skip hAsc h_expectedNonce
  refine convertsM_of_convertsM
    (convertsM_bind_and hAsc (assert_eq.convertsM hAsc.result h_expectedNonce1)) rfl ?_
  simp only [true_implies]
  have h_max : MAX_NONCE_VALUE_LEN = 100 := rfl
  by_cases hc : 0 < nonce_val.length ∧ nonce_val.length ≤ 99 ∧
      (∀ c ∈ nonce_val.toList, 48 ≤ c.toNat ∧ c.toNat ≤ 57)
  · rw [if_pos hc]
    have hv := asciiDigitsToScalar.value_encodeV (p := bn254) hc.1 hc.2.1 hc.2.2
    constructor
    · rintro ⟨-, h_eq⟩
      exact ⟨hv.trans h_eq, hc.2.2, hc.1, by omega⟩
    · rintro ⟨h_eq, -, -, -⟩
      exact ⟨hc, hv.symm.trans h_eq⟩
  · rw [if_neg hc]
    constructor
    · rintro ⟨hc', -⟩
      exact absurd hc' hc
    · rintro ⟨-, h_digits, h_len0, h_lenw⟩
      exact absurd ⟨h_len0, by omega, h_digits⟩ hc

end verifyNonce
