import Clap.Lang.Core.FB.assert
import Clap.Lang.Data.BigInt.bigLessThan
import Clap.Lang.Data.FArray.bits2num
import Clap.Lang.Data.Packing.assertIs64BitLimbs
import Clap.Lang.Data.Packing.bigEndianBitsToScalars
import Clap.Lang.Data.RSA.rsaPkcs1v15Verify

/-!
# `rsa2048e65537Pkcs1v15Verify`: RSA-2048 signature verification

Circom: `RSA_2048_e_65537_PKCS1_V1_5_Verify(64, 32)`. It packs the 256 SHA-256 output bits
into four limbs, range-checks the signature, asserts `signature < modulus` (`BigLessThan`), and
runs the encoded-message check `rsaPkcs1v15Verify`.

`convertsM` states it, given 64-bit signature and modulus limbs, as

    s < n  ∧  s ^ 65537 mod n = PKCS1.em256 h,

with `s` and `n` the numbers the limbs encode and `h` the digest.

* the modulus limbs are range-checked by the `fpmul` gates here. Circom's wrapper leaves that to `AssertIs64BitLimbs(pubkey_modulus)` elsewhere in `keyless`;
* the message bits are taken to be bits (`FArray.conversion`), as the SHA-256 circuit produces them, but we don't check it here.
* nothing checks that the modulus really has 256 octets.

Unlike Circom, `fpmul` returns the canonical remainder, so this circuit accepts only when
`s ^ 65537 mod n` is the encoded message, where Circom accepts any `s ^ 65537` congruent to it
modulo `n`. The two agree for every modulus above the encoded message (every `n ≥ 2^2033`)
-/

namespace Clap.Lang.RSA

variable {p : ℕ}

/-- Verify the RSA-2048, `e = 65537`, PKCS#1 v1.5 signature `signature` (32 limbs of 64 bits,
least significant first) under the modulus `pubkey_modulus` (the same) on the SHA-256 digest
`message_bits` (256 bits, most significant first). -/
def rsa2048e65537Pkcs1v15Verify [p.AtLeastTwo] (signature pubkey_modulus : FVec p 32) (message_bits : FArray p 256) : ClapM p Unit := do
  -- Circom: signal message_limbs[4] <== BigEndianBitsToScalars(256, SIGNATURE_LIMB_BIT_WIDTH)(message_bits);
  let message_limbs ← Packing.bigEndianBitsToScalars (w := 4) 64 message_bits
  -- Circom: AssertIs64BitLimbs(SIGNATURE_NUM_LIMBS)(signature);
  Packing.assertIs64BitLimbs signature
  -- Circom: signal sig_ok <== BigLessThan(252, SIGNATURE_NUM_LIMBS)(signature, pubkey_modulus);
  let sig_ok ← BigInt.bigLessThan 252 signature pubkey_modulus
  -- Circom: sig_ok === 1;
  assert sig_ok
  -- Circom: message_limbs_le[i] = message_limbs[3 - i];
  -- Circom: RSA_PKCS1_v1_5_Verify(SIGNATURE_LIMB_BIT_WIDTH, SIGNATURE_NUM_LIMBS)(signature, pubkey_modulus, message_limbs_le);
  rsaPkcs1v15Verify signature pubkey_modulus message_limbs.reverse

namespace rsa2048e65537Pkcs1v15Verify

/-- `BitVec.ofBoolListLE` reads its list least significant bit first. -/
private lemma toNat_ofBoolListLE (l : List Bool) :
  (BitVec.ofBoolListLE l).toNat = Nat.ofDigits 2 (l.map Bool.toNat)
:= by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [BitVec.ofBoolListLE, BitVec.toNat_concat, List.map_cons, Nat.ofDigits_cons, ih]
    cases b <;> simp <;> ring

/-- The digest limbs `BigEndianBitsToScalars` produces, least significant first. -/
private def hashedVals (p : ℕ) (msg_vals : Vector Bool 256) : Vector (ZMod p) 4 :=
  ((toChunks (w := 4) 64 msg_vals).map fun c ↦ FArray.toNum (p := p) c.reverse).reverse

/-- The digest limbs are in range, and spell the integer of the digest. -/
private lemma hashedVals_spec {msg_vals : Vector Bool 256} (hp : 2 ^ 64 ≤ p) :
  (∀ i : Fin 4, (hashedVals p msg_vals)[i].val < 2 ^ 64) ∧
  limbsToNat 64 (hashedVals p msg_vals).toList = PKCS1.ofBitsBE msg_vals.toList
:= by
  -- a chunk, read big-endian, as a field element
  have h_chunk : ∀ c : Vector Bool 64,
      (FArray.toNum (p := p) c.reverse).val = PKCS1.ofBitsBE c.toList := by
    intro c
    have h_lt : PKCS1.ofBitsBE c.toList < 2 ^ 64 := by simpa using PKCS1.ofBitsBE_lt c.toList
    rw [FArray.toNum_eq_ofBoolListLE, Vector.toList_reverse, toNat_ofBoolListLE,
      ← PKCS1.ofBitsBE.eq_1, ZMod.val_natCast_of_lt (lt_of_lt_of_le h_lt hp)]
  constructor
  · intro i
    simp only [hashedVals, Fin.getElem_fin, Vector.getElem_reverse, Vector.getElem_map, h_chunk]
    exact lt_of_lt_of_eq (PKCS1.ofBitsBE_lt _) (by simp)
  · conv_rhs => rw [← PKCS1.flatten_toChunks (w := 4) (size := 64) msg_vals, PKCS1.toList_flatten]
    rw [PKCS1.ofBitsBE_flatten (m := 64) _ (by
      intro c hc
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hc
      simp)]
    rw [limbsToNat_eq_ofDigits, hashedVals, Vector.toList_reverse, Vector.toList_map,
      List.map_reverse, List.map_map, List.map_reverse, List.map_map]
    congr 2
    exact List.map_congr_left fun c _ ↦ h_chunk c

variable {state : ClapMState p} {signature pubkey_modulus : FVec p 32}
  {message_bits : FArray p 256} {sig_vals mod_vals : Vector (ZMod p) 32}
  {msg_vals : Vector Bool 256}

lemma convertsM [p.AtLeastTwo]
  (h_signature : Converts FVec.conversion state signature sig_vals)
  (h_modulus : Converts FVec.conversion state pubkey_modulus mod_vals)
  (h_message : Converts FArray.conversion state message_bits msg_vals)
  (hp : 2 ^ 253 < p)
:
  ConvertsM FUnit.conversion (rsa2048e65537Pkcs1v15Verify signature pubkey_modulus message_bits)
    state ()
    ((∀ i : Fin 32, sig_vals[i].val < 2 ^ 64) ∧ (∀ i : Fin 32, mod_vals[i].val < 2 ^ 64) ∧
     limbsToNat 64 sig_vals.toList < limbsToNat 64 mod_vals.toList ∧
     limbsToNat 64 sig_vals.toList ^ 65537 % limbsToNat 64 mod_vals.toList = PKCS1.em256 (PKCS1.ofBitsBE msg_vals.toList))
:= by
  have hp64 : 2 ^ 64 < p := lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hp
  unfold rsa2048e65537Pkcs1v15Verify
  -- the four digest limbs: no assertion
  have h1 := Packing.bigEndianBitsToScalars.convertsM (w := 4) (bitsPerScalar := 64) h_message
  -- the signature's range check
  have h2 := Packing.assertIs64BitLimbs.convertsM (converts_skip h1 h_signature)
  -- `signature < pubkey_modulus`, at any input: the modulus range is only asserted later
  have h3 := BigInt.bigLessThan.convertsM_unchecked (n := 252)
    (converts_skip h2 (converts_skip h1 h_signature)) (converts_skip h2 (converts_skip h1 h_modulus))
  have h4 := assert.convertsM h3.result
  have h5 := rsaPkcs1v15Verify.convertsM
    (converts_skip h4 (converts_skip h3 (converts_skip h2 (converts_skip h1 h_signature))))
    (converts_skip h4 (converts_skip h3 (converts_skip h2 (converts_skip h1 h_modulus))))
    (converts_skip h4 (converts_skip h3 (converts_skip h2 (FVec.converts_reverse h1.result)))) hp64
  refine convertsM_of_convertsM
    (convertsM_bind_and h1 (convertsM_bind_and h2 (convertsM_bind_and h3 (convertsM_bind_and h4 h5))))
    rfl ?_
  -- what is left is arithmetic on the ideal values
  clear h1 h2 h3 h4 h5 h_signature h_modulus h_message
  obtain ⟨h_hashed_range, h_hashed⟩ := hashedVals_spec (p := p) (msg_vals := msg_vals) hp64.le
  rw [show ((toChunks 64 msg_vals).map fun c ↦ FArray.toNum (p := p) c.reverse).reverse =
    hashedVals p msg_vals from rfl, h_hashed]
  have h_n : 2 ^ (252 + 1) < p := hp
  constructor
  · rintro ⟨-, h_s, h_ok, h_lt, -, h_m, -, h_M, h_R⟩
    rw [BigInt.bigLessThan.raw_eq (w := 64) h_s h_m (by norm_num) h_n] at h_lt
    exact ⟨h_s, h_m, by simpa using h_lt, h_R⟩
  · rintro ⟨h_s, h_m, h_lt, h_R⟩
    refine ⟨trivial, h_s, BigInt.bigLessThan.ok_of h_s h_m (by norm_num) h_n, ?_,
      h_s, h_m, h_hashed_range, lt_of_le_of_lt (Nat.zero_le _) h_lt, h_R⟩
    rw [BigInt.bigLessThan.raw_eq (w := 64) h_s h_m (by norm_num) h_n]
    simpa using h_lt

end rsa2048e65537Pkcs1v15Verify

end Clap.Lang.RSA
