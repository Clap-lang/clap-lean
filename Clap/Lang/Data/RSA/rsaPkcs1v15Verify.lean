import Clap.Lang.Core.Combinators.ofFnM
import Clap.Lang.Core.F.mkF
import Clap.Lang.Data.FVec.assert_eq
import Clap.Lang.Data.RSA.fpPow65537Mod
import Clap.Lang.Data.RSA.PKCS1

/-!
# `rsaPkcs1v15Verify`: RSA-2048 / SHA-256 encoded-message check

Circom: `RSA_PKCS1_v1_5_Verify(64, 32)`. It raises the signature to `65537` modulo
the public modulus and checks the result is the EMSA-PKCS1-v1_5 encoding of the SHA-256 digest
`hashed`. Its four low limbs are the digest and its 28 high limbs are fixed (`emLimbs`).

`convertsM` states that as `s ^ 65537 % n = PKCS1.em256 h`, with `s`, `n` and `h` the numbers the
limbs encode. This template does not check `s < n`, which RSAVP1 requires. The keyless
wrapper `rsa2048e65537Pkcs1v15Verify` adds it with `BigLessThan`.

Two deviations from Circom:

* `pm.out[6]` is compared with one equality instead of a `Num2Bits(64)` and 64 bit checks (documented at `emLimbs`).
* `fpmul` returns the canonical remainder (`r < n`, enforced by the gate's `check_lt`), while
  Circom's `FpMul` only checks `a · b = n · q + r` with `q`, `r` below `2^2048`. So Circom accepts
  whenever `s ^ 65537 ≡ EM (mod n)`, and this circuit only when `s ^ 65537 mod n = EM`. The two
  agree whenever `EM < n`, that is for every modulus above `PKCS1.em256 h` (every `n ≥ 2^2033`,
  so every RSA-2048 key). Below that Circom alone accepts, without any private key: with the
  digest `PKCS1.exampleH`, `n = 7` and `s = 4` satisfy every Circom constraint. Keyless is not
  exposed, since its modulus is the issuer's key, bound through the public-inputs hash.
-/

namespace Clap.Lang.RSA

variable {p : ℕ}

/-- The values the 28 high limbs `pm.out[4..31]` of `s ^ 65537 mod n`.

One difference from Circom, in limb 6: Circom compares limbs 4, 5 and 7–31 with their
constant directly, but checks limb 6 bit by bit:
- it splits `pm.out[6]` into its 64 bits (`Num2Bits(64)`);
- it requires the low 32 bits to spell `0x00303130` (`REMAINS_BITS`);
- it requires the high 32 bits to be all ones.

Here limb 6 is compared directly too, with the number: `0xFFFFFFFF00303130`.
Both accept exactly the same values. Fixing every bit of a 64-bit number fixes the number, and
`pm.out[6]` is below `2^64` anyway, since `fpmul` range-checks its output limbs. The direct
comparison is one constraint instead of about 129, with no extra bit signals. -/
def emLimbs : Vector ℕ 28 :=
  -- Circom: pm.out[4] === 217300885422736416;
  -- Circom: pm.out[5] === 938447882527703397;
  -- Circom: num2bits_6.in <== pm.out[6]; num2bits_6.out[i] === REMAINS_BITS[31 - i] (i < 32),
  -- Circom: num2bits_6.out[i] === 1 (32 ≤ i < 64).
  -- Here: pm.out[6] === 0xFFFFFFFF00303130, one comparison for the same 64 bits (see above).
  #v[217300885422736416, 938447882527703397, 0xFFFFFFFF00303130] ++
  -- Circom: for (var i = 7; i < 31; i++) { pm.out[i] === 18446744073709551615; }
  Vector.replicate 24 18446744073709551615 ++
  -- Circom: pm.out[31] === 562949953421311;
  #v[562949953421311]

lemma toList_emLimbs : emLimbs.toList = PKCS1.em256Limbs := by decide +kernel

/-- RSA PKCS#1 v1.5 / SHA-256 check of the signature `sign` against the modulus `modulus` and the
digest `hashed`. Does not check `sign < modulus`. -/
def rsaPkcs1v15Verify (sign modulus : FVec p 32) (hashed : FVec p 4) : ClapM p Unit := do
  -- Circom: component pm = FpPow65537Mod(LIMB_BIT_WIDTH, NUM_LIMBS);
  -- Circom: pm.base[i] <== sign[i]; pm.modulus[i] <== modulus[i];
  let pm ← fpPow65537Mod 64 32 sign modulus
  -- Circom: the constants of `pm.out[4..31] === …` below.
  let em ← Vector.ofFnM fun i : Fin 28 ↦ mkF (emLimbs[i] : ZMod p)
  -- Circom: hashed[i] === pm.out[i]; (i < 4), then pm.out[4..31] === emLimbs.
  FVec.assert_eq pm (hashed ++ em)

namespace rsaPkcs1v15Verify

variable {state : ClapMState p} {sign modulus : FVec p 32} {hashed : FVec p 4}
  {sign_vals mod_vals : Vector (ZMod p) 32} {hashed_vals : Vector (ZMod p) 4}

/- `s ^ 65537 % n = PKCS1.em256 h` -/
lemma convertsM [p.AtLeastTwo]
  (h_sign : Converts FVec.conversion state sign sign_vals)
  (h_modulus : Converts FVec.conversion state modulus mod_vals)
  (h_hashed : Converts FVec.conversion state hashed hashed_vals)
  (hp : 2 ^ 64 < p)
:
  ConvertsM FUnit.conversion (rsaPkcs1v15Verify sign modulus hashed) state ()
    ((∀ i : Fin 32, sign_vals[i].val < 2 ^ 64) ∧ (∀ i : Fin 32, mod_vals[i].val < 2 ^ 64) ∧
     (∀ i : Fin 4, hashed_vals[i].val < 2 ^ 64) ∧ 0 < limbsToNat 64 mod_vals.toList ∧
     limbsToNat 64 sign_vals.toList ^ 65537 % limbsToNat 64 mod_vals.toList = PKCS1.em256 (limbsToNat 64 hashed_vals.toList))
:= by
  unfold rsaPkcs1v15Verify
  have hA := fpPow65537Mod.convertsM_unchecked (w := 64) (k := 32) h_sign h_modulus
  refine convertsM_of_convertsM (convertsM_bind_and (constraints2 :=
      natToLimbsV p 64 32
          (fpPow65537Mod.raw p 64 32 (limbsToNat 64 mod_vals.toList) (limbsToNat 64 sign_vals.toList)) =
        hashed_vals ++ emLimbs.map (fun c : ℕ ↦ (c : ZMod p))) hA ?rest) rfl ?iff
  case rest =>
    have h_pm := Limbs.converts_FVec hA.result
    have h_hashed' := converts_skip hA h_hashed
    clear h_sign h_modulus h_hashed
    step (convertsM_ofFnM (vals := emLimbs.map (fun c : ℕ ↦ (c : ZMod p)))
      (fun i _ ↦ by simpa using mkF.convertsM)) as em
    exact convertsM_of_convertsM (FVec.assert_eq.convertsM h_pm (FVec.converts_append h_hashed' h_em))
      rfl (true_imp_iff.symm)
  case iff =>
    have hp' : 2 ^ 64 ≤ p := hp.le
    have h_vals : ∀ R, natToLimbsV p 64 32 R = hashed_vals ++ emLimbs.map (fun c : ℕ ↦ (c : ZMod p)) ↔
        natToLimbs (p := p) 64 32 R =
          hashed_vals.toList ++ PKCS1.em256Limbs.map (Nat.cast : ℕ → ZMod p) := by
      intro R
      rw [← Vector.toList_inj, toList_natToLimbsV, Vector.toList_append, Vector.toList_map,
        toList_emLimbs]
    have h_hashed_range : (∀ x ∈ hashed_vals.toList, x.val < 2 ^ 64) ↔
        ∀ i : Fin 4, hashed_vals[i].val < 2 ^ 64 := by
      constructor
      · intro h i
        exact h _ (by simp)
      · intro h x hx
        obtain ⟨i, h_i, rfl⟩ := List.getElem_of_mem hx
        simpa using h ⟨i, by simpa using h_i⟩
    constructor
    · rintro ⟨⟨h_s, h_m, h_M⟩, h_eq⟩
      have hMN := limbsToNat_toList_lt h_m
      rw [fpPow65537Mod.raw_eq hp' h_M hMN, h_vals,
        PKCS1.natToLimbs_eq_em256_iff (by simp) (lt_trans (Nat.mod_lt _ h_M) hMN) hp',
        h_hashed_range] at h_eq
      exact ⟨h_s, h_m, h_eq.1, h_M, h_eq.2⟩
    · rintro ⟨h_s, h_m, h_h, h_M, h_R⟩
      have hMN := limbsToNat_toList_lt h_m
      refine ⟨⟨h_s, h_m, h_M⟩, ?_⟩
      rw [fpPow65537Mod.raw_eq hp' h_M hMN, h_vals,
        PKCS1.natToLimbs_eq_em256_iff (by simp) (lt_trans (Nat.mod_lt _ h_M) hMN) hp',
        h_hashed_range]
      exact ⟨h_h, h_R⟩

end rsaPkcs1v15Verify

section examples

private def evalPm (s n : ℕ) : Option (Vector (ZMod Primes.bn254) 32) :=
  let cmd : ClapM Primes.bn254 (HashConsSt Primes.bn254 × FVec Primes.bn254 32) := do
    let s ← (natToLimbsV Primes.bn254 64 32 s).mapM
      (fun x ↦ liftM (HashConsM.mkConstant (p := Primes.bn254) x))
    let n ← (natToLimbsV Primes.bn254 64 32 n).mapM
      (fun x ↦ liftM (HashConsM.mkConstant (p := Primes.bn254) x))
    let r ← fpPow65537Mod 64 32 s n
    let σ ← getThe (HashConsSt Primes.bn254)
    return (σ, r)
  let Γ := cmd.getVarStore {} 0 {}
  let r := (cmd.run 0 {}).1.1.1
  r.2.mapM fun e ↦ [Γ, r.1|e]

example : evalPm PKCS1.exampleS PKCS1.exampleN =
    some (natToLimbsV Primes.bn254 64 32 (PKCS1.em256 PKCS1.exampleH)) := by
  native_decide

example : (natToLimbsV Primes.bn254 64 32 (PKCS1.em256 PKCS1.exampleH)).toList.drop 4 =
    emLimbs.toList.map (Nat.cast : ℕ → ZMod Primes.bn254) := by
  native_decide

end examples

end Clap.Lang.RSA
