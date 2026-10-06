import Clap.Lang.Data.RSA.fpSquareN

/-! `base ^ 65537 mod modulus` on bignums -/

namespace Clap.Lang.RSA

variable {p : ℕ}

/-- `base ^ 65537 mod modulus` on `k` limbs of `w` bits. Satisfiable exactly when the limbs of
`base` and `modulus` are below `2^w` and `modulus` is nonzero. -/
def fpPow65537Mod (w k : ℕ) (base modulus : FVec p k) : ClapM p (FVec p k) := do
  -- Circom: doublers[0].a/b[j] <== base[j]; doublers[i + 1].a/b[j] <== doublers[i].out[j];
  let d15 ← fpSquareN w k 16 base modulus
  -- Circom: adder.a[j] <== base[j]; adder.b[j] <== doublers[15].out[j]; out[j] <== adder.out[j];
  fpmul w k base d15 modulus

namespace fpPow65537Mod

/-- What the 17 gates compute for any modulus `M`, from `X`. -/
def raw (p w k M X : ℕ) : ℕ :=
  X * limbsToNat w (natToLimbs (p := p) w k (fpSquareN.raw p w k 16 M X)) % M

/-- With a nonzero modulus below `2^(w*k)` the exponentiation is exact. -/
lemma raw_eq {w k M X : ℕ} (hp : 2 ^ w ≤ p) (hM : 0 < M) (hMN : M < 2 ^ (w * k)) :
  raw p w k M X = X ^ 65537 % M
:= by
  rw [raw, limbsToNat_natToLimbs hp, fpSquareN.raw_eq hp hM hMN,
    Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ hM) hMN), Nat.mul_mod_mod, ← pow_succ']
  rfl

/-- For any modulus below `2^(w*k)`, zero included, the result agrees with `X ^ 65537 % M` on the
limbs. -/
lemma raw_mod {w k M X : ℕ} (hp : 2 ^ w ≤ p) (hMN : M < 2 ^ (w * k)) :
  raw p w k M X % 2 ^ (w * k) = X ^ 65537 % M % 2 ^ (w * k)
:= by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have h16 := fpSquareN.raw_mod (p := p) (n := 16) (X := X) hp hMN
    rw [Nat.mod_zero] at h16
    rw [raw, limbsToNat_natToLimbs hp, Nat.mod_zero, Nat.mod_zero, h16, Nat.mul_mod_mod,
      ← pow_succ']
    rfl
  · rw [raw_eq hp hM hMN]

variable {w k : ℕ} {state : ClapMState p} {base modulus : FVec p k}
  {base_vals mod_vals : Vector (ZMod p) k}

lemma convertsM_unchecked
  (h_base : Converts FVec.conversion state base base_vals)
  (h_modulus : Converts FVec.conversion state modulus mod_vals)
:
  ConvertsM (Limbs.conversion w k) (fpPow65537Mod w k base modulus) state
    (raw p w k (limbsToNat w mod_vals.toList) (limbsToNat w base_vals.toList))
    ((∀ i : Fin k, base_vals[i].val < 2 ^ w) ∧ (∀ i : Fin k, mod_vals[i].val < 2 ^ w) ∧
      0 < limbsToNat w mod_vals.toList)
:= by
  unfold fpPow65537Mod
  have hA := fpSquareN.convertsM_unchecked (w := w) (n := 16) h_base h_modulus
  have hB := fpmul.convertsM (w := w) (converts_skip hA h_base) (Limbs.converts_FVec hA.result)
    (converts_skip hA h_modulus)
  refine convertsM_of_convertsM (convertsM_bind_and hA hB) (by simp [raw]) ?_
  constructor
  · rintro ⟨h, -⟩
    exact h
  · rintro ⟨h_b, h_m, h_M⟩
    exact ⟨⟨h_b, h_m, h_M⟩, h_b, fun i ↦ val_natToLimbsV_lt i.isLt, h_m, h_M⟩

lemma convertsM
  (h_base : Converts FVec.conversion state base base_vals)
  (h_modulus : Converts FVec.conversion state modulus mod_vals)
  (h_mod_vals : ∀ i : Fin k, mod_vals[i].val < 2 ^ w)
  (hp : 2 ^ w ≤ p)
:
  ConvertsM (Limbs.conversion w k) (fpPow65537Mod w k base modulus) state
    (limbsToNat w base_vals.toList ^ 65537 % limbsToNat w mod_vals.toList)
    ((∀ i : Fin k, base_vals[i].val < 2 ^ w) ∧ 0 < limbsToNat w mod_vals.toList)
:= by
  refine Limbs.convertsM_congr (raw_mod hp (limbsToNat_toList_lt h_mod_vals))
    (convertsM_of_convertsM (convertsM_unchecked h_base h_modulus) rfl ?_)
  exact ⟨fun ⟨h_b, _, h_M⟩ ↦ ⟨h_b, h_M⟩, fun ⟨h_b, h_M⟩ ↦ ⟨h_b, h_mod_vals, h_M⟩⟩

end fpPow65537Mod

section examples

private def evalFpPow {k : ℕ} (q w : ℕ) (a m : Vector (ZMod q) k) : Option (Vector (ZMod q) k) :=
  let cmd : ClapM q (HashConsSt q × FVec q k) := do
    let a ← a.mapM (fun x ↦ liftM (HashConsM.mkConstant (p := q) x))
    let m ← m.mapM (fun x ↦ liftM (HashConsM.mkConstant (p := q) x))
    let r ← fpPow65537Mod w k a m
    let σ ← getThe (HashConsSt q)
    return (σ, r)
  let Γ := cmd.getVarStore {} 0 {}
  let r := (cmd.run 0 {}).1.1.1
  r.2.mapM fun e ↦ [Γ, r.1|e]

-- 2^65537 mod (2^31 - 1): ord(2) = 31 and 65537 ≡ 3 (mod 31), so 2^3
example : evalFpPow Primes.babybear 16 #v[2, 0] #v[2^16 - 1, 2^15 - 1] = some #v[8, 0] := by
  native_decide
-- 3^65537 mod (2^31 - 1) = 2120727063 = 47639 + 32359·2^16
example : evalFpPow Primes.babybear 16 #v[3, 0] #v[2^16 - 1, 2^15 - 1] = some #v[47639, 32359] := by
  native_decide
-- (m - 1)^65537 ≡ m - 1 (mod m), as (m - 1)^2 ≡ 1 and 65537 is odd; m = 2^32 - 1
example : evalFpPow Primes.babybear 16 #v[2^16 - 2, 2^16 - 1] #v[2^16 - 1, 2^16 - 1] =
    some #v[2^16 - 2, 2^16 - 1] := by native_decide
-- 2^65537 mod (2^63 - 1): ord(2) = 63 and 65537 ≡ 17 (mod 63), so 2^17 = [0, 2, 0, 0]
example : evalFpPow Primes.babybear 16 #v[2, 0, 0, 0] #v[2^16 - 1, 2^16 - 1, 2^16 - 1, 2^15 - 1] =
    some #v[0, 2, 0, 0] := by native_decide

end examples

end Clap.Lang.RSA
