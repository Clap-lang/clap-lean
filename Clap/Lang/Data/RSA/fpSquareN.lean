import Clap.Lang.Core.Combinators.foldlM
import Clap.Lang.Gate.fpmul

/-! `n` successive `fpmul` squarings of a bignum, `base ^ 2 ^ n mod modulus`.
It is the `doublers` chain of Circom's `FpPow65537Mod(N, K)`
-/

namespace Clap.Lang.RSA

variable {p : ℕ}

/-- `n` successive modular squarings of `base`, `base ^ 2 ^ n mod modulus`, on `k` limbs of `w`
bits. Satisfiable exactly when the limbs of `base` and `modulus` are below `2^w` and `modulus` is
nonzero. -/
def fpSquareN (w k n : ℕ) [NeZero n] (base modulus : FVec p k) : ClapM p (FVec p k) := do
  -- Circom: doublers[0].a[j] <== base[j]; doublers[0].b[j] <== base[j];
  let d0 ← fpmul w k base base modulus
  -- Circom: doublers[i + 1].a[j] <== doublers[i].out[j]; doublers[i + 1].b[j] <== doublers[i].out[j];
  (Vector.replicate (n - 1) modulus).foldlM (fun acc m ↦ fpmul w k acc acc m) d0

namespace fpSquareN

/-- One squaring on the number an accumulator's limbs encode. -/
def square (p w k M r : ℕ) : ℕ :=
  limbsToNat w (natToLimbs (p := p) w k r) * limbsToNat w (natToLimbs (p := p) w k r) % M

def raw (p w k n M X : ℕ) : ℕ := (square p w k M)^[n - 1] (X * X % M)

lemma foldl_replicate {α β : Type} {j : ℕ} {x : α} {f : β → α → β} {init : β} :
  (Vector.replicate j x).foldl f init = (fun r ↦ f r x)^[j] init
:= by
  rw [← Vector.foldl_toList, Vector.toList_replicate]
  induction j generalizing init with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, List.foldl_cons, ih, Function.iterate_succ_apply]

private lemma square_eq {w k M r : ℕ} (hp : 2 ^ w ≤ p) :
  square p w k M r = (r % 2 ^ (w * k)) * (r % 2 ^ (w * k)) % M
:= by
  rw [square, limbsToNat_natToLimbs hp]

/-- With a nonzero modulus below `2^(w*k)` the squarings are exact. -/
lemma raw_eq {w k n M X : ℕ} [NeZero n] (hp : 2 ^ w ≤ p) (hM : 0 < M) (hMN : M < 2 ^ (w * k)) :
  raw p w k n M X = X ^ 2 ^ n % M
:= by
  have key : ∀ j, (square p w k M)^[j] (X * X % M) = X ^ 2 ^ (j + 1) % M := by
    intro j
    induction j with
    | zero => simp [pow_two]
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, square_eq hp,
        Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ hM) hMN), ← Nat.mul_mod, ← pow_two, ← pow_mul,
        ← pow_succ]
  rw [raw, key, Nat.sub_add_cancel (Nat.pos_of_neZero n)]

/-- For any modulus below `2^(w*k)`, zero included, the squarings agree with `X ^ 2 ^ n % M` on
the limbs. -/
lemma raw_mod {w k n M X : ℕ} [NeZero n] (hp : 2 ^ w ≤ p) (hMN : M < 2 ^ (w * k)) :
  raw p w k n M X % 2 ^ (w * k) = X ^ 2 ^ n % M % 2 ^ (w * k)
:= by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have key : ∀ j, (square p w k 0)^[j] (X * X % 0) % 2 ^ (w * k) =
        X ^ 2 ^ (j + 1) % 2 ^ (w * k) := by
      intro j
      induction j with
      | zero => simp [pow_two]
      | succ j ih =>
        rw [Function.iterate_succ_apply', square_eq hp, Nat.mod_zero, ih, ← Nat.mul_mod,
          ← pow_two, ← pow_mul, ← pow_succ]
    rw [raw, key, Nat.sub_add_cancel (Nat.pos_of_neZero n), Nat.mod_zero]
  · rw [raw_eq hp hM hMN]

variable {w k n : ℕ} {state : ClapMState p} {base modulus : FVec p k}
  {base_vals mod_vals : Vector (ZMod p) k}

/-- One step of the fold: squaring an accumulator whose limbs are in range asserts only the
modulus' range and that it is nonzero. -/
private lemma step_convertsM
  {state' : ClapMState p} {acc m : FVec p k} {r : ℕ} {m_vals : Vector (ZMod p) k}
  (h_acc : Converts (Limbs.conversion w k) state' acc r)
  (h_m : Converts FVec.conversion state' m m_vals)
:
  ConvertsM (Limbs.conversion w k) (fpmul w k acc acc m) state'
    (square p w k (limbsToNat w m_vals.toList) r)
    ((∀ i : Fin k, m_vals[i].val < 2 ^ w) ∧ 0 < limbsToNat w m_vals.toList)
:= by
  refine convertsM_of_convertsM
    (fpmul.convertsM (Limbs.converts_FVec h_acc) (Limbs.converts_FVec h_acc) h_m)
    (by simp [square]) ?_
  simp

lemma convertsM_unchecked [NeZero n]
  (h_base : Converts FVec.conversion state base base_vals)
  (h_modulus : Converts FVec.conversion state modulus mod_vals)
:
  ConvertsM (Limbs.conversion w k) (fpSquareN w k n base modulus) state
    (raw p w k n (limbsToNat w mod_vals.toList) (limbsToNat w base_vals.toList))
    ((∀ i : Fin k, base_vals[i].val < 2 ^ w) ∧ (∀ i : Fin k, mod_vals[i].val < 2 ^ w) ∧
      0 < limbsToNat w mod_vals.toList)
:= by
  unfold fpSquareN
  have hA := fpmul.convertsM (w := w) h_base h_base h_modulus
  have hF := convertsM_foldlM_constraints
    (C_acc := Limbs.conversion w k) (C_elem := FVec.conversion)
    (f := fun acc m ↦ fpmul w k acc acc m)
    (f_spec := fun r m_vals ↦ square p w k (limbsToNat w m_vals.toList) r)
    (step_constraints := fun m_vals ↦
      (∀ i : Fin k, m_vals[i].val < 2 ^ w) ∧ 0 < limbsToNat w m_vals.toList)
    (v := Vector.replicate (n - 1) modulus) (vals := Vector.replicate (n - 1) mod_vals)
    (fun i ↦ by simpa using converts_skip hA h_modulus) hA.result
    (fun h_acc h_m ↦ step_convertsM h_acc h_m)
  refine convertsM_of_convertsM (convertsM_bind_and hA hF) ?_ ?_
  · rw [foldl_replicate]
    rfl
  · simp only [Fin.getElem_fin, Vector.getElem_replicate]
    constructor
    · rintro ⟨⟨h_b, -, h_m, h_M⟩, -⟩
      exact ⟨h_b, h_m, h_M⟩
    · rintro ⟨h_b, h_m, h_M⟩
      exact ⟨⟨h_b, h_b, h_m, h_M⟩, fun _ ↦ ⟨h_m, h_M⟩⟩

lemma convertsM [NeZero n]
  (h_base : Converts FVec.conversion state base base_vals)
  (h_modulus : Converts FVec.conversion state modulus mod_vals)
  (h_mod_vals : ∀ i : Fin k, mod_vals[i].val < 2 ^ w)
  (hp : 2 ^ w ≤ p)
:
  ConvertsM (Limbs.conversion w k) (fpSquareN w k n base modulus) state
    (limbsToNat w base_vals.toList ^ 2 ^ n % limbsToNat w mod_vals.toList)
    ((∀ i : Fin k, base_vals[i].val < 2 ^ w) ∧ 0 < limbsToNat w mod_vals.toList)
:= by
  refine Limbs.convertsM_congr (raw_mod hp (limbsToNat_toList_lt h_mod_vals))
    (convertsM_of_convertsM (convertsM_unchecked h_base h_modulus) rfl ?_)
  exact ⟨fun ⟨h_b, _, h_M⟩ ↦ ⟨h_b, h_M⟩, fun ⟨h_b, h_M⟩ ↦ ⟨h_b, h_mod_vals, h_M⟩⟩

end fpSquareN

end Clap.Lang.RSA
