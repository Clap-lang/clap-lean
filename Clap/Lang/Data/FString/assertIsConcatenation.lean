import Clap.Lang.Core.Combinators.foldlM
import Clap.Lang.Core.FUnit.assert_eq
import Clap.Lang.Data.FArray.rightArraySelector
import Clap.Lang.Gate.eq0
import Clap.Lang.Data.FString.isSubstring

namespace Clap.Lang.FString

open Poseidon RandomOracle Primes FiatShamir

variable {p : ℕ}

section check

/-- `left` is zero after `left.len`. Circom enforces this explicitly because otherwise the start
of `right` could sit at the end of `left` and still pass the polynomial check. -/
def assertIsConcatenation.padding [p.AtLeastTwo] {nL : ℕ} (left : FString p nL) :
    ClapM p Unit := do
  let one ← mkF 1
  let lm1 ← left.len - one
  let sel ← rightArraySelector nL lm1
  (sel.zip left.data).foldlM (fun _ sx ↦ do
    let prod ← sx.1 * sx.2
    eq0 prod) ()

/-- `full(α) = left(α) + α^left_len · right(α)`, given the challenge powers. `SelectArrayValue` gives `α^left_len`, and asserts `left_len < nF`. -/
def assertIsConcatenation.identity [p.AtLeastTwo] {nF nL nR : ℕ} (hL : nL ≤ nF) (hR : nR ≤ nF)
    (full : FVec p nF) (left : FString p nL) (right : FVec p nR) (pows : FVec p nF) :
    ClapM p Unit := do
  let leftEval ← dotProduct left.data ((pows.extract 0 nL).cast (by omega))
  let rightEval ← dotProduct right ((pows.extract 0 nR).cast (by omega))
  let fullEval ← dotProduct full pows
  let dv ← selectArrayValue nF pows left.len
  let prod ← dv * rightEval
  let rhs ← leftEval + prod
  assert_eq fullEval rhs

namespace assertIsConcatenation

private lemma dot_prefix_eq_evalAt {k nF : ℕ} (h : k ≤ nF) (a : Vector (ZMod p) k) (α : ZMod p) :
    (a.zip (Vector.cast (show min k nF - 0 = k by omega)
      ((Vector.ofFn fun i : Fin nF ↦ α ^ i.val).extract 0 k))).foldl
        (fun acc xy ↦ acc + xy.1 * xy.2) 0 = evalAt a α := by
  rw [dotProduct.foldl_eq_sum, zero_add, evalAt]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.getElem_fin, Vector.getElem_cast]
  rw [Vector.getElem_extract]
  simp

private lemma padding_step_convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {sx : F p × F p}
  {sx_val : ZMod p × ZMod p}
  (h_sx : Converts FPair.conversion state sx sx_val)
:
  ConvertsM FUnit.conversion (do let prod ← mkMul sx.1 sx.2; eq0 prod) state ()
    (sx_val.1 * sx_val.2 = 0)
:= by
  have h_s := FPair.converts_fst h_sx
  have h_x := FPair.converts_snd h_sx
  clear h_sx
  step mkMul.convertsM h_s h_x as prod
  apply convertsM_of_convertsM (eq0.convertsM h_prod)
  · rfl
  · simp

private lemma fold_padding_convertsM
  [p.AtLeastTwo]
  {nL : ℕ}
  {state : ClapMState p}
  {sel data : FVec p nL}
  {sel_vals data_vals : Vector (ZMod p) nL}
  (h_sel : Converts FVec.conversion state sel sel_vals)
  (h_data : Converts FVec.conversion state data data_vals)
:
  ConvertsM FUnit.conversion
    ((sel.zip data).foldlM (fun _ sx ↦ do let prod ← mkMul sx.1 sx.2; eq0 prod) ()) state ()
    (∀ i : Fin nL, sel_vals[i] * data_vals[i] = 0)
:= by
  apply convertsM_of_convertsM
    (convertsM_foldlM_constraints (C_acc := FUnit.conversion) (init_val := ())
      (f_spec := fun _ _ ↦ ()) (step_constraints := fun sx : ZMod p × ZMod p ↦ sx.1 * sx.2 = 0)
      (fun i ↦ FVec.converts_zip h_sel h_data i.isLt) FUnit.converts
      (fun _ h_sx ↦ padding_step_convertsM h_sx))
  · rfl
  · simp

private lemma bind_fold_convertsM
  [p.AtLeastTwo]
  {nL : ℕ}
  {state : ClapMState p}
  {action : ClapM p (FArray p nL)}
  {data : FVec p nL}
  {data_vals : Vector (ZMod p) nL}
  {sel_vals : Vector Bool nL}
  {C_sel : Prop}
  (h_action : ConvertsM FArray.conversion action state sel_vals C_sel)
  (h_data : Converts FVec.conversion state data data_vals)
:
  ConvertsM FUnit.conversion
    (action >>= fun sel ↦ (sel.zip data).foldlM (fun _ sx ↦ do
      let prod ← mkMul sx.1 sx.2
      eq0 prod) ()) state ()
    (C_sel ∧ ∀ i : Fin nL, (if sel_vals[i] then (1 : ZMod p) else 0) * data_vals[i] = 0)
:= by
  apply convertsM_of_convertsM (convertsM_bind_and h_action
    (fold_padding_convertsM (FVec.converts_of_FArray_converts h_action.result)
      (converts_skip h_action h_data)))
  · rfl
  · simp

lemma padding_convertsM
  [p.AtLeastTwo]
  {nL : ℕ}
  {state : ClapMState p}
  {left : FString p nL}
  {left_vals : Vector (ZMod p) nL}
  {len_val : ZMod p}
  (h_data : Converts FVec.conversion state left.data left_vals)
  (h_len : Converts F.conversion state left.len len_val)
  (h_nL : nL < p)
:
  ConvertsM FUnit.conversion (padding left) state ()
    (0 < len_val.val ∧ len_val.val ≤ nL ∧ ∀ i : Fin nL, len_val.val ≤ i.val → left_vals[i] = 0)
:= by
  unfold padding
  step mkF.convertsM as one
  step mkSub.convertsM h_len h_one as lm1
  apply convertsM_of_convertsM
    (bind_fold_convertsM (rightArraySelector.convertsM h_lm1 h_nL) h_data)
  · rfl
  · simp only [true_implies, Vector.getElem_ofFn, Fin.getElem_fin]
    have h10 : (1 : ZMod p) ≠ 0 := one_ne_zero
    -- `(len - 1).val` is `len.val - 1` when `len ≠ 0`, and `p - 1` when it is.
    by_cases h0 : len_val = 0
    · subst h0
      have hp1 : ((0 : ZMod p) - 1).val = p - 1 := by
        haveI : Fact (1 < p) := ⟨Nat.AtLeastTwo.one_lt⟩
        rw [zero_sub, ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]
      simp only [hp1, ZMod.val_zero, lt_self_iff_false, false_and, iff_false, not_and]
      intro h _
      omega
    · have h_val : (len_val - 1).val = len_val.val - 1 := by
        haveI : Fact (1 < p) := ⟨Nat.AtLeastTwo.one_lt⟩
        have h1 : (1 : ZMod p).val = 1 := ZMod.val_one p
        have hpos : 0 < len_val.val := by
          rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]; exact h0
        rw [ZMod.val_sub (by rw [h1]; omega), h1]
      have hpos : 0 < len_val.val := by
        rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]; exact h0
      rw [h_val]
      constructor
      · rintro ⟨h_lt, h_pad⟩
        refine ⟨hpos, by omega, fun i hi ↦ ?_⟩
        have := h_pad i
        simp only [show len_val.val - 1 < i.val by omega, decide_true, if_true, one_mul] at this
        exact this
      · rintro ⟨-, h_le, h_pad⟩
        refine ⟨by omega, fun i ↦ ?_⟩
        by_cases hi : len_val.val ≤ i.val
        · rw [h_pad i hi, mul_zero]
        · simp [show ¬ (len_val.val - 1 < i.val) by omega]

private lemma final_convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {fullEval leftEval rightEval dv : F p}
  {full_val left_val right_val dv_val : ZMod p}
  (h_full : Converts F.conversion state fullEval full_val)
  (h_left : Converts F.conversion state leftEval left_val)
  (h_right : Converts F.conversion state rightEval right_val)
  (h_dv : Converts F.conversion state dv dv_val)
:
  ConvertsM FUnit.conversion (do
      let prod ← dv * rightEval
      let rhs ← leftEval + prod
      assert_eq fullEval rhs) state ()
    (full_val = left_val + dv_val * right_val)
:= by
  step mkMul.convertsM h_dv h_right as prod
  step mkAdd.convertsM h_left h_prod as rhs
  apply convertsM_of_convertsM (assert_eq.convertsM h_full h_rhs)
  · rfl
  · simp

private lemma bind_final_convertsM
  [p.AtLeastTwo]
  {state : ClapMState p}
  {action : ClapM p (F p)}
  {fullEval leftEval rightEval : F p}
  {full_val left_val right_val dv_val : ZMod p}
  {C_dv : Prop}
  (h_action : ConvertsM F.conversion action state dv_val C_dv)
  (h_full : Converts F.conversion state fullEval full_val)
  (h_left : Converts F.conversion state leftEval left_val)
  (h_right : Converts F.conversion state rightEval right_val)
:
  ConvertsM FUnit.conversion (action >>= fun dv ↦ do
      let prod ← dv * rightEval
      let rhs ← leftEval + prod
      assert_eq fullEval rhs) state ()
    (C_dv ∧ full_val = left_val + dv_val * right_val)
:= convertsM_bind_and h_action
    (final_convertsM (converts_skip h_action h_full) (converts_skip h_action h_left)
      (converts_skip h_action h_right) h_action.result)

lemma identity_convertsM
  [p.AtLeastTwo]
  {nF nL nR : ℕ}
  (hL : nL ≤ nF) (hR : nR ≤ nF)
  {state : ClapMState p}
  {full : FVec p nF} {left : FString p nL} {right : FVec p nR} {pows : FVec p nF}
  {full_vals : Vector (ZMod p) nF} {left_vals : Vector (ZMod p) nL}
  {right_vals : Vector (ZMod p) nR} {len_val α : ZMod p}
  (h_full : Converts FVec.conversion state full full_vals)
  (h_data : Converts FVec.conversion state left.data left_vals)
  (h_len : Converts F.conversion state left.len len_val)
  (h_right : Converts FVec.conversion state right right_vals)
  (h_pows : Converts FVec.conversion state pows (Vector.ofFn fun i : Fin nF ↦ α ^ i.val))
  (h_nF : nF < p)
:
  ConvertsM FUnit.conversion (identity hL hR full left right pows) state ()
    (len_val.val < nF ∧ evalAt full_vals α = evalAt left_vals α + α ^ len_val.val * evalAt right_vals α)
:= by
  unfold identity
  step dotProduct.convertsM h_data (FVec.converts_vector_cast
    (FVec.converts_extract 0 nL h_pows) (show min nL nF - 0 = nL by omega)) as leftEval
  step dotProduct.convertsM h_right (FVec.converts_vector_cast
    (FVec.converts_extract 0 nR h_pows) (show min nR nF - 0 = nR by omega)) as rightEval
  step dotProduct.convertsM h_full h_pows as fullEval
  apply convertsM_of_convertsM (bind_final_convertsM
    (selectArrayValue.convertsM h_len h_pows h_nF) h_fullEval h_leftEval h_rightEval)
  · rfl
  · rw [dot_prefix_eq_evalAt hL, dot_prefix_eq_evalAt hR]
    have h_full_eval : (full_vals.zip (Vector.ofFn fun i : Fin nF ↦ α ^ i.val)).foldl
        (fun acc xy ↦ acc + xy.1 * xy.2) 0 = evalAt full_vals α := by
      rw [dotProduct.foldl_eq_sum, zero_add, evalAt]
      simp
    rw [h_full_eval]
    simp only [true_implies]
    constructor
    · rintro ⟨h_lt, h_eq⟩
      refine ⟨h_lt, ?_⟩
      simpa [h_lt, Vector.getD] using h_eq
    · rintro ⟨h_lt, h_eq⟩
      refine ⟨h_lt, ?_⟩
      simpa [h_lt, Vector.getD] using h_eq

end assertIsConcatenation

end check

section assertIsConcatenation

-- Poseidon is opaque to these proofs; see `Data/HashToField/hashElemsToField.lean`.
attribute [local irreducible] Clap.Lang.Poseidon.poseidonBN254

/-- After the three hashes the challenge, its powers, the padding check and the identity. -/
def assertIsConcatenation.afterHashes {nF nL nR : ℕ} (hL : nL ≤ nF) (hR : nR ≤ nF)
    (full : FVec bn254 nF) (left : FString bn254 nL) (right : FString bn254 nR)
    (leftHash rightHash fullHash : F bn254) : ClapM bn254 Unit := do
  let α ← poseidonBN254 #v[leftHash, rightHash, fullHash, left.len]
  let pows ← powers α nF
  assertIsConcatenation.padding left
  assertIsConcatenation.identity hL hR full left right.data pows

/-- After hashing `left`. -/
def assertIsConcatenation.afterLeft {nF nL nR : ℕ} (hL : nL ≤ nF) (hR : nR ≤ nF)
    (full : FVec bn254 nF) (left : FString bn254 nL) (right : FString bn254 nR)
    (leftHash : F bn254) : ClapM bn254 Unit := do
  let rightHash ← HashToField.hashBytesToField right
  let fullLen ← mkAdd left.len right.len
  let fullHash ← HashToField.hashBytesToField (⟨full, fullLen⟩ : FString bn254 nF)
  assertIsConcatenation.afterHashes hL hR full left right leftHash rightHash fullHash

/-- `full = left ++ right`, by one polynomial identity at a Fiat–Shamir challenge.

- The challenge is `H(H(left, ℓL), H(right, ℓR), H(full, ℓL + ℓR), ℓL)`.
- It asserts that `left` is zero from `ℓL = left.len` on, with `1 ≤ ℓL ≤ nL` and `ℓL < nF`.
- It asserts the identity `full(α) = left(α) + α^ℓL · right(α)`.

`right`'s length enters only the hashes, and its padding is not checked. As in Circom, the
caller is assumed to have validated `right_len`: at the Keyless call site `right` carries SHA-2
padding past it. `IsConcat` accordingly compares `right` in full. -/
def assertIsConcatenation {nF nL nR : ℕ} (hL : nL ≤ nF) (hR : nR ≤ nF)
    (full : FVec bn254 nF) (left : FString bn254 nL) (right : FString bn254 nR) :
    ClapM bn254 Unit := do
  let leftHash ← HashToField.hashBytesToField left
  assertIsConcatenation.afterLeft hL hR full left right leftHash

namespace assertIsConcatenation

/-- The Fiat–Shamir challenge `H(H(left, ℓL), H(right, ℓR), H(full, ℓL + ℓR), ℓL)`. -/
def challenge (H : HashFn) {nF nL nR : ℕ} (full_vals : Vector (ZMod bn254) nF)
    (left_vals : Vector (ZMod bn254) nL) (right_vals : Vector (ZMod bn254) nR)
    (lenL lenR : ZMod bn254) : ZMod bn254 :=
  H #v[HashToField.hashBytesToFieldSpec H left_vals lenL,
    HashToField.hashBytesToFieldSpec H right_vals lenR,
    HashToField.hashBytesToFieldSpec H full_vals (lenL + lenR), lenL]

/-- Everything `assertIsConcatenation` asserts. -/
def checks (H : HashFn) {nF nL nR : ℕ} (full_vals : Vector (ZMod bn254) nF)
    (left_vals : Vector (ZMod bn254) nL) (right_vals : Vector (ZMod bn254) nR)
    (lenL lenR : ZMod bn254) : Prop :=
  (∀ i : Fin nL, left_vals[i].val < 2 ^ 8) ∧ (∀ i : Fin nR, right_vals[i].val < 2 ^ 8) ∧
  (∀ i : Fin nF, full_vals[i].val < 2 ^ 8) ∧
  (0 < lenL.val ∧ lenL.val ≤ nL ∧ ∀ i : Fin nL, lenL.val ≤ i.val → left_vals[i] = 0) ∧
  lenL.val < nF ∧
  let α := challenge H full_vals left_vals right_vals lenL lenR
  evalAt full_vals α = evalAt left_vals α + α ^ lenL.val * evalAt right_vals α

lemma afterHashes_convertsM
  {H : HashFn}
  (h_H : Computes H)
  {nF nL nR : ℕ}
  (hL : nL ≤ nF) (hR : nR ≤ nF)
  {state : ClapMState bn254}
  {full : FVec bn254 nF} {left : FString bn254 nL} {right : FString bn254 nR}
  {leftHash rightHash fullHash : F bn254}
  {full_vals : Vector (ZMod bn254) nF} {left_vals : Vector (ZMod bn254) nL}
  {right_vals : Vector (ZMod bn254) nR}
  {lenL_val leftHash_val rightHash_val fullHash_val : ZMod bn254}
  (h_full : Converts FVec.conversion state full full_vals)
  (h_left : Converts FVec.conversion state left.data left_vals)
  (h_lenL : Converts F.conversion state left.len lenL_val)
  (h_right : Converts FVec.conversion state right.data right_vals)
  (h_leftHash : Converts F.conversion state leftHash leftHash_val)
  (h_rightHash : Converts F.conversion state rightHash rightHash_val)
  (h_fullHash : Converts F.conversion state fullHash fullHash_val)
  (h_nF : nF < bn254)
:
  ConvertsM FUnit.conversion (afterHashes hL hR full left right leftHash rightHash fullHash)
    state ()
    ((0 < lenL_val.val ∧ lenL_val.val ≤ nL ∧
        ∀ i : Fin nL, lenL_val.val ≤ i.val → left_vals[i] = 0) ∧
      (lenL_val.val < nF ∧
        let α := H #v[leftHash_val, rightHash_val, fullHash_val, lenL_val]
        evalAt full_vals α = evalAt left_vals α + α ^ lenL_val.val * evalAt right_vals α))
:= by
  unfold afterHashes
  have h_inputs := FVec.converts_push (FVec.converts_push (FVec.converts_push
    (FVec.converts_push FVec.converts_empty h_leftHash) h_rightHash) h_fullHash) h_lenL
  step (h_H (by decide) (by decide) h_inputs) as α
  step powers.convertsM h_α as pows
  have hP := padding_convertsM h_left h_lenL (by omega)
  apply convertsM_of_convertsM (convertsM_bind_and
    (function := fun _ ↦ identity hL hR full left right.data pows_result) hP
    (identity_convertsM hL hR (converts_skip hP h_full) (converts_skip hP h_left)
      (converts_skip hP h_lenL) (converts_skip hP h_right) (converts_skip hP h_pows) h_nF))
  · rfl
  · simp

lemma afterLeft_convertsM
  {H : HashFn}
  (h_H : Computes H)
  {nF nL nR : ℕ}
  (hL : nL ≤ nF) (hR : nR ≤ nF)
  {state : ClapMState bn254}
  {full : FVec bn254 nF} {left : FString bn254 nL} {right : FString bn254 nR}
  {leftHash : F bn254}
  {full_vals : Vector (ZMod bn254) nF} {left_vals : Vector (ZMod bn254) nL}
  {right_vals : Vector (ZMod bn254) nR} {lenL_val lenR_val leftHash_val : ZMod bn254}
  (h_full : Converts FVec.conversion state full full_vals)
  (h_left : Converts FVec.conversion state left.data left_vals)
  (h_lenL : Converts F.conversion state left.len lenL_val)
  (h_right : Converts FVec.conversion state right.data right_vals)
  (h_lenR : Converts F.conversion state right.len lenR_val)
  (h_leftHash : Converts F.conversion state leftHash leftHash_val)
  (h_nR : nR ≤ 1953) (h_nF : nF ≤ 1953)
:
  ConvertsM FUnit.conversion (afterLeft hL hR full left right leftHash) state ()
    ((∀ i : Fin nR, right_vals[i].val < 2 ^ 8) ∧
      (∀ i : Fin nF, full_vals[i].val < 2 ^ 8) ∧
      ((0 < lenL_val.val ∧ lenL_val.val ≤ nL ∧
          ∀ i : Fin nL, lenL_val.val ≤ i.val → left_vals[i] = 0) ∧
        (lenL_val.val < nF ∧
          let α := H #v[leftHash_val, HashToField.hashBytesToFieldSpec H right_vals lenR_val,
            HashToField.hashBytesToFieldSpec H full_vals (lenL_val + lenR_val), lenL_val]
          evalAt full_vals α = evalAt left_vals α + α ^ lenL_val.val * evalAt right_vals α)))
:= by
  unfold afterLeft
  have hR' := HashToField.hashBytesToField.convertsM h_H h_right h_lenR h_nR
  apply convertsM_bind_and (function := fun rh ↦ do
    let fullLen ← mkAdd left.len right.len
    let fullHash ← HashToField.hashBytesToField (⟨full, fullLen⟩ : FString bn254 nF)
    afterHashes hL hR full left right leftHash rh fullHash) hR'
  have h_full1 := converts_skip hR' h_full
  have h_left1 := converts_skip hR' h_left
  have h_lenL1 := converts_skip hR' h_lenL
  have h_right1 := converts_skip hR' h_right
  have h_lenR1 := converts_skip hR' h_lenR
  have h_leftHash1 := converts_skip hR' h_leftHash
  have h_rh := hR'.result
  clear h_full h_left h_lenL h_right h_lenR h_leftHash hR'
  generalize (HashToField.hashBytesToField right).getResult state.numAlloc state.σ = rh at *
  generalize (HashToField.hashBytesToField right).getState state = st1 at *
  step mkAdd.convertsM h_lenL1 h_lenR1 as fullLen
  have hF := HashToField.hashBytesToField.convertsM (input := (⟨full, fullLen_result⟩ :
    FString bn254 nF)) h_H h_full1 h_fullLen h_nF
  apply convertsM_of_convertsM (convertsM_bind_and
    (function := fun fh ↦ afterHashes hL hR full left right leftHash rh fh) hF
    (afterHashes_convertsM h_H hL hR (converts_skip hF h_full1) (converts_skip hF h_left1)
      (converts_skip hF h_lenL1) (converts_skip hF h_right1) (converts_skip hF h_leftHash1)
      (converts_skip hF h_rh) hF.result (lt_of_le_of_lt h_nF (by decide))))
  · rfl
  · simp

lemma convertsM
  {H : HashFn}
  (h_H : Computes H)
  {nF nL nR : ℕ}
  (hL : nL ≤ nF) (hR : nR ≤ nF)
  {state : ClapMState bn254}
  {full : FVec bn254 nF} {left : FString bn254 nL} {right : FString bn254 nR}
  {full_vals : Vector (ZMod bn254) nF} {left_vals : Vector (ZMod bn254) nL}
  {right_vals : Vector (ZMod bn254) nR} {lenL_val lenR_val : ZMod bn254}
  (h_full : Converts FVec.conversion state full full_vals)
  (h_left : Converts FVec.conversion state left.data left_vals)
  (h_lenL : Converts F.conversion state left.len lenL_val)
  (h_right : Converts FVec.conversion state right.data right_vals)
  (h_lenR : Converts F.conversion state right.len lenR_val)
  (h_nF : nF ≤ 1953)
:
  ConvertsM FUnit.conversion (assertIsConcatenation hL hR full left right) state ()
    (checks H full_vals left_vals right_vals lenL_val lenR_val)
:= by
  unfold assertIsConcatenation
  have hLh := HashToField.hashBytesToField.convertsM h_H h_left h_lenL (by omega)
  apply convertsM_of_convertsM (convertsM_bind_and
    (function := fun lh ↦ afterLeft hL hR full left right lh) hLh
    (afterLeft_convertsM h_H hL hR (converts_skip hLh h_full) (converts_skip hLh h_left)
      (converts_skip hLh h_lenL) (converts_skip hLh h_right) (converts_skip hLh h_lenR)
      hLh.result (by omega) h_nF))
  · rfl
  · simp only [checks, challenge]

/-! ### What `checks` means -/

lemma ext_pad_of {nL : ℕ} {left_vals : Vector (ZMod bn254) nL} {ℓ : ℕ}
    (h : ∀ i : Fin nL, ℓ ≤ i.val → left_vals[i] = 0) : ∀ i, ℓ ≤ i → ext left_vals i = 0 := by
  intro i hi
  by_cases h_i : i < nL
  · rw [ext_of_lt _ h_i]
    exact h ⟨i, h_i⟩ hi
  · exact ext_of_le _ (by omega)

/-- (Completeness) A real concatenation, with its lengths in range and its bytes bytes, passes every check, whatever `H` is. -/
lemma checks_of_isConcat {H : HashFn} {nF nL nR : ℕ} {full_vals : Vector (ZMod bn254) nF}
    {left_vals : Vector (ZMod bn254) nL} {right_vals : Vector (ZMod bn254) nR}
    {lenL lenR : ZMod bn254}
    (h_bL : ∀ i : Fin nL, left_vals[i].val < 2 ^ 8) (h_bR : ∀ i : Fin nR, right_vals[i].val < 2 ^ 8)
    (h_bF : ∀ i : Fin nF, full_vals[i].val < 2 ^ 8)
    (h_pos : 0 < lenL.val) (h_le : lenL.val ≤ nL) (h_lt : lenL.val < nF)
    (h_cat : IsConcat full_vals left_vals right_vals lenL.val) :
    checks H full_vals left_vals right_vals lenL lenR := by
  refine ⟨h_bL, h_bR, h_bF, ⟨h_pos, h_le, fun i hi ↦ ?_⟩, h_lt, evalAt_of_isConcat h_cat _⟩
  have := h_cat.1 i.val hi
  rwa [ext_of_lt _ i.isLt] at this

/-- The challenge query, as a function of the random function. -/
def challengeQuery (f : Query → ZMod bn254) {nF nL nR : ℕ} (full_vals : Vector (ZMod bn254) nF)
    (left_vals : Vector (ZMod bn254) nL) (right_vals : Vector (ZMod bn254) nR)
    (lenL lenR : ZMod bn254) : Query :=
  RandomOracle.hashQ #v[HashToField.hashBytesToFieldSpec (Query.toHashFn f) left_vals lenL,
    HashToField.hashBytesToFieldSpec (Query.toHashFn f) right_vals lenR,
    HashToField.hashBytesToFieldSpec (Query.toHashFn f) full_vals (lenL + lenR), lenL]

/-- (Soundness under the random oracle) For a fixed instance that is not a concatenation, the
checks all pass with probability at most `((nF - 1) + (nR - 1) + 75) / p` over `H ← randomOracle`.

The first term is Schwartz–Zippel for the difference polynomial, while the challenge query is
fresh. The `75 / p` covers its colliding with one of the queries that hashing the three strings
makes:

- `75 = 3 · 25`: one `HashToField.challenge_mem_transcript_le` per hashed string (`left`,
  `right`, `full`), union-bounded.
- `25 = 5 · 5`: hashing a string's field elements makes at most 5 Poseidon calls, up to 4 chunk
  calls on 16 elements each and the final call on their digests `#v[d₀, …, dₖ₋₁]`. Input `j` of
  the challenge query is the string's hash, so equaling one of these calls `t` forces
  `hash = t.coord j`, which `HashToField.prob_hash_eq_le` bounds by `5 / p`.
- `5 = 1 + 4`: the hash is `f` at the final call. That is `1 / p` while the final call is none of
  the chunk calls, and `1 / p` for each of the 4 chunk calls it could equal, since that forces
  the first digest `d₀` to equal the chunk's first element.

A crude bound -/
theorem prob_checks_le {nF nL nR : ℕ} (hL : nL ≤ nF) (full_vals : Vector (ZMod bn254) nF)
    (left_vals : Vector (ZMod bn254) nL) (right_vals : Vector (ZMod bn254) nR)
    (lenL lenR : ZMod bn254)
    (h_bad : ¬ IsConcat full_vals left_vals right_vals lenL.val) :
    randomOracle.toOuterMeasure
        {f | checks (Query.toHashFn f) full_vals left_vals right_vals lenL lenR}
      ≤ (((nF - 1) + (nR - 1) + 75 : ℕ) : ENNReal) / bn254 := by
  classical
  -- Without the padding or with `lenL ≥ nF` nothing passes; otherwise the identity is nontrivial.
  by_cases h_pre : (∀ i : Fin nL, lenL.val ≤ i.val → left_vals[i] = 0) ∧ lenL.val < nF
  swap
  · have h_empty : {f | checks (Query.toHashFn f) full_vals left_vals right_vals lenL lenR} = ∅ := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hf
      exact h_pre ⟨hf.2.2.2.1.2.2, hf.2.2.2.2.1⟩
    rw [h_empty]
    simp
  obtain ⟨h_pad, h_lt⟩ := h_pre
  set D := concatDiff full_vals left_vals right_vals lenL.val with hD
  have h_D : D ≠ 0 := by
    rw [hD, Ne, concatDiff_eq_zero_iff _ _ _ (ext_pad_of h_pad)]
    exact h_bad
  set vL := HashToField.hashBytesToFieldElems left_vals lenL
  set vR := HashToField.hashBytesToFieldElems right_vals lenR
  set vF := HashToField.hashBytesToFieldElems full_vals (lenL + lenR)
  set c := fun f ↦ challengeQuery f full_vals left_vals right_vals lenL lenR
  set T := fun f ↦ HashToField.transcript f vL ∪ HashToField.transcript f vR ∪
    HashToField.transcript f vF
  have h_ch : ∀ f, challenge (Query.toHashFn f) full_vals left_vals right_vals lenL lenR =
      f (c f) := fun f ↦ RandomOracle.toHashFn_apply f _ (by decide)
  have h_sub : {f | checks (Query.toHashFn f) full_vals left_vals right_vals lenL lenR} ⊆
      (({f | c f ∈ HashToField.transcript f vL} ∪ {f | c f ∈ HashToField.transcript f vR}) ∪
        {f | c f ∈ HashToField.transcript f vF}) ∪
      {f | c f ∉ (T f : Set Query) ∧ D.eval (f (c f)) = 0} := by
    intro f hf
    have h_root : D.eval (f (c f)) = 0 := by
      rw [hD, eval_concatDiff, ← h_ch f, hf.2.2.2.2.2, sub_self]
    by_cases h : c f ∈ T f
    · simp only [T, Finset.mem_union] at h
      left
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · exact Or.inr ⟨by simpa using h, h_root⟩
  have h_coord : ∀ (j : ℕ) (hj : j < 3) f,
      (c f).coord j = (#v[HashToField.hashBytesToFieldSpec (Query.toHashFn f) left_vals lenL,
        HashToField.hashBytesToFieldSpec (Query.toHashFn f) right_vals lenR,
        HashToField.hashBytesToFieldSpec (Query.toHashFn f) full_vals (lenL + lenR),
        lenL] : Vector (ZMod bn254) 4)[j] := by
    intro j hj f
    simp only [c, challengeQuery]
    rw [RandomOracle.coord_hashQ _ (by decide), dif_pos (by omega)]
  have hcL := HashToField.challenge_mem_transcript_le vL 0 c (fun f ↦ h_coord 0 (by decide) f)
  have hcR := HashToField.challenge_mem_transcript_le vR 1 c (fun f ↦ h_coord 1 (by decide) f)
  have hcF := HashToField.challenge_mem_transcript_le vF 2 c (fun f ↦ h_coord 2 (by decide) f)
  have h_fresh := randomOracle_fresh_le c (fun f ↦ ↑(T f)) (fun _ y ↦ D.eval y = 0)
    ((nF - 1) + (nR - 1))
    (fun f f' h ↦ by
      have h' : ∀ q ∈ T f, f q = f' q := by simpa using h
      have eL := HashToField.congr vL (fun q hq ↦ h' q (by simp [T, hq]))
      have eR := HashToField.congr vR (fun q hq ↦ h' q (by simp [T, hq]))
      have eF := HashToField.congr vF (fun q hq ↦ h' q (by simp [T, hq]))
      have hL' : HashToField.hashBytesToFieldSpec (Query.toHashFn f) left_vals lenL =
          HashToField.hashBytesToFieldSpec (Query.toHashFn f') left_vals lenL := eL.1
      have hR' : HashToField.hashBytesToFieldSpec (Query.toHashFn f) right_vals lenR =
          HashToField.hashBytesToFieldSpec (Query.toHashFn f') right_vals lenR := eR.1
      have hF' : HashToField.hashBytesToFieldSpec (Query.toHashFn f) full_vals (lenL + lenR) =
          HashToField.hashBytesToFieldSpec (Query.toHashFn f') full_vals (lenL + lenR) := eF.1
      refine ⟨?_, by simp [T, eL.2, eR.2, eF.2], rfl⟩
      simp only [c, challengeQuery, hL', hR', hF'])
    (fun _ ↦ card_roots_le h_D (natDegree_concatDiff_le _ _ _ hL h_lt))
  calc randomOracle.toOuterMeasure
          {f | checks (Query.toHashFn f) full_vals left_vals right_vals lenL lenR}
      ≤ ((randomOracle.toOuterMeasure {f | c f ∈ HashToField.transcript f vL} +
            randomOracle.toOuterMeasure {f | c f ∈ HashToField.transcript f vR}) +
            randomOracle.toOuterMeasure {f | c f ∈ HashToField.transcript f vF}) +
          randomOracle.toOuterMeasure {f | c f ∉ (T f : Set Query) ∧ D.eval (f (c f)) = 0} := by
        refine (MeasureTheory.measure_mono h_sub).trans ?_
        refine (MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact MeasureTheory.measure_union_le _ _
    _ ≤ ((25 / bn254 + 25 / bn254) + 25 / bn254) + (((nF - 1) + (nR - 1) : ℕ) : ENNReal) / bn254 :=
        add_le_add (add_le_add (add_le_add hcL hcR) hcF) h_fresh
    _ = (((nF - 1) + (nR - 1) + 75 : ℕ) : ENNReal) / bn254 := by
        simp only [ENNReal.div_add_div_same]
        push_cast
        ring_nf

end assertIsConcatenation

end assertIsConcatenation

section examples

private def gatesHold (c : ClapM bn254 Unit) : Bool :=
  let circ := c.getCircuit 0 {}
  let σ := c.getHashConsState 0 {}
  let Γ := c.getVarStore {} 0 {}
  circ.all fun g ↦ match g with
    | .eq0 e => [Γ, σ|e] == some 0
    | .num2bits w e => ([Γ, σ|e].map fun v ↦ decide (v.val < 2 ^ w)).getD false
    | _ => true

private def concat {nF nL nR : ℕ} (hL : nL ≤ nF) (hR : nR ≤ nF) (full : Vector (ZMod bn254) nF)
    (left : Vector (ZMod bn254) nL) (lenL : ZMod bn254) (right : Vector (ZMod bn254) nR)
    (lenR : ZMod bn254) : Bool :=
  gatesHold do
    let fl ← full.mapM (fun x ↦ liftM (HashConsM.mkConstant (p := bn254) x))
    let l ← left.mapM (fun x ↦ liftM (HashConsM.mkConstant (p := bn254) x))
    let ll ← liftM (HashConsM.mkConstant (p := bn254) lenL)
    let r ← right.mapM (fun x ↦ liftM (HashConsM.mkConstant (p := bn254) x))
    let rl ← liftM (HashConsM.mkConstant (p := bn254) lenR)
    assertIsConcatenation hL hR fl ⟨l, ll⟩ ⟨r, rl⟩

-- "hello" = "hel" ++ "lo"
example : concat (by decide) (by decide) #v[104, 101, 108, 108, 111] #v[104, 101, 108] 3
    #v[108, 111] 2 = true := by native_decide
-- zero padding throughout: "ab" = "a" ++ "b"
example : concat (by decide) (by decide) #v[97, 98, 0] #v[97, 0] 1 #v[98, 0] 1 = true := by
  native_decide
-- "abc" ≠ "ab" ++ "b"
example : concat (by decide) (by decide) #v[97, 98, 99] #v[97, 98] 2 #v[98] 1 = false := by
  native_decide
-- a nonzero byte in `left` past its length fails
example : concat (by decide) (by decide) #v[97, 98, 99] #v[97, 98, 99] 2 #v[99] 1 = false := by
  native_decide
-- `right`'s padding is not checked, but the identity compares it in full
example : concat (by decide) (by decide) #v[97, 98, 99] #v[97, 98] 2 #v[99, 100] 1 = false := by
  native_decide

/-
The rest of the old vectors, left as comments: each takes about 20 s. All were checked with
`native_decide` on 2026-09-29.

-- "hello" = "h" ++ "ello"
example : concat (by decide) (by decide) #v[104, 101, 108, 108, 111] #v[104] 1
    #v[101, 108, 108, 111] 4 = true
-- "abc" = "ab" ++ "c"
example : concat (by decide) (by decide) #v[97, 98, 99] #v[97, 98] 2 #v[99] 1 = true
-- "abc" ≠ "ac" ++ "c"
example : concat (by decide) (by decide) #v[97, 98, 99] #v[97, 99] 2 #v[99] 1 = false
-- `left` zero past its length
example : concat (by decide) (by decide) #v[97, 98, 99] #v[97, 98, 0] 2 #v[99] 1 = true
-- `right` zero past its length
example : concat (by decide) (by decide) #v[97, 98, 99] #v[97, 98] 2 #v[99, 0] 1 = true
-/

end examples

end Clap.Lang.FString
