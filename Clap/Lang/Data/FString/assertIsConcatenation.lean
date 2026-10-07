import Clap.Lang.Core.Combinators.foldlM
import Clap.Lang.Core.FUnit.assert_eq
import Clap.Lang.Data.FArray.rightArraySelector
import Clap.Lang.Gate.eq0
import Clap.Lang.Data.FString.isSubstring

namespace Clap.Lang.FString

open Poseidon RandomOracle Primes FiatShamir

variable {p : ℕ}

/-! Circom's `AssertIsConcatenation` reads each byte array as the coefficients of a polynomial, evaluates them at one challenge `α`, and
checks `full(α) = left(α) + α^ℓ · right(α)`. Vectors are compared through `ext v i`, their zero
extension, so no index bounds appear. -/

section identity

open Polynomial hiding ext

namespace assertIsConcatenation

variable {nF nL nR : ℕ}

/-- `full` is `left` (zero-padded after `ℓ`) followed by `right`.
`left` is `0` from `ℓ` on, and every position of `full`, zero-extended, is `left`'s plus
`right`'s shifted to start at `ℓ`.

`right` is compared in full, including padding. The identity pins every entry of `right` that
lands inside `full`, and makes those past the end of `full` zero. Its length enters only the
hashes -/
def IsConcat (full : Vector (ZMod p) nF) (left : Vector (ZMod p) nL) (right : Vector (ZMod p) nR) (ℓ : ℕ) : Prop :=
  (∀ i, ℓ ≤ i → ext left i = 0) ∧ ∀ i, ext full i = ext left i + (if ℓ ≤ i then ext right (i - ℓ) else 0)

noncomputable def concatDiff (full : Vector (ZMod p) nF) (left : Vector (ZMod p) nL)
    (right : Vector (ZMod p) nR) (ℓ : ℕ) : (ZMod p)[X] := vecPoly full - (vecPoly left + X ^ ℓ * vecPoly right)

lemma concatDiff_eq_zero_iff (full : Vector (ZMod p) nF) (left : Vector (ZMod p) nL)
    (right : Vector (ZMod p) nR) {ℓ : ℕ} (h_pad : ∀ i, ℓ ≤ i → ext left i = 0) :
    concatDiff full left right ℓ = 0 ↔ IsConcat full left right ℓ := by
  rw [concatDiff, sub_eq_zero, Polynomial.ext_iff]
  simp only [coeff_add, coeff_vecPoly, coeff_X_pow_mul_vecPoly]
  exact ⟨fun h ↦ ⟨h_pad, h⟩, fun h ↦ h.2⟩

lemma eval_concatDiff (full : Vector (ZMod p) nF) (left : Vector (ZMod p) nL)
    (right : Vector (ZMod p) nR) (ℓ : ℕ) (α : ZMod p) :
    (concatDiff full left right ℓ).eval α =
      evalAt full α - (evalAt left α + α ^ ℓ * evalAt right α) := by
  simp [concatDiff, eval_vecPoly]

lemma natDegree_concatDiff_le (full : Vector (ZMod p) nF) (left : Vector (ZMod p) nL)
    (right : Vector (ZMod p) nR) {ℓ : ℕ} (hL : nL ≤ nF) (hℓ : ℓ < nF) :
    (concatDiff full left right ℓ).natDegree ≤ (nF - 1) + (nR - 1) := by
  unfold concatDiff
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (natDegree_vecPoly_le _).trans (by omega)
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (natDegree_vecPoly_le _).trans (by omega)
    · exact (natDegree_X_pow_mul_vecPoly_le _ _).trans (by omega)

/-- (Completeness of the identity) a real concatenation passes at every `α`. -/
lemma evalAt_of_isConcat {full : Vector (ZMod p) nF} {left : Vector (ZMod p) nL}
    {right : Vector (ZMod p) nR} {ℓ : ℕ} (h : IsConcat full left right ℓ) (α : ZMod p) :
    evalAt full α = evalAt left α + α ^ ℓ * evalAt right α := by
  have h0 := (concatDiff_eq_zero_iff full left right h.1).mpr h
  have := congrArg (Polynomial.eval α) h0
  rw [eval_concatDiff] at this
  simpa [sub_eq_zero] using this

end assertIsConcatenation

end identity

/-! For strings encoded by `FString.encodeV`, `IsConcat` is string concatenation. see
`isSubstring.lean`'s section of the same name for the shared helpers. -/

section strings

namespace assertIsConcatenation

/-- A list of characters, one byte each, zero-extended. -/
def zext (l : List Char) (i : ℕ) : ZMod p := if h : i < l.length then (((l[i]'h).toUInt8.toNat : ℕ) : ZMod p) else 0

lemma ext_encodeV_eq_zext {w : ℕ} {S : String} (hS : S.length ≤ w) (i : ℕ) :
    ext (encodeV (p := p) w S) i = zext S.toList i := by
  rw [ext_encodeV hS, zext]

lemma zext_append (L R : List Char) (i : ℕ) :
    zext (p := p) (L ++ R) i = zext L i + (if L.length ≤ i then zext R (i - L.length) else 0) := by
  unfold zext
  by_cases h1 : i < L.length
  · simp [h1, List.getElem_append_left h1, show ¬ L.length ≤ i by omega,
      show i < L.length + R.length by omega]
  · by_cases h2 : i < L.length + R.length
    · simp [h1, h2, List.getElem_append_right (show L.length ≤ i by omega),
        show i - L.length < R.length by omega, show L.length ≤ i by omega]
    · simp [h1, show ¬ i < L.length + R.length by omega, show ¬ i - L.length < R.length by omega]

/-- NUL-free byte strings are determined by their zero extensions. -/
lemma zext_inj {l₁ l₂ : List Char} (hp : 256 < p)
    (h₁ : ∀ c ∈ l₁, 0 < c.toNat ∧ c.toNat < 256) (h₂ : ∀ c ∈ l₂, 0 < c.toNat ∧ c.toNat < 256) :
    (∀ i, zext (p := p) l₁ i = zext l₂ i) ↔ l₁ = l₂ := by
  refine ⟨fun h ↦ ?_, fun h _ ↦ by rw [h]⟩
  -- a position inside one list and outside the other would equate a nonzero byte with `0`
  have h_nz : ∀ {l : List Char}, (∀ c ∈ l, 0 < c.toNat ∧ c.toNat < 256) → ∀ i (hi : i < l.length),
      zext (p := p) l i ≠ 0 := by
    intro l hl i hi h0
    rw [zext, dif_pos hi, toUInt8_toNat_of_lt (hl _ (List.getElem_mem hi)).2] at h0
    have := natCast_inj (p := p) (a := (l[i]).toNat) (b := 0)
      (by have := (hl _ (List.getElem_mem hi)).2; omega) (by omega)
      (by rw [Nat.cast_zero]; exact h0)
    have := (hl _ (List.getElem_mem hi)).1
    omega
  have h_len : l₁.length = l₂.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact h_nz h₂ l₁.length hlt (by rw [← h l₁.length, zext, dif_neg (by omega)])
    · exact h_nz h₁ l₂.length hlt (by rw [h l₂.length, zext, dif_neg (by omega)])
  apply List.ext_getElem h_len
  intro i hi₁ hi₂
  have := h i
  rw [zext, zext, dif_pos hi₁, dif_pos hi₂, toUInt8_toNat_of_lt (h₁ _ (List.getElem_mem hi₁)).2,
    toUInt8_toNat_of_lt (h₂ _ (List.getElem_mem hi₂)).2] at this
  exact Char.ext (UInt32.toNat.inj (natCast_inj (a := (l₁[i]).toNat) (b := (l₂[i]).toNat)
    (by have := (h₁ _ (List.getElem_mem hi₁)).2; omega)
    (by have := (h₂ _ (List.getElem_mem hi₂)).2; omega) this))

/-- For strings encoded by `FString.encodeV`, `IsConcat` at `ℓ = left.length` is string
concatenation. The characters are bytes with no NUL -/
theorem isConcat_encodeV_iff {nF nL nR : ℕ} {F L R : String} (hp : 256 < p)
    (hF : F.length ≤ nF) (hL : L.length ≤ nL) (hR : R.length ≤ nR)
    (hFc : ∀ c ∈ F.toList, 0 < c.toNat ∧ c.toNat < 256)
    (hLc : ∀ c ∈ L.toList, 0 < c.toNat ∧ c.toNat < 256)
    (hRc : ∀ c ∈ R.toList, 0 < c.toNat ∧ c.toNat < 256) :
    IsConcat (encodeV (p := p) nF F) (encodeV (p := p) nL L) (encodeV (p := p) nR R) L.length ↔ F = L ++ R := by
  unfold IsConcat
  have h_pad : ∀ i, L.length ≤ i → ext (encodeV (p := p) nL L) i = 0 := by
    intro i hi
    rw [ext_encodeV_eq_zext hL, zext, dif_neg (by rw [String.length_toList]; omega)]
  simp only [ext_encodeV_eq_zext hF, ext_encodeV_eq_zext hL, ext_encodeV_eq_zext hR]
  rw [← String.toList_inj, String.toList_append]
  rw [← zext_inj (p := p) hp hFc (by
    intro c hc
    rw [List.mem_append] at hc
    exact hc.elim (hLc c) (hRc c))]
  simp only [zext_append, String.length_toList]
  constructor
  · exact fun h ↦ h.2
  · exact fun h ↦ ⟨by simpa [ext_encodeV_eq_zext hL] using h_pad, h⟩

end assertIsConcatenation

end strings

section check

/-- Circom's lines 33–36: `left` is zero from `left.len` on. Circom enforces this explicitly
because otherwise the start of `right` could sit at the end of `left` and still pass the
polynomial check. `RightArraySelector(left_len-1)` is satisfiable only when `1 ≤ left.len ≤ nL`. -/
def assertIsConcatenation.padding [p.AtLeastTwo] {nL : ℕ} (left : FString p nL) : ClapM p Unit := do
  -- Circom: `left_len-1`
  let lm1 ← left.len - (← mkF 1)
  -- Circom: `signal left_selector[MAX_LEFT_STR_LEN] <== RightArraySelector(MAX_LEFT_STR_LEN)(left_len-1);`
  let sel ← rightArraySelector nL lm1
  -- Circom: `left_selector[i] * left[i] === 0;`, for each `i < MAX_LEFT_STR_LEN`
  (sel.zip left.data).foldlM (fun _ sx ↦ do
    let prod ← sx.1 * sx.2
    eq0 prod) ()

/-- Circom's `AssertIsConcatenation` from `left_poly` on (lines 45–66), given the challenge powers
`pows`: `full(α) = left(α) + α^left_len · right(α)`. `selectArrayValue` gives `α^left_len`, and
asserts `left_len < nF`. `hL` and `hR` are Circom's implicit array bounds: `left_poly` and
`right_poly` read `challenge_powers[i]` for `i` up to `MAX_LEFT_STR_LEN` and `MAX_RIGHT_STR_LEN`.

Circom makes every product a signal: `left_poly[i]`, `right_poly[i]` and `full_poly[i]`. Here
they stay expressions inside `dotProduct`. -/
def assertIsConcatenation.identity [p.AtLeastTwo] {nF nL nR : ℕ} (hL : nL ≤ nF) (hR : nR ≤ nF)
    (full : FVec p nF) (left : FString p nL) (right : FVec p nR) (pows : FVec p nF) : ClapM p Unit := do
  -- Circom: `left_poly[i] <== left[i] * challenge_powers[i];` and `signal left_poly_eval <== Sum(MAX_LEFT_STR_LEN)(left_poly);`, as one dot product
  let leftEval ← dotProduct left.data ((pows.extract 0 nL).cast (by omega))
  -- Circom: `right_poly[i] <== right[i] * challenge_powers[i];` and `signal right_poly_eval <== Sum(MAX_RIGHT_STR_LEN)(right_poly);`
  let rightEval ← dotProduct right ((pows.extract 0 nR).cast (by omega))
  -- Circom: `full_poly[i] <== full_string[i] * challenge_powers[i];` and `signal full_poly_eval <== Sum(MAX_FULL_STR_LEN)(full_poly);`
  let fullEval ← dotProduct full pows
  -- Circom: `var distinguishing_value = SelectArrayValue(MAX_FULL_STR_LEN)(challenge_powers, left_len);`
  let dv ← selectArrayValue nF pows left.len
  -- Circom: `full_poly_eval === left_poly_eval + distinguishing_value * right_poly_eval;`
  let prod ← dv * rightEval
  let rhs ← leftEval + prod
  assert_eq fullEval rhs

namespace assertIsConcatenation

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
    · have hpos : 0 < len_val.val := by
        rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]; exact h0
      have h_val : (len_val - 1).val = len_val.val - 1 := by
        haveI : Fact (1 < p) := ⟨Nat.AtLeastTwo.one_lt⟩
        have h1 : (1 : ZMod p).val = 1 := ZMod.val_one p
        rw [ZMod.val_sub (by rw [h1]; omega), h1]
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
    (len_val.val < nF ∧
      evalAt full_vals α = evalAt left_vals α + α ^ len_val.val * evalAt right_vals α)
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
  · rw [dotProduct_powers_prefix_eq_evalAt hL, dotProduct_powers_prefix_eq_evalAt hR,
      dotProduct_powers_eq_evalAt]
    simp only [true_implies]
    exact and_congr_right fun h_lt ↦ by simp [h_lt, Vector.getD]

/-- The powers, then the identity. Stated at an abstract state, so that `afterHashes_convertsM`
does not elaborate it against `padding`'s concrete post-state. -/
private lemma powers_identity_convertsM
  [p.AtLeastTwo]
  {nF nL nR : ℕ}
  (hL : nL ≤ nF) (hR : nR ≤ nF)
  {state : ClapMState p}
  {α : F p} {full : FVec p nF} {left : FString p nL} {right : FVec p nR}
  {α_val : ZMod p} {full_vals : Vector (ZMod p) nF} {left_vals : Vector (ZMod p) nL}
  {right_vals : Vector (ZMod p) nR} {len_val : ZMod p}
  (h_α : Converts F.conversion state α α_val)
  (h_full : Converts FVec.conversion state full full_vals)
  (h_data : Converts FVec.conversion state left.data left_vals)
  (h_len : Converts F.conversion state left.len len_val)
  (h_right : Converts FVec.conversion state right right_vals)
  (h_nF : nF < p)
:
  ConvertsM FUnit.conversion (do
      let pows ← powers α nF
      identity hL hR full left right pows) state ()
    (len_val.val < nF ∧ evalAt full_vals α_val =
      evalAt left_vals α_val + α_val ^ len_val.val * evalAt right_vals α_val)
:= by
  step powers.convertsM h_α as pows
  apply convertsM_of_convertsM
    (identity_convertsM hL hR h_full h_data h_len h_right h_pows h_nF)
  · rfl
  · simp

end assertIsConcatenation

end check

section assertIsConcatenation

-- Poseidon is opaque to these proofs (see `Data/HashToField/hashElemsToField.lean`.)
attribute [local irreducible] Clap.Lang.Poseidon.poseidonBN254

/-- Circom's `AssertIsConcatenation` after the three hashes (lines 30–66): the challenge, the
padding check, the powers, then `identity`. -/
def assertIsConcatenation.afterHashes {nF nL nR : ℕ} (hL : nL ≤ nF) (hR : nR ≤ nF)
    (full : FVec bn254 nF) (left : FString bn254 nL) (right : FString bn254 nR)
    (leftHash rightHash fullHash : F bn254) : ClapM bn254 Unit := do
  -- Circom: `signal random_challenge <== Poseidon(4)([left_hash, right_hash, full_hash, left_len]);`
  let α ← poseidonBN254 #v[leftHash, rightHash, fullHash, left.len]
  -- Circom: lines 33–36, `left` is zero from `left_len` on
  assertIsConcatenation.padding left
  -- Circom: `challenge_powers[0] <== 1;`, `challenge_powers[1] <== random_challenge;` and `challenge_powers[i] <== challenge_powers[i-1] * random_challenge;`
  let pows ← powers α nF
  -- Circom: lines 45–66, the identity
  assertIsConcatenation.identity hL hR full left right.data pows

/-- Circom's `AssertIsConcatenation` after `left_hash` (lines 28–29): the other two hashes, then `afterHashes`. -/
def assertIsConcatenation.afterLeft {nF nL nR : ℕ} (hL : nL ≤ nF) (hR : nR ≤ nF)
    (full : FVec bn254 nF) (left : FString bn254 nL) (right : FString bn254 nR)
    (leftHash : F bn254) : ClapM bn254 Unit := do
  -- Circom: `signal right_hash <== HashBytesToFieldWithLen(MAX_RIGHT_STR_LEN)(right, right_len);`
  let rightHash ← HashToField.hashBytesToField right
  -- Circom: `left_len+right_len`, the length `full_string` is hashed with
  let fullLen ← mkAdd left.len right.len
  -- Circom: `signal full_hash <== HashBytesToFieldWithLen(MAX_FULL_STR_LEN)(full_string, left_len+right_len);`
  let fullHash ← HashToField.hashBytesToField (⟨full, fullLen⟩ : FString bn254 nF)
  assertIsConcatenation.afterHashes hL hR full left right leftHash rightHash fullHash

/-- `full = left ++ right`. ℓL/ℓR is left.len/right.len

- The challenge is `H(H(left, ℓL), H(right, ℓR), H(full, ℓL + ℓR), ℓL)`.
- It asserts that the three strings are bytes (hashing them range-checks them).
- It asserts that `left` is zero from `ℓL = left.len` on, with `1 ≤ ℓL ≤ nL`.
- It asserts `ℓL < nF` (`SelectArrayValue`). So, like Circom, it rejects `left` filling all of `full`, `ℓL = nL = nF`.
- It asserts the identity `full(α) = left(α) + α^ℓL · right(α)`.

`right`'s length enters only the hashes, and its padding is not checked. As in Circom, the
caller is assumed to have validated `right_len`: at the Keyless call site `right` carries SHA-2
padding past it. The identity compares `right` in full, padding included, and `IsConcat` does
too. -/
def assertIsConcatenation {nF nL nR : ℕ} (hL : nL ≤ nF) (hR : nR ≤ nF)
    (full : FVec bn254 nF) (left : FString bn254 nL) (right : FString bn254 nR) : ClapM bn254 Unit := do
  -- Circom: `signal left_hash <== HashBytesToFieldWithLen(MAX_LEFT_STR_LEN)(left, left_len);`
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
  -- `padding` and `identity` both assert, so they are sequenced with `convertsM_bind_and`.
  have hP := padding_convertsM h_left h_lenL (by omega)
  apply convertsM_of_convertsM (convertsM_bind_and
    (function := fun _ ↦ do
      let pows ← powers α_result nF
      identity hL hR full left right.data pows) hP
    (powers_identity_convertsM hL hR (converts_skip hP h_α) (converts_skip hP h_full)
      (converts_skip hP h_left) (converts_skip hP h_lenL) (converts_skip hP h_right) h_nF))
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

/-! What is checks -/

private lemma ext_pad_of {nL : ℕ} {left_vals : Vector (ZMod bn254) nL} {ℓ : ℕ}
    (h : ∀ i : Fin nL, ℓ ≤ i.val → left_vals[i] = 0) : ∀ i, ℓ ≤ i → ext left_vals i = 0 := by
  intro i hi
  by_cases h_i : i < nL
  · rw [ext_of_lt _ h_i]
    exact h ⟨i, h_i⟩ hi
  · exact ext_of_le _ (by omega)

/-- (Completeness) A real concatenation, with its lengths in range and its entries bytes, passes
every check, whatever `H` is. -/
lemma checks_of_isConcat {H : HashFn} {nF nL nR : ℕ} {full_vals : Vector (ZMod bn254) nF}
    {left_vals : Vector (ZMod bn254) nL} {right_vals : Vector (ZMod bn254) nR}
    {lenL lenR : ZMod bn254}
    (h_bL : ∀ i : Fin nL, left_vals[i].val < 2 ^ 8)
    (h_bR : ∀ i : Fin nR, right_vals[i].val < 2 ^ 8)
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

-- TODO: we could have a crude prob with just d / p
/-- (The challenge under the random oracle) For a fixed instance and a fixed nonzero polynomial
`P` of degree at most `d`, the challenge is a root of `P` with probability at most `(d + 75) / p`
over `H ← randomOracle`.

The `d / p` is Schwartz–Zippel, valid while the challenge query is fresh. The `75 / p` covers its
colliding with one of the queries that hashing the three strings makes:

- `75 = 3 · 25`: one `HashToField.challenge_mem_transcript_le` per hashed string (`left`, `right`, `full`), union-bounded.
- `25 = 5 · 5`: hashing a string's field elements makes at most 5 Poseidon calls, up to 4 chunk
  calls on 16 elements each and the final call on their digests `#v[d₀, …, dₖ₋₁]`. Input `j` of
  the challenge query is the string's hash, so equaling one of these calls `t` forces
  `hash = t.coord j`, which `HashToField.prob_hash_eq_le` bounds by `5 / p`.
- `5 = 1 + 4`: the hash is `f` at the final call. That is `1 / p` while the final call is none of
  the chunk calls, and `1 / p` for each of the 4 chunk calls it could equal, since that forces
  the first digest `d₀` to equal the chunk's first element.

The bound is crude, but it only has to be negligible. -/
theorem prob_challenge_root_le {nF nL nR : ℕ} (full_vals : Vector (ZMod bn254) nF)
    (left_vals : Vector (ZMod bn254) nL) (right_vals : Vector (ZMod bn254) nR)
    (lenL lenR : ZMod bn254) {P : Polynomial (ZMod bn254)} (hP : P ≠ 0) {d : ℕ}
    (hd : P.natDegree ≤ d) :
    randomOracle.toOuterMeasure
      {f | P.eval (challenge (Query.toHashFn f) full_vals left_vals right_vals lenL lenR) = 0} ≤ ((d + 75 : ℕ) : ENNReal) / bn254 := by
  classical
  set vL := HashToField.hashBytesToFieldElems left_vals lenL
  set vR := HashToField.hashBytesToFieldElems right_vals lenR
  set vF := HashToField.hashBytesToFieldElems full_vals (lenL + lenR)
  set c := fun f ↦ challengeQuery f full_vals left_vals right_vals lenL lenR
  set T := fun f ↦ HashToField.transcript f vL ∪ HashToField.transcript f vR ∪
    HashToField.transcript f vF
  have h_ch : ∀ f, challenge (Query.toHashFn f) full_vals left_vals right_vals lenL lenR =
      f (c f) := fun f ↦ RandomOracle.toHashFn_apply f _ (by decide)
  have h_sub :
      {f | P.eval (challenge (Query.toHashFn f) full_vals left_vals right_vals lenL lenR) = 0} ⊆
        (({f | c f ∈ HashToField.transcript f vL} ∪ {f | c f ∈ HashToField.transcript f vR}) ∪
          {f | c f ∈ HashToField.transcript f vF}) ∪
        {f | c f ∉ (T f : Set Query) ∧ P.eval (f (c f)) = 0} := by
    intro f hf
    rw [Set.mem_setOf_eq, h_ch f] at hf
    by_cases h : c f ∈ T f
    · simp only [T, Finset.mem_union] at h
      left
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · exact Or.inr ⟨by simpa using h, hf⟩
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
  have h_fresh := randomOracle_fresh_le c (fun f ↦ ↑(T f)) (fun _ y ↦ P.eval y = 0) d
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
    (fun _ ↦ card_roots_le hP hd)
  calc randomOracle.toOuterMeasure
          {f | P.eval (challenge (Query.toHashFn f) full_vals left_vals right_vals lenL lenR) = 0}
      ≤ ((randomOracle.toOuterMeasure {f | c f ∈ HashToField.transcript f vL} +
            randomOracle.toOuterMeasure {f | c f ∈ HashToField.transcript f vR}) +
            randomOracle.toOuterMeasure {f | c f ∈ HashToField.transcript f vF}) +
          randomOracle.toOuterMeasure {f | c f ∉ (T f : Set Query) ∧ P.eval (f (c f)) = 0} := by
        refine (MeasureTheory.measure_mono h_sub).trans ?_
        refine (MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact MeasureTheory.measure_union_le _ _
    _ ≤ ((25 / bn254 + 25 / bn254) + 25 / bn254) + (d : ENNReal) / bn254 :=
        add_le_add (add_le_add (add_le_add hcL hcR) hcF) h_fresh
    _ = ((d + 75 : ℕ) : ENNReal) / bn254 := by
        simp only [ENNReal.div_add_div_same]
        push_cast
        ring_nf

/-- (Soundness under the random oracle) For a fixed instance that is not a concatenation, the
checks all pass with probability at most `((nF - 1) + (nR - 1) + 75) / p` over
`H ← randomOracle`. Without the padding, or with `ℓL ≥ nF`, nothing passes. Otherwise passing
makes the challenge a root of `concatDiff`, which is nonzero and of degree at most
`(nF - 1) + (nR - 1)`: `prob_challenge_root_le`. -/
theorem prob_checks_le {nF nL nR : ℕ} (hL : nL ≤ nF) (full_vals : Vector (ZMod bn254) nF)
    (left_vals : Vector (ZMod bn254) nL) (right_vals : Vector (ZMod bn254) nR)
    (lenL lenR : ZMod bn254)
    (h_bad : ¬ IsConcat full_vals left_vals right_vals lenL.val) :
    randomOracle.toOuterMeasure
      {f | checks (Query.toHashFn f) full_vals left_vals right_vals lenL lenR} ≤ (((nF - 1) + (nR - 1) + 75 : ℕ) : ENNReal) / bn254 := by
  classical
  by_cases h_pre : (∀ i : Fin nL, lenL.val ≤ i.val → left_vals[i] = 0) ∧ lenL.val < nF
  swap
  · have h_empty :
        {f | checks (Query.toHashFn f) full_vals left_vals right_vals lenL lenR} = ∅ := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hf
      exact h_pre ⟨hf.2.2.2.1.2.2, hf.2.2.2.2.1⟩
    rw [h_empty]
    simp
  obtain ⟨h_pad, h_lt⟩ := h_pre
  have h_D : concatDiff full_vals left_vals right_vals lenL.val ≠ 0 := by
    rw [Ne, concatDiff_eq_zero_iff _ _ _ (ext_pad_of h_pad)]
    exact h_bad
  refine le_trans (MeasureTheory.measure_mono fun f hf ↦ ?_)
    (prob_challenge_root_le full_vals left_vals right_vals lenL lenR h_D
      (natDegree_concatDiff_le _ _ _ hL h_lt))
  rw [Set.mem_setOf_eq, eval_concatDiff, hf.2.2.2.2.2, sub_self]

/-!

`assertIsConcatenation`'s specification: `sound` and `complete`, on strings encoded by
`FString.encodeV`. `convertsM` says the circuit's constraints are `checks H …` for the hash `H` it
computes. These here say what `checks` means for a fixed instance when `H ← randomOracle` (`sound`),
and for every `H` (`complete`). -/

/-- (soundness of `assertIsConcatenation`) When `F ≠ L ++ R`, the checks all pass with
probability at most `((nF - 1) + (nR - 1) + 75) / p`. -/
theorem sound {nF nL nR : ℕ} (hL : nL ≤ nF) {F L R : String}
    (lenR : ZMod bn254)
    (hF : F.length ≤ nF) (hL' : L.length ≤ nL) (hR : R.length ≤ nR) (h_nF : nF < bn254)
    (hFc : ∀ c ∈ F.toList, 0 < c.toNat ∧ c.toNat < 256)
    (hLc : ∀ c ∈ L.toList, 0 < c.toNat ∧ c.toNat < 256)
    (hRc : ∀ c ∈ R.toList, 0 < c.toNat ∧ c.toNat < 256)
    (h_bad : F ≠ L ++ R) :
    randomOracle.toOuterMeasure
      {f | checks (Query.toHashFn f) (encodeV nF F) (encodeV nL L) (encodeV nR R) L.length lenR} ≤ (((nF - 1) + (nR - 1) + 75 : ℕ) : ENNReal) / bn254 := by
  refine prob_checks_le hL _ _ _ _ _ ?_
  rwa [ZMod.val_natCast_of_lt (by omega), isConcat_encodeV_iff (by decide) hF hL' hR hFc hLc hRc]

/-- (completeness of `assertIsConcatenation`) When `F = L ++ R`, with `L` not empty and shorter than `nF`, every check passes, whatever `H` is. -/
theorem complete {H : HashFn} {nF nL nR : ℕ} {F L R : String} (lenR : ZMod bn254)
    (hF : F.length ≤ nF) (hL' : L.length ≤ nL) (hR : R.length ≤ nR) (h_nF : nF < bn254)
    (hLc : ∀ c ∈ L.toList, 0 < c.toNat ∧ c.toNat < 256)
    (hRc : ∀ c ∈ R.toList, 0 < c.toNat ∧ c.toNat < 256)
    (h_pos : 0 < L.length) (h_lt : L.length < nF) (h_cat : F = L ++ R) :
    checks H (encodeV nF F) (encodeV nL L) (encodeV nR R) L.length lenR := by
  have h_l : (L.length : ZMod bn254).val = L.length := ZMod.val_natCast_of_lt (by omega)
  have hFc : ∀ c ∈ F.toList, 0 < c.toNat ∧ c.toNat < 256 := by
    intro c hc
    rw [h_cat, String.toList_append, List.mem_append] at hc
    exact hc.elim (hLc c) (hRc c)
  have h_bytes : ∀ {w : ℕ} {S : String} (i : Fin w),
      ((encodeV (p := bn254) w S)[i]).val < 2 ^ 8 :=
    fun i ↦ lt_of_lt_of_le (encodeV_val_lt i.isLt) (by norm_num)
  refine checks_of_isConcat h_bytes h_bytes h_bytes (by rwa [h_l]) (by rwa [h_l]) (by rwa [h_l])
    ?_
  rw [h_l, isConcat_encodeV_iff (by decide) hF hL' hR hFc hLc hRc]
  exact h_cat

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

end examples

end Clap.Lang.FString
