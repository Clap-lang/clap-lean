import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Clap.Model.Convert.PaddedVector

/-!
# The polynomial identities (Fiat–Shamir)

Circom's `IsSubstring` and `AssertIsConcatenation`read each byte array as the coefficients of a polynomial, evaluate those polynomials at one
challenge `α`, and check one identity at `α`:

- substring: `ŝ(α) = α^s · t(α)`, with `ŝ` the window `[s, e)` of `str` and `t` the substring;
- concatenation: `full(α) = left(α) + α^ℓ · right(α)`.

Vectors are compared through `ext v i`, their zero extension, so no index bounds appear.
-/

open Polynomial

namespace Clap.FiatShamir

variable {p : ℕ}

/-- The zero extension of `v`: `v[i]` inside, `0` beyond. -/
def ext {n : ℕ} (v : Vector (ZMod p) n) (i : ℕ) : ZMod p := (v[i]?).getD 0

lemma ext_of_lt {n : ℕ} (v : Vector (ZMod p) n) {i : ℕ} (h : i < n) : ext v i = v[i] := by
  simp [ext, h]

lemma ext_of_le {n : ℕ} (v : Vector (ZMod p) n) {i : ℕ} (h : n ≤ i) : ext v i = 0 := by
  simp [ext, show ¬ i < n by omega]

/-- `Σ v[i] · Xⁱ`. -/
noncomputable def vecPoly {n : ℕ} (v : Vector (ZMod p) n) : (ZMod p)[X] :=
  ∑ i : Fin n, C v[i] * X ^ (i : ℕ)

/-- `Σ v[i] · αⁱ`, what `dotProduct v (powers α n)` computes. -/
def evalAt {n : ℕ} (v : Vector (ZMod p) n) (α : ZMod p) : ZMod p :=
  ∑ i : Fin n, v[i] * α ^ (i : ℕ)

lemma coeff_vecPoly {n : ℕ} (v : Vector (ZMod p) n) (m : ℕ) : (vecPoly v).coeff m = ext v m := by
  unfold vecPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases h : m < n
  · rw [Finset.sum_eq_single ⟨m, h⟩]
    · simp [ext_of_lt v h]
    · intro i _ hi
      have : m ≠ i.val := fun h' ↦ hi (Fin.ext h'.symm)
      simp [this]
    · simp
  · rw [ext_of_le v (by omega)]
    apply Finset.sum_eq_zero
    intro i _
    have : m ≠ i.val := by omega
    simp [this]

lemma eval_vecPoly {n : ℕ} (v : Vector (ZMod p) n) (α : ZMod p) :
    (vecPoly v).eval α = evalAt v α := by
  simp [vecPoly, evalAt, eval_finsetSum]

lemma natDegree_vecPoly_le {n : ℕ} (v : Vector (ZMod p) n) : (vecPoly v).natDegree ≤ n - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_vecPoly, ext_of_le v]
  have : n - 1 < N := by exact_mod_cast hN
  omega

lemma coeff_X_pow_mul_vecPoly {n : ℕ} (v : Vector (ZMod p) n) (s m : ℕ) :
    (X ^ s * vecPoly v).coeff m = if s ≤ m then ext v (m - s) else 0 := by
  rw [coeff_X_pow_mul', coeff_vecPoly]

lemma natDegree_X_pow_mul_vecPoly_le {n : ℕ} (v : Vector (ZMod p) n) (s : ℕ) :
    (X ^ s * vecPoly v).natDegree ≤ s + (n - 1) := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  have hN' : s + (n - 1) < N := by exact_mod_cast hN
  rw [coeff_X_pow_mul_vecPoly]
  split
  · rw [ext_of_le v (by omega)]
  · rfl

/-! ## Substring -/

section substring

variable {n m : ℕ}

/-- The window `[s, e)` of `str`, as the circuit selects it: `ArraySelector`'s bit at `i` is
`(s ≤ i) xor (e ≤ i)`, which is the interval once `s ≤ e`, and the selected string is that bit
times `str[i]`. -/
def window (str : Vector (ZMod p) n) (s e : ℕ) : Vector (ZMod p) n :=
  Vector.ofFn fun i ↦ if (decide (s ≤ i.val) ^^ decide (e ≤ i.val)) then str[i] else 0

lemma ext_window (str : Vector (ZMod p) n) {s e : ℕ} (h : s ≤ e) (i : ℕ) :
    ext (window str s e) i = if s ≤ i ∧ i < e then ext str i else 0 := by
  by_cases hi : i < n
  · rw [ext_of_lt _ hi, ext_of_lt _ hi]
    simp only [window, Vector.getElem_ofFn]
    by_cases h1 : s ≤ i <;> by_cases h2 : e ≤ i <;> simp [h1, h2]; omega
  · rw [ext_of_le _ (by omega), ext_of_le _ (by omega)]
    simp

/-- `substr` occurs in `str` at `s`, for length `ℓ`. The window
`[s, s + ℓ)` of `str` (zero past its end), shifted to `0`, is `substr` zero-extended.

Unfolded, this says `substr[j] = str[s + j]` for `j < ℓ` with `s + j` inside `str`, that
`substr` is `0` after `ℓ`, and wherever the window runs past the end of `str`, and that `str` is
`0` wherever the window runs past the end of `substr`. -/
def SubstrAt (str : Vector (ZMod p) n) (substr : Vector (ZMod p) m) (s ℓ : ℕ) : Prop :=
  ∀ i : ℕ, (if s ≤ i ∧ i < s + ℓ then ext str i else 0) =
    (if s ≤ i then ext substr (i - s) else 0)

/-- The polynomial the substring check tests at `α`: window minus shifted substring. -/
noncomputable def substrDiff (str : Vector (ZMod p) n) (substr : Vector (ZMod p) m) (s e : ℕ) :
    (ZMod p)[X] :=
  vecPoly (window str s e) - X ^ s * vecPoly substr

lemma substrDiff_eq_zero_iff (str : Vector (ZMod p) n) (substr : Vector (ZMod p) m)
    {s ℓ : ℕ} :
    substrDiff str substr s (s + ℓ) = 0 ↔ SubstrAt str substr s ℓ := by
  rw [substrDiff, sub_eq_zero, Polynomial.ext_iff]
  simp only [coeff_vecPoly, coeff_X_pow_mul_vecPoly, ext_window str (show s ≤ s + ℓ by omega)]
  rfl

lemma eval_substrDiff (str : Vector (ZMod p) n) (substr : Vector (ZMod p) m) (s e : ℕ)
    (α : ZMod p) :
    (substrDiff str substr s e).eval α =
      evalAt (window str s e) α - α ^ s * evalAt substr α := by
  simp [substrDiff, eval_vecPoly]

lemma natDegree_substrDiff_le (str : Vector (ZMod p) n) (substr : Vector (ZMod p) m)
    {s e : ℕ} (hs : s < n) :
    (substrDiff str substr s e).natDegree ≤ (n - 1) + (m - 1) := by
  unfold substrDiff
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (natDegree_vecPoly_le _).trans (by omega)
  · exact (natDegree_X_pow_mul_vecPoly_le _ _).trans (by omega)

/-- (Completeness of the identity) when `substr` occurs at `s`, the check's two sides agree at
every `α`. -/
lemma evalAt_window_of_substrAt {str : Vector (ZMod p) n} {substr : Vector (ZMod p) m}
    {s ℓ : ℕ} (h : SubstrAt str substr s ℓ) (α : ZMod p) :
    evalAt (window str s (s + ℓ)) α = α ^ s * evalAt substr α := by
  have h0 := (substrDiff_eq_zero_iff str substr).mpr h
  have := congrArg (Polynomial.eval α) h0
  rw [eval_substrDiff] at this
  simpa [sub_eq_zero] using this

end substring

/-! ## Concatenation -/

section concatenation

variable {nF nL nR : ℕ}

/-- `full` is `left` (zero-padded after `ℓ`) followed by `right`.
`left` is `0` from `ℓ` on, and every position of `full`, zero-extended, is `left`'s plus
`right`'s shifted to start at `ℓ`.

`right` is compared in full, including padding. The identity pins every entry of `right` that
lands inside `full`, and makes those past the end of `full` zero. Its length enters only the
hashes -/
def IsConcat (full : Vector (ZMod p) nF) (left : Vector (ZMod p) nL) (right : Vector (ZMod p) nR)
    (ℓ : ℕ) : Prop :=
  (∀ i, ℓ ≤ i → ext left i = 0) ∧
  ∀ i, ext full i = ext left i + (if ℓ ≤ i then ext right (i - ℓ) else 0)

/-- The polynomial the concatenation check tests at `α`. -/
noncomputable def concatDiff (full : Vector (ZMod p) nF) (left : Vector (ZMod p) nL)
    (right : Vector (ZMod p) nR) (ℓ : ℕ) : (ZMod p)[X] :=
  vecPoly full - (vecPoly left + X ^ ℓ * vecPoly right)

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

end concatenation

/-! ## Counting accepting challenges -/

/-- A nonzero polynomial of degree at most `d` vanishes at no more than `d` points -/
lemma card_roots_le [Fact (Nat.Prime p)] {P : (ZMod p)[X]} (hP : P ≠ 0) {d : ℕ}
    (hd : P.natDegree ≤ d) :
    (Finset.univ.filter fun α : ZMod p ↦ P.eval α = 0).card ≤ d := by
  classical
  calc (Finset.univ.filter fun α : ZMod p ↦ P.eval α = 0).card
      ≤ P.roots.toFinset.card := by
        apply Finset.card_le_card
        intro α hα
        simp only [Finset.mem_filter] at hα
        simp [Multiset.mem_toFinset, mem_roots hP, IsRoot, hα.2]
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ ≤ d := hd


/-! ## On strings

`SubstrAt` and `IsConcat` are about zero-extended vectors. For strings encoded by
`FString.encodeV`, one byte per character, they are the string statements, provided no character
is NUL: otherwise zero padding could stand in for one. -/

section strings

open Clap.Lang

/-- The byte a character is encoded as. -/
private lemma byte_eq {c : Char} (h : c.toNat < 256) : c.toUInt8.toNat = c.toNat := by
  show (c.val.toUInt8).toNat = c.val.toNat
  rw [UInt32.toNat_toUInt8]
  exact Nat.mod_eq_of_lt h

private lemma natCast_inj {a b : ℕ} (ha : a < p) (hb : b < p) (h : (a : ZMod p) = (b : ZMod p)) :
    a = b := by
  haveI : NeZero p := ⟨by omega⟩
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

lemma ext_encodeV {w : ℕ} {S : String} (hS : S.length ≤ w) (i : ℕ) :
    ext (FString.encodeV (p := p) w S) i =
      if h : i < S.toList.length then (((S.toList[i]'h).toUInt8.toNat : ℕ) : ZMod p) else 0 := by
  by_cases hi : i < w
  · rw [ext_of_lt _ hi]
    simp [FString.encodeV]
  · rw [ext_of_le _ (by omega)]
    have : ¬ i < S.toList.length := by rw [String.length_toList]; omega
    simp [this]

/-- A window of `L` read as a list: `M` sits in `L` at `s`, position by position. -/
private lemma list_window_iff {α : Type} (L M : List α) (s : ℕ) (hM : 0 < M.length) :
    (∀ j (hj : j < M.length), ∃ h : s + j < L.length, L[s + j] = M[j]) ↔
      s + M.length ≤ L.length ∧ M = (L.drop s).take M.length := by
  constructor
  · intro h
    have h_len : s + M.length ≤ L.length := by
      obtain ⟨hlt, -⟩ := h (M.length - 1) (by omega)
      omega
    refine ⟨h_len, ?_⟩
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop]; omega
    · intro j h1 h2
      obtain ⟨hlt, heq⟩ := h j h1
      rw [List.getElem_take, List.getElem_drop, heq]
  · rintro ⟨h_len, h_eq⟩ j hj
    refine ⟨by omega, ?_⟩
    have h1 : j < ((L.drop s).take M.length).length := by
      simp only [List.length_take, List.length_drop]; omega
    have := List.getElem_of_eq h_eq hj
    rw [this, List.getElem_take, List.getElem_drop]

/-- For strings encoded by `FString.encodeV`, `SubstrAt` is the statement: `T` fits in
`S` at `s` and is a prefix of what follows. `T` has no NUL character, so that `S`'s zero padding
cannot stand in for it. -/
theorem substrAt_encodeV_iff {n m s : ℕ} {S T : String} (hp : 256 < p)
    (hS : S.length ≤ n) (hT : T.length ≤ m) (hT0 : 0 < T.length)
    (hSc : ∀ c ∈ S.toList, c.toNat < 256) (hTc : ∀ c ∈ T.toList, 0 < c.toNat ∧ c.toNat < 256) :
    SubstrAt (FString.encodeV (p := p) n S) (FString.encodeV (p := p) m T) s T.length ↔
      s + T.length ≤ S.length ∧ T.toList <+: S.toList.drop s := by
  -- 1. the identity is pointwise on the window
  have step1 : SubstrAt (FString.encodeV (p := p) n S) (FString.encodeV (p := p) m T) s T.length ↔
      ∀ j < T.length, ext (FString.encodeV (p := p) n S) (s + j) =
        ext (FString.encodeV (p := p) m T) j := by
    constructor
    · intro h j hj
      have := h (s + j)
      simp only [show s ≤ s + j by omega, show s + j < s + T.length by omega, and_self, if_true,
        Nat.add_sub_cancel_left] at this
      exact this
    · intro h i
      by_cases hsi : s ≤ i
      · obtain ⟨j, rfl⟩ : ∃ j, i = s + j := ⟨i - s, by omega⟩
        simp only [hsi, true_and, if_true, Nat.add_sub_cancel_left]
        by_cases hj : j < T.length
        · rw [if_pos (by omega), h j hj]
        · rw [if_neg (by omega), ext_encodeV hT, dif_neg (by rw [String.length_toList]; omega)]
      · simp [hsi]
  -- 2. each position: the substring's byte is nonzero, so `S` must have the same character there
  have step2 : ∀ j (hj : j < T.length), (ext (FString.encodeV (p := p) n S) (s + j) =
      ext (FString.encodeV (p := p) m T) j ↔
      ∃ h : s + j < S.toList.length,
        S.toList[s + j] = T.toList[j]'(by rw [String.length_toList]; exact hj)) := by
    intro j hj
    have hjT : j < T.toList.length := by rw [String.length_toList]; exact hj
    have hTj := hTc _ (List.getElem_mem hjT)
    rw [ext_encodeV hS, ext_encodeV hT, dif_pos hjT, byte_eq hTj.2]
    by_cases hsj : s + j < S.toList.length
    · have hSj := hSc _ (List.getElem_mem hsj)
      rw [dif_pos hsj, byte_eq hSj]
      constructor
      · intro heq
        refine ⟨hsj, Char.ext (UInt32.toNat.inj ?_)⟩
        exact natCast_inj (a := (S.toList[s + j]).toNat) (b := (T.toList[j]).toNat)
          (by omega) (by omega) heq
      · rintro ⟨_, heq⟩
        rw [heq]
    · rw [dif_neg hsj]
      simp only [hsj, IsEmpty.exists_iff, iff_false]
      intro h0
      have := natCast_inj (p := p) (a := 0) (b := (T.toList[j]).toNat) (by omega) (by omega)
        (by rw [Nat.cast_zero]; exact h0)
      omega
  -- 3. the pointwise statement is the prefix statement
  rw [step1]
  have step12 := (show (∀ j < T.length, ext (FString.encodeV (p := p) n S) (s + j) =
        ext (FString.encodeV (p := p) m T) j) ↔ _ from
      ⟨fun h j hj ↦ (step2 j hj).mp (h j hj), fun h j hj ↦ (step2 j hj).mpr (h j hj)⟩)
  rw [step12, List.prefix_iff_eq_take]
  exact list_window_iff S.toList T.toList s hT0

/-- A list of characters, one byte each, zero-extended. -/
def zext (l : List Char) (i : ℕ) : ZMod p :=
  if h : i < l.length then (((l[i]'h).toUInt8.toNat : ℕ) : ZMod p) else 0

lemma ext_encodeV_eq_zext {w : ℕ} {S : String} (hS : S.length ≤ w) (i : ℕ) :
    ext (FString.encodeV (p := p) w S) i = zext S.toList i := by
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
    rw [zext, dif_pos hi, byte_eq (hl _ (List.getElem_mem hi)).2] at h0
    have := natCast_inj (p := p) (a := (l[i]).toNat) (b := 0) (by have := (hl _ (List.getElem_mem hi)).2; omega)
      (by omega) (by rw [Nat.cast_zero]; exact h0)
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
  rw [zext, zext, dif_pos hi₁, dif_pos hi₂, byte_eq (h₁ _ (List.getElem_mem hi₁)).2,
    byte_eq (h₂ _ (List.getElem_mem hi₂)).2] at this
  exact Char.ext (UInt32.toNat.inj (natCast_inj (a := (l₁[i]).toNat) (b := (l₂[i]).toNat)
    (by have := (h₁ _ (List.getElem_mem hi₁)).2; omega)
    (by have := (h₂ _ (List.getElem_mem hi₂)).2; omega) this))

/-- For strings encoded by `FString.encodeV`, `IsConcat` at `ℓ = left.length` is string
concatenation. The characters are bytes with no NUL, so that zero padding cannot stand in for one.
`left`'s padding holds automatically. -/
theorem isConcat_encodeV_iff {nF nL nR : ℕ} {F L R : String} (hp : 256 < p)
    (hF : F.length ≤ nF) (hL : L.length ≤ nL) (hR : R.length ≤ nR)
    (hFc : ∀ c ∈ F.toList, 0 < c.toNat ∧ c.toNat < 256)
    (hLc : ∀ c ∈ L.toList, 0 < c.toNat ∧ c.toNat < 256)
    (hRc : ∀ c ∈ R.toList, 0 < c.toNat ∧ c.toNat < 256) :
    IsConcat (FString.encodeV (p := p) nF F) (FString.encodeV (p := p) nL L)
      (FString.encodeV (p := p) nR R) L.length ↔ F = L ++ R := by
  unfold IsConcat
  have h_pad : ∀ i, L.length ≤ i → ext (FString.encodeV (p := p) nL L) i = 0 := by
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

end strings

end Clap.FiatShamir
