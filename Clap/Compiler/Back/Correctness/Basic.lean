import CompPoly.Univariate.Basic

variable {p : ℕ} {var : Type} [inst : Fact (Nat.Prime p)] [inst' : Fact (p > 2)]

omit inst' in
lemma ZMod.coeff_mul {f g : Polynomial (ZMod p)} :
    ∀ {i : ℕ},
      ((f * g).coeff i).val =
        (∑ k ∈ Finset.range i.succ, (f.coeff k).val * (g.coeff (i - k)).val) % p := by
  intros i
  simp
    [
      Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ZMod.val_finset_sum,
      ZMod.val_mul, ← Finset.sum_nat_mod
    ]

omit inst' in
lemma ZMod.coeff_add {f g : Polynomial (ZMod p)} :
    ∀ {i : ℕ},
      ((f + g).coeff i).val =
        ((f.coeff i).val + (g.coeff i).val) % p := by
  intros i
  rw [Polynomial.coeff_add, ZMod.val_add]

omit inst' in
lemma mul_no_overflow {b₁ b₂ d₁ d₂ : ℕ} {f g : Polynomial (ZMod p)} :
    b₁ * b₂ * (min d₁ d₂) < p →
    (∀ i, (f.coeff i).val < b₁) →
    (∀ i, (g.coeff i).val < b₂) →
    f.natDegree < d₁ →
    g.natDegree < d₂ →
      ∀ {i : ℕ},
      ((f * g).coeff i).val =
        (∑ k ∈ Finset.range i.succ, (f.coeff (k, i - k).1).val * (g.coeff (k, i - k).2).val) := by
  intros bound_lt_p f_coeff_bound g_coeff_bound f_degree g_degree i
  rw [ZMod.coeff_mul]
  rw [Nat.mod_eq_iff_lt (by grind)]
  apply lt_of_le_of_lt ?_ bound_lt_p
  let sf x := (f.coeff (x, i - x).1).val * (g.coeff (x, i - x).2).val
  let s := (Finset.range i.succ).filter (sf ·  ≠ 0)
  have : (b₁ * b₂) * s.card ≤ (b₁ * b₂) * min d₁ d₂ := by
    apply Nat.mul_le_mul_left _
    dsimp [s, sf]
    have deg_bound_of_coeff_prod_neq : ∀ x, (f.coeff x).val * (g.coeff (i - x)).val ≠ 0 → x < d₁ ∧ i - x < d₂ := by
      intros x h
      rw [Nat.mul_ne_zero_iff, ZMod.val_ne_zero, ZMod.val_ne_zero] at h
      have h₁ := Polynomial.le_natDegree_of_ne_zero h.1
      have h₂ := Polynomial.le_natDegree_of_ne_zero h.2
      grind
    have deg_bound_of_coeff_prod_neq : ∀ x ∈ Finset.range (i + 1), (f.coeff x).val * (g.coeff (i - x)).val ≠ 0 → x < d₁ ∧ i - x < d₂ := by
      intros x _
      exact deg_bound_of_coeff_prod_neq x
    have {α : Type} {s : Finset α} {P Q : α → Prop} [DecidablePred P] [DecidablePred Q] :
        (∀ a ∈ s, P a → Q a) → {a ∈ s | P a}.card ≤ {a ∈ s | Q a}.card := by
      intros h
      apply Finset.card_le_card
      grind
    specialize this deg_bound_of_coeff_prod_neq
    apply le_trans this
    rw [Finset.filter_and]
    have {α : Type} [DecidableEq α] {A B : Finset α} : (A ∩ B).card ≤ min A.card B.card := by
      apply Nat.le_min_of_le_of_le
      · apply Finset.card_le_card ?_
        exact Finset.inter_subset_left
      · apply Finset.card_le_card ?_
        exact Finset.inter_subset_right
    apply le_trans this
    apply inf_le_inf
    · by_cases h : i < d₁
      · have : {a ∈ Finset.range (i + 1) | a < d₁} = Finset.range (i + 1) := by
          simp only [Finset.filter_eq_self, Finset.mem_range, Order.lt_add_one_iff]
          intros e h'
          exact lt_of_le_of_lt h' h
        rw [this]
        simp [h]
      · have : {a ∈ Finset.range (i + 1) | a < d₁} = Finset.range d₁ := by
          ext e
          apply Iff.intro
          · intros h'
            simp only [Finset.mem_filter, Finset.mem_range, Order.lt_add_one_iff] at h' ⊢
            exact h'.2
          · simp only [not_lt] at h
            intros h'
            simp only [Finset.mem_range, Finset.mem_filter, Order.lt_add_one_iff] at h' ⊢
            refine And.intro ?_ h'
            linarith
        rw [this]
        simp
    · by_cases h : i < d₂
      · have : {a ∈ Finset.range (i + 1) | i - a < d₂} = Finset.range (i + 1) := by
          simp
          intros e _
          grind
        rw [this]
        simp [h]
      · simp only [not_lt] at h
        have : {a ∈ Finset.range (i + 1) | i - a < d₂} = Finset.Ico ((i - d₂) + 1) i.succ := by
          ext e
          apply Iff.intro
          · intros h'
            simp only [Finset.mem_filter, Finset.mem_range, Order.lt_add_one_iff,
              Nat.succ_eq_add_one, Finset.mem_Ico, Order.add_one_le_iff] at h' ⊢
            grind
          · intros h'
            simp only [Nat.succ_eq_add_one, Finset.mem_Ico, Order.add_one_le_iff,
              Order.lt_add_one_iff, Finset.mem_filter, Finset.mem_range] at h' ⊢
            grind
        rw [this]
        simp
        grind
  refine le_trans ?_ this
  rw [←Finset.sum_filter_ne_zero]
  dsimp [s, sf]
  apply Finset.sum_le_card_mul_bound
  intros a h
  specialize f_coeff_bound a
  specialize g_coeff_bound (i - a)
  nlinarith

omit inst' in
lemma add_no_overflow {fb gb : ℕ} {f g : Polynomial (ZMod p)} {i : ℕ} :
  fb + gb ≤ p →
  (f.coeff i).val < fb →
  (g.coeff i).val < gb →
    ((f + g).coeff i).val = (f.coeff i).val + (g.coeff i).val := by
  intros h hf hg
  rw [ZMod.coeff_add, Nat.mod_eq_of_lt]
  grind

omit inst' in
lemma mul_coeff_bound {b₁ b₂ d₁ d₂ : ℕ} {f g : Polynomial (ZMod p)} :
    b₁ * b₂ * (min d₁ d₂) < p →
    (∀ i, (f.coeff i).val < b₁) →
    (∀ i, (g.coeff i).val < b₂) →
    f.natDegree < d₁ →
    g.natDegree < d₂ →
    ∀ i, ((f * g).coeff i).val < b₁ * b₂ * (min d₁ d₂)
    := by
  intros h f_bound g_bound f_deg g_deg i
  rw [mul_no_overflow h f_bound g_bound f_deg g_deg, ←Finset.sum_filter_ne_zero]
  let sf x := (f.coeff (x, i - x).1).val * (g.coeff (x, i - x).2).val
  let s := (Finset.range i.succ).filter (sf ·  ≠ 0)
  have : (b₁ * b₂) * s.card ≤ (b₁ * b₂) * min d₁ d₂ := by
    apply Nat.mul_le_mul_left _
    dsimp [s, sf]
    have deg_bound_of_coeff_prod_neq : ∀ x, (f.coeff x).val * (g.coeff (i - x)).val ≠ 0 → x < d₁ ∧ i - x < d₂ := by
      intros x h
      rw [Nat.mul_ne_zero_iff, ZMod.val_ne_zero, ZMod.val_ne_zero] at h
      have h₁ := Polynomial.le_natDegree_of_ne_zero h.1
      have h₂ := Polynomial.le_natDegree_of_ne_zero h.2
      grind
    have deg_bound_of_coeff_prod_neq : ∀ x ∈ Finset.range (i + 1), (f.coeff x).val * (g.coeff (i - x)).val ≠ 0 → x < d₁ ∧ i - x < d₂ := by
      intros x _
      exact deg_bound_of_coeff_prod_neq x
    have {α : Type} {s : Finset α} {P Q : α → Prop} [DecidablePred P] [DecidablePred Q] :
        (∀ a ∈ s, P a → Q a) → {a ∈ s | P a}.card ≤ {a ∈ s | Q a}.card := by
      intros h
      apply Finset.card_le_card
      grind
    specialize this deg_bound_of_coeff_prod_neq
    apply le_trans this
    rw [Finset.filter_and]
    have {α : Type} [DecidableEq α] {A B : Finset α} : (A ∩ B).card ≤ min A.card B.card := by
      apply Nat.le_min_of_le_of_le
      · apply Finset.card_le_card ?_
        exact Finset.inter_subset_left
      · apply Finset.card_le_card ?_
        exact Finset.inter_subset_right
    apply le_trans this
    apply inf_le_inf
    · by_cases h : i < d₁
      · have : {a ∈ Finset.range (i + 1) | a < d₁} = Finset.range (i + 1) := by
          simp only [Finset.filter_eq_self, Finset.mem_range, Order.lt_add_one_iff]
          intros e h'
          exact lt_of_le_of_lt h' h
        rw [this]
        simp [h]
      · have : {a ∈ Finset.range (i + 1) | a < d₁} = Finset.range d₁ := by
          ext e
          apply Iff.intro
          · intros h'
            simp only [Finset.mem_filter, Finset.mem_range, Order.lt_add_one_iff] at h' ⊢
            exact h'.2
          · simp only [not_lt] at h
            intros h'
            simp only [Finset.mem_range, Finset.mem_filter, Order.lt_add_one_iff] at h' ⊢
            refine And.intro ?_ h'
            linarith
        rw [this]
        simp
    · by_cases h : i < d₂
      · have : {a ∈ Finset.range (i + 1) | i - a < d₂} = Finset.range (i + 1) := by
          simp
          intros e _
          grind
        rw [this]
        simp [h]
      · simp only [not_lt] at h
        have : {a ∈ Finset.range (i + 1) | i - a < d₂} = Finset.Ico ((i - d₂) + 1) i.succ := by
          ext e
          apply Iff.intro
          · intros h'
            simp only [Finset.mem_filter, Finset.mem_range, Order.lt_add_one_iff,
              Nat.succ_eq_add_one, Finset.mem_Ico, Order.add_one_le_iff] at h' ⊢
            grind
          · intros h'
            simp only [Nat.succ_eq_add_one, Finset.mem_Ico, Order.add_one_le_iff,
              Order.lt_add_one_iff, Finset.mem_filter, Finset.mem_range] at h' ⊢
            grind
        rw [this]
        simp
        grind
  by_cases h'' : s = ∅
  · dsimp [s, sf] at h''
    rw [h'']
    simp
    specialize f_bound 0
    specialize g_bound 0
    grind
  · refine lt_of_lt_of_le ?_ this
    apply Finset.sum_lt_card_mul_bound h''
    · specialize f_bound 0
      specialize g_bound 0
      apply Nat.mul_pos (Nat.zero_lt_of_lt f_bound) (Nat.zero_lt_of_lt g_bound)
    · intros a h
      specialize f_bound a
      specialize g_bound (i - a)
      simp only
      exact Nat.mul_lt_mul'' f_bound g_bound

omit inst' in
lemma add_coeff_bound {fb gb : ℕ} {f g : Polynomial (ZMod p)} {i : ℕ} :
  fb + gb ≤ p →
  (f.coeff i).val < fb →
  (g.coeff i).val < gb →
    ((f + g).coeff i).val < fb + gb := by
  intros h hf hg
  rw [add_no_overflow h hf hg]
  grind
