import Clap.Util.Wheels

variable {p : ℕ}

@[simp, grind =]
lemma limbsToNat_nil {w : ℕ} : limbsToNat (p := p) w [] = 0 := rfl

@[simp, grind =]
lemma limbsToNat_cons {w : ℕ} {x : ZMod p} {xs : List (ZMod p)} :
  limbsToNat w (x :: xs) = x.val + 2 ^ w * limbsToNat w xs := rfl

@[simp, grind =]
lemma natToLimbs_zero {w n : ℕ} : natToLimbs (p := p) w 0 n = [] := rfl

@[grind =]
lemma natToLimbs_succ {w k n : ℕ} :
  natToLimbs (p := p) w (k + 1) n = ((n % 2 ^ w : ℕ) : ZMod p) :: natToLimbs w k (n / 2 ^ w) := rfl

@[simp, grind =]
lemma toList_natToLimbsV {w k n : ℕ} : (natToLimbsV p w k n).toList = natToLimbs w k n := rfl

lemma limbsToNat_eq_ofDigits (w : ℕ) (l : List (ZMod p)) :
  limbsToNat w l = Nat.ofDigits (2 ^ w) (l.map ZMod.val)
:= by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [Nat.ofDigits_cons, ih]

lemma limbsToNat_append {w : ℕ} (l₁ l₂ : List (ZMod p)) :
  limbsToNat w (l₁ ++ l₂) = limbsToNat w l₁ + 2 ^ (w * l₁.length) * limbsToNat w l₂
:= by
  induction l₁ with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, limbsToNat_cons, ih, List.length_cons, Nat.mul_succ, pow_add]
    ring

/-- `limbsToNat` as the positional sum `fpMulPureV` uses. -/
lemma limbsToNat_eq_sum {w : ℕ} (l : List (ZMod p)) :
  limbsToNat w l = ∑ i : Fin l.length, l[i].val * (2 ^ w) ^ i.val
:= by
  induction l with
  | nil => simp
  | cons x xs ih =>
    show _ = ∑ i : Fin (xs.length + 1), (x :: xs)[i].val * (2 ^ w) ^ i.val
    rw [limbsToNat_cons, ih, Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.getElem_fin,
      List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ, pow_succ]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring

lemma limbsToNat_toList_eq_sum {w k : ℕ} (v : Vector (ZMod p) k) :
  limbsToNat w v.toList = ∑ i : Fin k, v[i].val * (2 ^ w) ^ i.val
:= by
  rw [limbsToNat_eq_sum]
  exact Fin.sum_congr' (fun i : Fin k ↦ v[i].val * (2 ^ w) ^ i.val) (by simp)

/-- Every limb `natToLimbs` produces is below `2^w`, whatever `p` is: `.val` of a cast never
exceeds the natural number cast. -/
lemma val_lt_of_mem_natToLimbs {w k n : ℕ} :
  ∀ x ∈ natToLimbs (p := p) w k n, x.val < 2 ^ w
:= by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    intro x hx
    rw [natToLimbs_succ, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [ZMod.val_natCast]
      exact lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by positivity))
    · exact ih x hx

@[simp]
lemma val_natToLimbsV_lt {w k n i : ℕ} (h_i : i < k) : (natToLimbsV p w k n)[i].val < 2 ^ w := by
  have := val_lt_of_mem_natToLimbs (p := p) (w := w) (k := k) (n := n) _
    (List.getElem_mem (l := natToLimbs w k n) (n := i) (by simpa using h_i))
  simpa [natToLimbsV] using this

private lemma two_pow_mul_succ {w k : ℕ} : 2 ^ (w * (k + 1)) = 2 ^ w * 2 ^ (w * k) := by
  rw [Nat.mul_succ, pow_add, mul_comm]

/-- `natToLimbs` only sees `n` modulo `2^(w*k)`, for every `p`. -/
lemma natToLimbs_mod {w k n : ℕ} :
  natToLimbs (p := p) w k (n % 2 ^ (w * k)) = natToLimbs w k n
:= by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [natToLimbs_succ, natToLimbs_succ, two_pow_mul_succ, Nat.mod_mul_right_div_self, ih,
      Nat.mod_mul_right_mod]

lemma natToLimbs_congr {w k a b : ℕ} (h : a % 2 ^ (w * k) = b % 2 ^ (w * k)) :
  natToLimbs (p := p) w k a = natToLimbs w k b
:= by
  rw [← natToLimbs_mod, h, natToLimbs_mod]

/-- Decoding an encoding returns `n % 2^(w*k)` once no limb can wrap the field. -/
lemma limbsToNat_natToLimbs {w k n : ℕ} (hp : 2 ^ w ≤ p) :
  limbsToNat w (natToLimbs (p := p) w k n) = n % 2 ^ (w * k)
:= by
  induction k generalizing n with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [natToLimbs_succ, limbsToNat_cons, ih, ZMod.val_natCast,
      Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) hp), two_pow_mul_succ,
      Nat.mod_mul]

lemma limbsToNat_lt {w : ℕ} {l : List (ZMod p)} (h : ∀ x ∈ l, x.val < 2 ^ w) :
  limbsToNat w l < 2 ^ (w * l.length)
:= by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs := ih (fun y hy ↦ h y (by simp [hy]))
    rw [limbsToNat_cons, List.length_cons, two_pow_mul_succ]
    calc x.val + 2 ^ w * limbsToNat w xs
        < 2 ^ w + 2 ^ w * limbsToNat w xs := by omega
      _ = 2 ^ w * (limbsToNat w xs + 1) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * xs.length) := Nat.mul_le_mul_left _ hxs

lemma limbsToNat_toList_lt {w k : ℕ} {v : Vector (ZMod p) k} (h : ∀ i : Fin k, v[i].val < 2 ^ w) :
  limbsToNat w v.toList < 2 ^ (w * k)
:= by
  have := limbsToNat_lt (w := w) (l := v.toList) (by
    intro x hx
    obtain ⟨i, h_i, rfl⟩ := List.getElem_of_mem hx
    simpa using h ⟨i, by simpa using h_i⟩)
  simpa using this

/-- Re-encoding a decoded in-range limb list gives it back. -/
lemma natToLimbs_limbsToNat [NeZero p] {w : ℕ} {l : List (ZMod p)}
  (h : ∀ x ∈ l, x.val < 2 ^ w) :
  natToLimbs w l.length (limbsToNat w l) = l
:= by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    rw [List.length_cons, natToLimbs_succ, limbsToNat_cons, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hx, ZMod.natCast_zmod_val,
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add,
      ih (fun y hy ↦ h y (by simp [hy]))]

lemma natToLimbs_append {w k₁ k₂ n m : ℕ} (hn : n < 2 ^ (w * k₁)) :
  natToLimbs (p := p) w (k₁ + k₂) (n + 2 ^ (w * k₁) * m) = natToLimbs w k₁ n ++ natToLimbs w k₂ m
:= by
  induction k₁ generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    simp [this]
  | succ k₁ ih =>
    rw [Nat.succ_add, natToLimbs_succ, natToLimbs_succ, List.cons_append, two_pow_mul_succ,
      mul_assoc, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ (by positivity),
      ih (by rw [two_pow_mul_succ] at hn; exact Nat.div_lt_of_lt_mul hn)]

/-- A limb-by-limb equality check against `l` pins `n` down to the number `l` encodes. -/
lemma natToLimbs_eq_iff {w k n : ℕ} {l : List (ZMod p)} (hl : l.length = k)
  (hn : n < 2 ^ (w * k)) (hp : 2 ^ w ≤ p) :
  natToLimbs w k n = l ↔ (∀ x ∈ l, x.val < 2 ^ w) ∧ n = limbsToNat w l
:= by
  constructor
  · rintro rfl
    exact ⟨val_lt_of_mem_natToLimbs, by rw [limbsToNat_natToLimbs hp, Nat.mod_eq_of_lt hn]⟩
  · rintro ⟨h, rfl⟩
    subst hl
    have : NeZero p := ⟨by have := Nat.one_le_two_pow (n := w); omega⟩
    exact natToLimbs_limbsToNat h

/-- The lexicographic step: with the low limbs in range, the order of two numbers is decided by
their high parts, and by the low limbs when those agree. -/
lemma limbsToNat_cons_lt_iff {w : ℕ} {a b : ZMod p} {as bs : List (ZMod p)}
  (ha : a.val < 2 ^ w) (hb : b.val < 2 ^ w) :
  limbsToNat w (a :: as) < limbsToNat w (b :: bs) ↔
    limbsToNat w as < limbsToNat w bs ∨ (limbsToNat w as = limbsToNat w bs ∧ a.val < b.val)
:= by
  rw [limbsToNat_cons, limbsToNat_cons]
  generalize limbsToNat w as = A, limbsToNat w bs = B
  have hc : 0 < 2 ^ w := by positivity
  generalize 2 ^ w = c at *
  rcases lt_trichotomy A B with h | rfl | h
  · have : c * A + c ≤ c * B := by nlinarith
    exact ⟨fun _ ↦ Or.inl h, fun _ ↦ by omega⟩
  · simp
  · have : c * B + c ≤ c * A := by nlinarith
    constructor
    · intro; omega
    · rintro (h' | ⟨h', _⟩) <;> omega

lemma limbsToNat_cons_eq_iff {w : ℕ} {a b : ZMod p} {as bs : List (ZMod p)}
  (ha : a.val < 2 ^ w) (hb : b.val < 2 ^ w) :
  limbsToNat w (a :: as) = limbsToNat w (b :: bs) ↔
    limbsToNat w as = limbsToNat w bs ∧ a.val = b.val
:= by
  have h₁ := limbsToNat_cons_lt_iff (as := as) (bs := bs) ha hb
  have h₂ := limbsToNat_cons_lt_iff (as := bs) (bs := as) hb ha
  constructor
  · intro h
    rw [h] at h₁ h₂
    have := h₁.not.mp (lt_irrefl _)
    have := h₂.not.mp (lt_irrefl _)
    omega
  · rintro ⟨h, h'⟩
    rw [limbsToNat_cons, limbsToNat_cons, h, h']
