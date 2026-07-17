import Clap.Compiler.Back.Cs
import Clap.Compiler.Back.IsZero
import Clap.Compiler.Back.Wg

namespace Clap.Num2Bits

variable {p : ℕ} {var : Type} [inst : Fact (Nat.Prime p)] [inst' : Fact (p > 2)]

section Cs

def assert_bit_e (b : var) (rest : Cs p var) : Cs p var :=
  .eq0 (.v b * (.c 1 - .v b)) rest

omit inst' in
lemma assert_bit_e_spec {b : ZMod p} {rest : Cs p (ZMod p)} :
    (assert_bit_e b rest).eval = if b = 0 ∨ b = 1 then rest.eval else denotation.n := by
  unfold assert_bit_e
  rewrite (occs := .pos [1]) [Cs.eval]
  have : (Exp.v b * (Exp.c 1 - Exp.v b)).eval = 0 ↔ (b = 0 ∨ b = 1) := by
    simp only [Exp.eval]
    simp
    have : 1 - b = 0 ↔ b = 1 := by
      rw [sub_eq_iff_eq_add, zero_add]
      aesop
    aesop (add simp sub_eq_zero)
  grind

def assert_bits_e (bs : List var) (rest : Cs p var) : Cs p var :=
  List.foldr assert_bit_e rest bs

omit inst' in
lemma assert_bits_e_spec {bs : List (ZMod p)} {rest : Cs p (ZMod p)} :
    (assert_bits_e bs rest).eval =
      if (∀ i : Fin bs.length, bs[i] = 0 ∨ bs[i] = 1)
      then rest.eval
      else denotation.n := by
  unfold assert_bits_e
  induction bs with
  | nil => simp
  | cons l ls ih =>
    simp only [List.foldr_cons, List.length_cons]
    split_ifs with h
    · have h₁ : l = 0 ∨ l = 1 := by
        specialize h 0
        simpa using h
      have h₂ : ∀ (i : Fin ls.length), ls.get i = 0 ∨ ls.get i = 1 := by
        intros i
        specialize h i.succ
        simp only [Fin.getElem_fin, Fin.val_succ, List.getElem_cons_succ] at h
        exact h
      simp only [assert_bit_e_spec, h₁, ↓reduceIte, ih]
      split_ifs with h'
      · rfl
      · exfalso; apply h'; exact h₂
    · rw [assert_bit_e_spec, ih]
      split_ifs with h' h''
      · exfalso
        simp only [not_forall, not_or] at h
        rcases h with ⟨i', h⟩
        match i' with
        | ⟨0, _⟩ =>
          simp only [Fin.zero_eta, Fin.getElem_fin, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
            List.getElem_cons_zero] at h
          tauto
        | ⟨.succ i', i'_lt⟩ =>
          simp only [Nat.succ_eq_add_one] at h
          specialize h'' ⟨i', by linarith⟩
          tauto
      · rfl
      · rfl

def assert_bits (args : List (ZMod p)) : Bool :=
  List.all args (fun (x : ZMod p) => x == 0 ∨ x == 1)

omit inst' in
lemma assert_bits_spec (args : List (ZMod p)) :
  assert_bits args ↔ ∀ i : Fin args.length, args[i] = 0 ∨ args[i] = 1 := by
    apply Iff.intro
    · intros h i
      unfold assert_bits at h
      simp only [beq_iff_eq, Bool.decide_or, List.all_eq_true, Bool.or_eq_true,
        decide_eq_true_eq] at h
      exact h _ (by simp)
    · intros h
      unfold assert_bits
      simp only [beq_iff_eq, Bool.decide_or, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]
      intros x h'
      rcases List.mem_iff_get.mp h' with ⟨i, h'⟩
      rw [←h']
      exact h i



omit inst' in
lemma assert_bits_of_num2bits {w : ℕ} {v : ZMod p} : assert_bits (num2bitsLsbPure w v) := by
  revert v
  induction w with
  | zero =>
    simp [num2bitsLsbPure, assert_bits]
  | succ w ih =>
    intros v
    unfold num2bitsLsbPure
    unfold assert_bits at ih ⊢
    simp only [beq_iff_eq, Bool.decide_or, List.all_cons, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, List.all_eq_true] at ih ⊢
    refine And.intro ?_ ih
    rcases Nat.mod_two_eq_zero_or_one v.val with h | h <;> simp [h]

lemma bits2num_val_lt_2_pow_w_of_assert_bits  {args : List (ZMod p)} : assert_bits args → (bits2num args).val < 2 ^ args.length := by
  intro cond₁
  unfold assert_bits at cond₁
  simp only [beq_iff_eq, Bool.decide_or, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at cond₁
  rw [bits2num_spec, ZMod.val_sum]
  apply Nat.mod_lt_of_lt
  have : ∑ i : Fin args.length, (2 ^ i.1 * args[i]).val ≤ ∑ i : Fin args.length, 2 ^ i.1 := by
    apply Finset.sum_le_sum
    intros i _
    specialize cond₁ args[i] (by simp)
    rcases cond₁ with cond₁ | cond₁
    · simp [cond₁]
    · simp [cond₁]
      convert ZMod.val_pow_le
      rfl
      refine Eq.symm (ZMod.val_ofNat_of_lt inst'.out)
      constructor
      linarith [inst'.out]
  apply lt_of_le_of_lt
  exact this
  clear this
  clear cond₁
  induction args.length with
  | zero =>
    simp
  | succ w ih =>
    simpa [Fin.sum_univ_castSucc, Nat.pow_succ, Nat.mul_two] using ih

def bits2num_e (bits : List var) : Exp p var :=
  List.foldr (fun b acc => .v b + .c 2 * acc) (.c 0) bits

omit inst' in
lemma bits2num_eq_eval_bits2num_e {bits : List (ZMod p)} : (bits2num_e bits).eval = bits2num bits := by
  unfold bits2num bits2num_e
  generalize e_eq : Exp.c (p := p) 0 = e
  generalize v_eq : (0 : ZMod p) = v
  have h : v = e.eval := by
    rw [←v_eq, ←e_eq, Exp.eval]
  induction bits with
  | nil =>
    simpa using h.symm
  | cons l ls ih =>
    simp only [List.foldr_cons, Exp.eval_add, ih, Exp.eval]



omit inst' in
lemma reduce₁ :
  ∀ {args : List (ZMod p)} {cs : Cs p (ZMod p)},
    assert_bits args -> (assert_bits_e args cs).eval = cs.eval := by
  intros args cs
  rw [assert_bits_e_spec]
  unfold assert_bits
  aesop

omit inst' in
lemma reduce₂ :
  ∀ {args : List (ZMod p)} {e : Expₑ p} {cs : Cs p (ZMod p)},
    e.eval = bits2num args -> (Cs.eq0 (bits2num_e args - e) cs).eval = cs.eval := by
  intros args e cs h
  rw (occs := .pos [1]) [Cs.eval]
  rw [Exp.eval_sub, bits2num_eq_eval_bits2num_e]
  rw [bits2num_spec] at h ⊢
  simp [h]

omit inst' in
lemma reduce {args : List (ZMod p)} {e : Expₑ p} {cs : Cs p (ZMod p)} :
  assert_bits args /\ e.eval = bits2num args ->
    (assert_bits_e args (.eq0 (bits2num_e args - e) cs)).eval = cs.eval := by
  rintro ⟨h₁, h₂⟩
  rw [reduce₁ h₁, reduce₂ h₂]

omit inst' in
lemma fail₁ :
  ∀ {args : List (ZMod p)} {cs : Cs p (ZMod p)},
    ¬ assert_bits args -> (assert_bits_e args cs).eval = .n := by
  intros args cs h
  rw [assert_bits_e_spec]
  unfold assert_bits at h
  simp only [beq_iff_eq, Bool.decide_or, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    not_forall, not_or] at h
  split_ifs with h'
  · exfalso
    rcases h with ⟨_, xh, _⟩
    rcases List.mem_iff_get.mp xh with ⟨i, _⟩
    specialize h' i
    aesop
  · rfl

omit inst' in
lemma fail₂ :
  ∀ {args : List (ZMod p)} {e : Expₑ p} {cs : Cs p (ZMod p)},
    e.eval ≠ (bits2num args) -> (Cs.eq0 (bits2num_e args - e) cs).eval = .n := by
  intros args e cs h
  
  unfold Cs.eval
  rw [Exp.eval_sub]
  rw [bits2num_eq_eval_bits2num_e]
  split_ifs with h'
  · exfalso
    apply h
    rw [sub_eq_zero, eq_comm] at h'
    exact h'
  · rfl

omit inst' in
lemma fail : ∀ {args : List (ZMod p)} {e : Expₑ p} {cs : Cs p (ZMod p)},
 (¬ (assert_bits args /\ e.eval = bits2num args)) ->
 (assert_bits_e args (.eq0 (bits2num_e args - e) cs)).eval = denotation.n := by
  intros args e cs h
  by_cases h' : assert_bits args
  · rw [reduce₁ h', fail₂ (by tauto)]
  · rw [fail₁ h']

def num2bits_circuit (w : ℕ) (e : Exp p var) (c : Vector var w → Cs p var) :=
  Cs.curry w (fun bits =>
      let ls := bits.toList
      letI rest := Cs.eq0 (bits2num_e ls - e) (c bits)
      assert_bits_e ls rest)

end Cs

section Wg

def num2bits_wg (w : ℕ) (e : Exp p (ZMod p)) (c : List (ZMod p) → Wg p) : Wg p :=
  letI bits := num2bitsLsbPure w (Exp.eval e)
  List.foldr (fun b acc => .cons b acc) (c bits) bits

end Wg

end Clap.Num2Bits
