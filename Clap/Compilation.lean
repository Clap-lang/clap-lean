import Mathlib.FieldTheory.Finite.Basic -- field operations, including / %

import Clap.Circuit
import Clap.Simulation

namespace Clap

/-
  This file introduces our "target language" `Cs` for Constraint System.
  Cs is a strict subset of Circuit and so is its evaluation function.
  A Circuit can be compiled to a Cs using `to_cs`, which introduces
  extra inputs (`lam`) to receive all the values that could be
  computed by the Circuit but can only be checked by a Cs.

  Soundness.F
  In order to show that a Cs is not more accepting that its original
  Circuit, i.e. that it won't accept more inputs, we show that there
  is a right-weak bisimulation `rw_bisim` between them.
  In particular, while a Circuit evaluates to any of the `denotation`
  values, a Cs might be stuck waiting for an extra input. Therefore
  the Cs is allowed to receive any value as extra input while the
  Circuit "waits" for the Cs to catch up, so long as they end up two
  denotations that bisimulate as well.

  A circuit can also be compiled to a Wg for Witness Generator using
  the `to_wg` function. A Wg computes the values needed by a Cs to
  check any computation that was done by the Circuit.

  Completeness
  A Cs and Wg can be composed using `wrap` to obtain a new Cs that
  does not require extra inputs compared to its original Circuit, as
  all extra inputs are immediately filled by the Wg.
  In order to show that Wg and Cs work correctly together, we show
  that, once wrapped, they are equivalent to the original Circuit.
-/


-- TODO we could remove this type and add an index to Circuit, which would save us from defining again the semantics of Cs
inductive Cs (p : ℕ) (var : Type) : Type where
  | nil : Cs p var
  | eq0 : Exp p var -> Cs p var -> Cs p var
  | lam : (var -> Cs p var) -> Cs p var

def Cs' (p : ℕ) : Type _ := (var:Type) -> Cs p var

variable {p : ℕ} [inst : Fact (Nat.Prime p)] [inst' : Fact (p ≠ 2)]
variable {var: Type}

def Cs.eval (c : Cs p (ZMod p)) : denotation (ZMod p) :=
  match c with
  | .nil => .u
  | .lam k => .l (fun x => eval (k x))
  | .eq0 e c =>
    if Exp.eval e = 0 then eval c else .n

def Cs.eval' (c : Cs' p) : denotation (ZMod p) := eval (c (ZMod p))

@[reducible]
def Cs.curry {n : ℕ} (k : Vector var n -> Cs p var) : Cs p var :=
  match n with
  | 0 => k ⟨#[], by rfl⟩
  | n+1 => .lam (fun (x : var) => Cs.curry (fun l => k (l.push x)))


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
    rw [this]
  simp only [this]

def assert_bits_e {w : ℕ} (bs : Vector var w) (rest : Cs p var) : Cs p var :=
  Vector.foldr assert_bit_e rest bs

omit inst' in
lemma assert_bits_e_spec {w : ℕ} {bs : Vector (ZMod p) w} {rest : Cs p (ZMod p)} :
    (assert_bits_e bs rest).eval = if (∀ i : Fin w, bs[i] = 0 ∨ bs[i] = 1) then rest.eval else denotation.n := by
  unfold assert_bits_e Vector.foldr
  rw [←Array.foldr_toList]
  have w_eq : w = bs.toArray.toList.length := by
    simp
  have {i : Fin w} : bs[i] = bs.toArray.toList.get (w_eq ▸ i) := by
    simp
    convert rfl
    · simp
    · exact eqRec_heq w_eq i
  simp only [this]
  clear this
  have {ls : List (ZMod p) } :
      (List.foldr assert_bit_e rest ls).eval =
        if ∀ i, ls.get i = 0 ∨ ls.get i = 1 then rest.eval
        else denotation.n := by
    induction ls with
    | nil => simp
    | cons l ls ih =>
      simp only [List.foldr_cons, List.length_cons, List.get_eq_getElem]
      split_ifs with h
      · have h₁ : l = 0 ∨ l = 1 := by
          specialize h 0
          simpa using h
        have h₂ : ∀ (i : Fin ls.length), ls.get i = 0 ∨ ls.get i = 1 := by
          intros i
          specialize h i.succ
          simp only [Fin.val_succ, List.getElem_cons_succ] at h
          exact h
        simp only [assert_bit_e_spec, h₁, ↓reduceIte, ih]
        split_ifs
        rfl
      · rw [assert_bit_e_spec, ih]
        split_ifs with h' h''
        · exfalso
          simp only [not_forall, not_or] at h
          rcases h with ⟨i', h⟩
          match i' with
          | ⟨0, _⟩ =>
            simp only [List.getElem_cons_zero] at h
            tauto
          | ⟨.succ i', i'_lt⟩ =>
            simp only [Nat.succ_eq_add_one, List.getElem_cons_succ] at h
            specialize h'' ⟨i', by linarith⟩
            simp only [List.get_eq_getElem] at h h''
            tauto
        · rfl
        · rfl
  specialize @this bs.toArray.toList
  convert this
  apply Iff.intro
  · intros h i
    specialize h (w_eq.symm ▸ i)
    have : i = w_eq ▸ w_eq.symm ▸ i :=
      eq_of_heq (heq_eqRec_iff_heq.mpr (HEq.symm (eqRec_heq (Eq.symm w_eq) i)))
    convert h
  · intros h i
    specialize h (w_eq ▸ i)
    exact h


def bits2num_e {w : ℕ} (bits : Vector var w) : Exp p var :=
  Vector.foldl (fun acc b => .v b + .c 2 * acc) (.c 0) bits

omit inst' in
lemma bits2num_e_spec {w : ℕ} {bits : Vector (ZMod p) w} :
  (bits2num_e bits).eval = ∑ i : Fin w, 2 ^ (w - (i.1 + 1)) * bits[i] := by
    unfold bits2num_e Vector.foldl
    rw [←Array.foldl_toList]
    have h₁ {i} : bits[i] = bits.toArray.toList.get i := by
      simp
      rfl
    have w_eq : w = bits.toArray.toList.length := by
      simp
    have sum_equiv : ∑ i : Fin w, 2 ^ (w - (i.1 + 1)) * bits[i] = (∑ i : Fin w, 2 ^ (w - (i.1 + 1)) * bits.toArray.toList.get (w_eq ▸ i)) + 0 := by
      rw [add_zero]
      apply fun a => congrArg Finset.univ.sum a
      ext i
      simp only [Fin.getElem_fin, Array.length_toList, List.get_eq_getElem, Array.getElem_toList,
        Vector.getElem_toArray, mul_eq_mul_left_iff, pow_eq_zero_iff', ne_eq]
      left
      convert rfl
      · unfold Array.size
        exact w_eq.symm
      · exact eqRec_heq w_eq i
    simp only [sum_equiv]
    generalize h_eq : Exp.c 0 = e
    have : 0 = e.eval := by
      rw [←h_eq, Exp.eval]
    rw [this]
    clear this
    revert e
    have (ls : List (ZMod p)) :
        ∀ (e : Exp p (ZMod p)),
          (List.foldl (fun acc b => Exp.v b + Exp.c 2 * acc) e ls).eval =
          (∑ i, 2 ^ (ls.length - (i.1 + 1)) * ls.get i) + 2 ^ ls.length * e.eval := by
      induction ls with
      | nil => simp
      | cons l ls ih =>
        intros e
        simp only [List.foldl_cons, ih, Exp.eval_add, Exp.eval_mul,
          List.length_cons]
        have : ∑ x : Fin (ls.length + 1), 2 ^ (ls.length + 1 - (x.1 + 1)) * (l :: ls).get x = 2 ^ ls.length * l + ∑ x : Fin ls.length, 2 ^ (ls.length - (x.1 + 1)) * ls[x] := by
          simp only [Nat.reduceSubDiff, List.get_eq_getElem, List.length_cons, Fin.getElem_fin]
          rw [Fin.sum_univ_succ]
          simp
        simp only [Exp.eval]
        grind
    intros e h
    specialize this bits.toArray.toList e
    simp only [← h, Array.foldl_toList, Vector.size_toArray, Array.length_toList,
      List.get_eq_getElem, Array.getElem_toList, Vector.getElem_toArray, Exp.eval, mul_zero,
      add_zero] at this ⊢
    rw [this]
    convert rfl with _ h a a' h_heq
    unfold Array.size at a'
    apply Fin.eq_of_val_eq
    apply Fin.val_eq_of_eq
    have : (w_eq ▸ a) ≍ a := by
      exact eqRec_heq w_eq a
    have : (w_eq ▸ a) ≍ a' := by
      exact eqRec_heq_iff.mpr h_heq
    exact eq_of_heq this

def to_cs (c : Circuit p var) : Cs p var :=
  match c with
  | .nil => .nil
  | .eq0 e c => .eq0 e (to_cs c)
  | .lam k => .lam (fun x => to_cs (k x))
  --
  | .share e k =>
      .lam (fun o =>
        .eq0 (e - .v o) (to_cs (k o)))
  | .is_zero e k =>
    .lam (fun inv =>
      .lam (fun o =>
        .eq0 (.c 1 - .v inv * e - .v o)
          (.eq0 (.v o * e) (to_cs (k o)))))
     -- e=0          o=1
     -- e≠0 inv=e^-1 o=0
  | .assert_range w e c =>
    Cs.curry (fun (bits : Vector _ w) =>
      letI rest := to_cs c
      letI rest := Cs.eq0 (bits2num_e bits - e) rest
      assert_bits_e bits rest)
  | .div_rem e k =>
      .lam (fun d =>
        .lam (fun r =>
          Cs.curry
            (fun (bits : Vector _ 8) =>
              letI rest := .eq0 (e - (256 * .v d + .v r)) (to_cs (k (d,r)))
              letI rest := Cs.eq0 (bits2num_e bits - Exp.v r) rest
              assert_bits_e bits rest
            )
        )
      )

def to_cs' (c : Circuit' p) : Cs' p := fun var => to_cs (c var)

inductive Wg (F : Type) : Type where
  | nil : Wg F
  | cons : F -> Wg F -> Wg F
  | input : (F -> Wg F) -> Wg F

def num2bits (n : ℕ) (f : ZMod p) : List (ZMod p) :=
  if n = 0
  then []
  else
    let bit := f.val % 2
    let rem := f.val / 2
    bit :: num2bits (n-1) rem

omit inst' in
lemma num2bits_length {w : ℕ} {v : ZMod p} : (num2bits w v).length = w := by
  revert v
  induction w with
  | zero => simp [num2bits]
  | succ w ih =>
    intros v
    unfold num2bits
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right,
      List.length_cons, ih]


example {w : ℕ} {v : ZMod p} :
  2 ^ w.succ < p →
  v.val < 2 ^ w.succ →
    let b : ZMod p :=
      if 2 ^ w ≤ v.val
      then 1
      else 0
    num2bits w.succ v = (num2bits w (v - b * 2 ^ w)) ++ [b] := by sorry
--     revert v
--     induction w with
--     | zero =>
--       intros v p_cond h
--       simp only [Nat.succ_eq_add_one, zero_add, pow_one] at h
--       split_ifs with cond
--       · have : v = 1 := by
--           have : v.val = 1 := by linarith
--           refine (ZMod.val_eq_one ?_ v).mp this
--           apply Nat.Prime.one_lt
--           exact inst.out
--         simp [num2bits, this, ZMod.val_one]
--       · have : v = 0 := by
--           simp only [pow_zero, not_le, Nat.lt_one_iff, ZMod.val_eq_zero] at cond
--           exact cond
--         simp [num2bits, this]
--       -- have : v = 1 := by
--       --   have : v.val = 1 := by linarith
--       --   refine (ZMod.val_eq_one ?_ v).mp this
--       --   apply Nat.Prime.one_lt
--       --   exact inst.out
--       -- simp [num2bits, this, ZMod.val_one]
--     | succ w ih =>
--       intros v p_cond h
--       split_ifs with cond
--       swap
--       · unfold num2bits
--         simp only [Nat.succ_eq_add_one, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self,
--           ↓reduceIte, add_tsub_cancel_right, List.cons_append, List.cons.injEq]
--         have p_cond' : 2 ^ (w + 1) < p := by
--           refine lt_trans ?_ p_cond
--           refine Nat.pow_lt_pow_succ ?_
--           decide
--         have v_div_2_le_p: v.val / 2 < p := by
--           apply lt_of_le_of_lt (Nat.div_le_self v.val 2)
--           exact lt_trans h p_cond
--         have : ((v.val / 2 : ℕ) : ZMod p).val < 2 ^ w.succ := by
--           rw [ZMod.val_natCast, Nat.mod_eq_of_lt v_div_2_le_p]
--           apply lt_of_le_of_lt (Nat.div_le_self v.val 2)
--           simp at cond
--           exact cond
--         specialize @ih (v.val / 2 : ℕ) p_cond' this

--         have importantFact : (2 ^ (w + 1) : ZMod p).val = 2 ^ (w + 1) := by
--           have : (2 : ZMod p).val = 2 := by
--             refine ZMod.val_ofNat_of_lt ?_
--             by_contra h'
--             simp only [not_lt] at h'
--             have := inst.out
--             have := inst'.out
--             omega
--           rw [ZMod.val_pow]
--           · rw [this]
--           · rw [this]
--             exact p_cond'
--         apply And.intro
--         · simp
--         · rw [ih]
--           split_ifs with cond'
--           · have : (v - 2 ^ (w + 1)).val = v.val - 2 ^ (w + 1) := by
--               rw [ZMod.val_sub (by rw [importantFact]; exact cond)]
--               have two_eq_two: (2 : ZMod p).val = 2 := by
--                   apply ZMod.val_ofNat_of_lt
--                   by_contra h''
--                   simp only [not_lt] at h''
--                   have : p = 0 ∨ p = 1 ∨ p = 2 := by
--                     omega
--                   rcases this with h | h | h
--                   · have fct := inst.out
--                     rw [h] at fct
--                     exact Nat.prime_zero_false fct
--                   · have fct := inst.out
--                     rw [h] at fct
--                     exact Nat.prime_one_false fct
--                   · have fct := inst'.out
--                     rw [h] at fct
--                     simp at fct
--               have : (2 ^ (w + 1) : ZMod p).val = 2 ^ (w + 1) := by
--                 rw [ZMod.val_pow] <;> rw [two_eq_two]
--                 nlinarith
--               rw [this]
--             rw [this]
--             have : (v.val - 2 ^ (w + 1)) / 2 = v.val / 2 - 2 ^ w := by
--               rw [Nat.pow_succ, mul_comm, Nat.sub_mul_div_of_le]
--               rw [mul_comm,←Nat.pow_succ]
--               exact cond
--             rw [this, one_mul]
--             have : (((v.val / 2 - 2 ^ w) : ℕ) : ZMod p) = ((v.val / 2 : ℕ) : ZMod p) - 2 ^ w := by
--               rw [Nat.cast_sub]
--               simp only [Nat.cast_pow, Nat.cast_ofNat]
--               convert cond'
--               simp only [ZMod.val_natCast]
--               rw [Nat.div_mod_eq_div (ZMod.val_lt v)]
--             rw [this]

--           · simp only [ZMod.val_natCast, not_le] at cond'
--             have : v.val / 2 < p := by
--               exact lt_of_le_of_lt (Nat.div_le_self v.val 2) (ZMod.val_lt v)
--             rw [Nat.mod_eq_of_lt this] at cond'
--             have : v.val / 2 < v.val / 2 := by
--               apply lt_of_lt_of_le
--               exact cond'
--               rw [Nat.le_div_iff_mul_le, ←Nat.pow_succ]
--               exact cond
--               decide
--             simp at this


--       · sorry

def to_wg (c : Circuit p (ZMod p)) : Wg (ZMod p) :=
  match c with
  | .nil => Wg.nil
  | .eq0 _ c => to_wg c
  | .lam k => Wg.input (fun i => to_wg (k i))
  | .share e k =>
    let e := Exp.eval e
    .cons e (to_wg (k e))
  | .is_zero e k =>
    let e := Exp.eval e
    let inv : (ZMod p) := e⁻¹
    let o : (ZMod p) := if e = 0 then 1 else 0
    .cons inv (.cons o (to_wg (k o)))
  | .assert_range w e c =>
    let bits : List (ZMod p) := num2bits w (Exp.eval e)
    List.foldr (fun b acc => .cons b acc) (to_wg c) bits
  | .div_rem e k =>
    let e := Exp.eval e
    let d := e.val / 256
    let r := e.val % 256
    .cons d (.cons r (to_wg (k (d,r))))

-- def to_wg' (c:Circuit' F) : Wg F := to_wg (c F)

def wrap (wg : Wg (ZMod p)) (cs : Cs p (ZMod p)) : Cs p (ZMod p) :=
  match wg,cs with
  |         .nil , .nil      => .nil
  |           wg , .eq0 e cs => .eq0 e (wrap wg cs)
  | Wg.input kwg , .lam k    => .lam (fun x => wrap (kwg x) (k x))
  |   .cons x wg , .lam k    => wrap (wg : Wg (ZMod p)) (k x)
  |            _ , _         => .eq0 (.c 1) .nil -- needed because we don't have typed wg and cs

open Simulation

def bits2num {w : ℕ} (bits : Vector (ZMod p) w) : (ZMod p) :=
  Vector.foldr (fun b acc => b + 2 * acc) 0 bits

lemma bits2num_spec {w : ℕ} {bits : Vector (ZMod p) w} : bits2num bits = ∑ i : Fin w, 2 ^ i.1 * bits[i] := by
  unfold bits2num Vector.foldr
  rw [←Array.foldr_toList]
  have h₁ {i} : bits[i] = bits.toArray.toList.get i := by
    simp
    rfl
  have w_eq : w = bits.toArray.toList.length := by
    simp
  -- rw [@Fin.sum_univ_def]
  -- unfold List.sum
  have : List.foldr (fun b acc => b + 2 * acc) 0 bits.toArray.toList = List.foldr (fun i acc => bits[i] + 2 * acc) 0 (List.finRange w) := by
    -- rw [@List.foldr.eq_def]
    -- match h : bits.toArray.toList with
    -- | .nil =>
    --   rw [h, List.length_nil] at w_eq
    --   have : (List.finRange w) = [] := by simp [w_eq]
    --   simp [this]
    -- | .cons l ls =>
    --   simp only
      sorry
  simp only [this, Fin.getElem_fin]
  have {f : Fin w → ZMod p} : (∑ i : Fin w, f i) = ((List.finRange w).map f).sum := rfl
  rw [this, List.sum, List.foldr_map]
  clear this
  have : List.foldr (fun i acc => bits[i.1] + 2 * acc) 0 (List.finRange w) = 2 ^ 0 * List.foldr (fun i acc => bits[i.1] + 2 * acc) 0 (List.finRange w) := by
    simp
  rw [this]
  clear this
  have : List.finRange w = (List.finRange w).drop 0 := by simp
  rw [this]
  clear this
  set i := (w : ℕ) with i_eq
  have : w - i = 0 := by
    simp [i_eq]
  simp only [←this]
  clear i_eq this
  induction i with
  | zero =>
    have : (List.finRange w).drop w = [] := by
      simp
    simp [this]
  | succ i ih =>
    by_cases h : i ≥ w
    · have : w - (i + 1) = w - i := by
        omega
      rw [this]
      exact ih
    · rw [ge_iff_le, not_le] at h
      have {a : ZMod p} : a ^ (w - (i + 1)) * a = a ^ (w - i) := by
        rw [←pow_succ]
        grind
      have h₁ : List.drop (w - (i + 1)) (List.finRange w) = ⟨w - (i + 1), by omega⟩ :: List.drop (w - i) (List.finRange w) := by

        sorry
      simp only [h₁, Nat.cast_ofNat, List.foldr_cons, LeftDistribClass.left_distrib, ←mul_assoc, this]
      erw [ih]

omit inst' in
lemma bits2num_eq_eval_bits2num_e {w : ℕ} {bits : Vector (ZMod p) w} : bits2num bits = (bits2num_e bits).eval := by
  rw [bits2num_e_spec]
  rw [← @bits2num_spec]

-- TODO one of these sorry definitions is causing the soundness kernel metavariable problem

omit inst' in
lemma rw_bisim_uncurry : ∀ (w : ℕ) (d : denotation (ZMod p)) (k : Vector (ZMod p) w -> Cs p (ZMod p)),
 (∀ args : Vector (ZMod p) w, rw_bisim d (k args).eval) ->
 rw_bisim d (Cs.curry k).eval := by
  intro w
  induction w
  case _ =>
    intros d k h
    simp [Cs.curry]
    apply h
  case _ ih =>
    intros d k h
    simp [Cs.curry]
    constructor
    intro x
    apply ih
    intro args
    apply h

def assert_bits {w : ℕ} (args : Vector (ZMod p) w) : Bool :=
  Vector.all args (fun (x : ZMod p) => x == 0 ∨ x == 1)

lemma bits2num_val_lt_2_pow_w_of_assert_bits  {w : ℕ} {args : Vector (ZMod p) w} : assert_bits args → (bits2num args).val < 2 ^ w := by
        intro cond₁
        unfold assert_bits at cond₁
        simp only [beq_iff_eq, Bool.decide_or, Vector.all_eq_true, Bool.or_eq_true,
          decide_eq_true_eq] at cond₁
        rw [bits2num_spec]
        have {f : Fin w → ZMod p} : (∑ i, f i).val = (∑ i, (f i).val) % p := by
          rw [Fin.sum_univ_def, Fin.sum_univ_def]
          unfold List.sum
          generalize ap_eq : (0 : ZMod p) = ap
          generalize a_eq : 0 = a
          generalize h : (List.finRange w) = ls
          have : ap.val = a % p := by
            aesop
          clear a_eq ap_eq h
          induction ls with
          | nil =>
            simpa using this
          | cons l ls ih =>
            simp [ZMod.val_add, ih, Nat.add_mod_mod]
        rw [this]
        apply Nat.mod_lt_of_lt
        have : ∑ i : Fin w, (2 ^ (w - (↑i + 1)) * args[i]).val ≤ ∑ i : Fin w, 2 ^ (w - (↑i + 1)) := by
          have {α : Type} [Fintype α] {f g : α → ℕ} : (∀ i, f i ≤ g i) → ∑ i, f i ≤ ∑ i, g i :=
            fun a => Finset.sum_le_sum fun i a_1 => a i
          apply this
          intros i
          specialize cond₁ i.1 i.2
          rcases cond₁ with cond₁ | cond₁
          · simp [cond₁]
          · simp [cond₁]
            rw [Nat.Simproc.sub_add_eq_comm]
            have {a : ZMod p} {e : ℕ}: (a ^ e).val = a.val ^ e % p := by
              induction e with
              | zero =>
                simp
                exact ZMod.val_one_eq_one_mod p
              | succ e ih =>
                rw [pow_succ, pow_succ, ←Nat.mod_mul_mod, ←ih, ZMod.val_mul]
            rw [this]
            have : (2 : ZMod p).val = 2 := by
              apply ZMod.val_ofNat_of_lt
              apply Nat.two_lt_of_ne <;> intros h
              · have := h ▸ inst.out
                exact Nat.prime_zero_false this
              · have := h ▸ inst.out
                exact Nat.prime_one_false this
              · have := h ▸ inst'.out
                simp at this
            rw [this]
            exact Nat.mod_le _ _
        apply lt_of_le_of_lt
        exact this
        have : ∑ i : Fin w, 2 ^ (w - (↑i + 1)) = ∑ i : Fin w, 2 ^ i.1 := by
          have {α : Type} [Fintype α] {f g : α → ℕ} (equiv : α → α) (h : Function.Bijective equiv) : (∀ a, f a = g (equiv a)) → ∑ a, f a = ∑ a, g a := by
            exact fun a => Function.Bijective.finset_sum equiv h f g a
          let e (i : Fin w) : Fin w := ⟨w - (i.1 + 1), by apply Nat.sub_lt_self <;> omega⟩
          apply Function.Bijective.finset_sum e
          · apply And.intro
            · intros a₁ a₂
              simp only [Fin.mk.injEq, e]
              omega
            · intros b
              dsimp [e]
              use ⟨w - (b.1 + 1), by omega⟩
              apply Fin.eq_of_val_eq
              simp only
              omega
          · intros x; dsimp [e]
        rw [this]
        clear this
        clear this
        clear this
        clear cond₁
        clear args
        induction w with
        | zero =>
          simp
        | succ w ih =>
          simpa [Fin.sum_univ_castSucc, Nat.pow_succ, Nat.mul_two] using ih

omit inst' in
lemma reduce₁ :
  ∀ {w : ℕ} {args : Vector (ZMod p) w} {cs : Cs p (ZMod p)},
    assert_bits args -> (assert_bits_e args cs).eval = cs.eval := by
  intros w args cs
  rw [assert_bits_e_spec]
  unfold assert_bits
  aesop

omit inst' in
lemma reduce₂ :
  ∀ {w : ℕ} {args : Vector (ZMod p) w} {e : Expₑ p} {cs : Cs p (ZMod p)},
    e.eval = bits2num args -> (Cs.eq0 (bits2num_e args - e) cs).eval = cs.eval := by
  intros w args e cs h
  rw (occs := .pos [1]) [Cs.eval]
  unfold Exp.eval
  rw [bits2num_spec] at h
  rw [bits2num_e_spec, h]
  simp

omit inst' in
lemma reduce {w : ℕ} {args : Vector (ZMod p) w} {e : Expₑ p} {cs : Cs p (ZMod p)} :
  assert_bits args /\ e.eval = bits2num args ->
    (assert_bits_e args (.eq0 (bits2num_e args - e) cs)).eval = cs.eval := by
  rintro ⟨h₁, h₂⟩
  rw [reduce₁ h₁, reduce₂ h₂]

omit inst' in
lemma fail₁ :
  ∀ {w : ℕ} {args : Vector (ZMod p) w} {cs : Cs p (ZMod p)},
    ¬ assert_bits args -> (assert_bits_e args cs).eval = .n := by
  intros w args cs h
  rw [assert_bits_e_spec]
  unfold assert_bits at h
  simp only [beq_iff_eq, Bool.decide_or, Vector.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    not_forall, not_or] at h
  split_ifs with h'
  · exfalso
    rcases h with ⟨i, ih, h⟩
    specialize h' ⟨i, ih⟩
    aesop
  · rfl

omit inst' in
lemma fail₂ :
  ∀ {w : ℕ} {args : Vector (ZMod p) w} {e : Expₑ p} {cs : Cs p (ZMod p)},
    e.eval ≠ (bits2num args) -> (Cs.eq0 (bits2num_e args - e) cs).eval = .n := by
  intros w args e cs h
  unfold Cs.eval Exp.eval
  rw [←bits2num_eq_eval_bits2num_e]
  split_ifs with h'
  · exfalso
    apply h
    rw [sub_eq_zero, eq_comm] at h'
    rw [h']
  · rfl

omit inst' in
lemma fail : ∀ {w : ℕ} {args : Vector (ZMod p) w} {e : Expₑ p} {cs : Cs p (ZMod p)},
 (¬ (assert_bits args /\ e.eval = bits2num args)) ->
 (assert_bits_e args (.eq0 (bits2num_e args - e) cs)).eval = denotation.n := by
  intros w args e cs h
  by_cases h' : assert_bits args
  · rw [reduce₁ h', fail₂ (by tauto)]
  · rw [fail₁ h']

theorem soundness :
  ∀ (c : Circuitₑ p),
    rw_bisim (Circuit.eval c) (Cs.eval (to_cs c)) := by
  intro c
  induction c with
  | nil =>
    simp [Circuit.eval,to_cs]
    constructor
  | lam k h =>
    simp [Circuit.eval,to_cs]
    constructor
    exact h
  | eq0 e c h =>
    simp [Circuit.eval,Cs.eval,to_cs]
    split
    apply h
    constructor
  | share e c h =>
    simp [Circuit.eval,Cs.eval,to_cs]
    apply rw_bisim.right
    intro x
    simp [Exp.eval]
    split
    have hmy : x = Exp.eval e := by grind
    rw [<-hmy]
    apply h
    constructor
  | is_zero e c h =>
    apply rw_bisim.right
    intro inv
    apply rw_bisim.right
    intro o
    simp [Exp.eval,Circuit.eval,Cs.eval]
    split
    case is_zero.h.h.isTrue he0 =>
      split
      case isTrue hsub =>
        split
        case isTrue hmul =>
          simp [*] at *
          have hmy : o=1 := by grind
          rw [hmy]
          apply h
        case isFalse hmul => constructor
      case isFalse hsub => constructor
    case is_zero.h.h.isFalse he0 =>
      split
      case isTrue hsub =>
        split
        case isTrue hmul =>
          simp [*] at *
          rw [hmul]
          apply h
        case isFalse hmul => constructor
      case isFalse hsub => constructor
  | assert_range w e c h =>
    simp [Circuit.eval,to_cs]
    apply rw_bisim_uncurry
    intros args
    by_cases cond₁ : assert_bits args <;> by_cases cond₂ : Exp.eval e = bits2num args
    · rw [reduce ⟨cond₁, cond₂⟩]
      have : e.eval.val < 2 ^ w := by
        rw [cond₂]
        exact bits2num_val_lt_2_pow_w_of_assert_bits cond₁
      simp [this]
      exact h
    · rw [reduce₁ cond₁, fail₂ cond₂]
      exact rw_bisim.none _
    · rw [fail₁ cond₁]
      exact rw_bisim.none _
    · rw [fail₁ cond₁]
      exact rw_bisim.none _
  | div_rem e c ih =>
    sorry
    -- apply rw_bisim.right
    -- intro d
    -- apply rw_bisim.right
    -- intro r
    -- apply rw_bisim_uncurry
    -- intros bits
    -- simp [Circuit.eval]
    -- by_cases h : assert_bits bits = true
    -- · rw [reduce₁ h]
    --   by_cases h' : Exp.eval (Exp.v r) = bits2num bits
    --   · rw [reduce₂ h']
    --     unfold Cs.eval
    --     split_ifs with h'
    --     ·
    --       have h₁ : d = ((e.eval.val / 256) : ℕ) := by
    --         simp only [Exp.eval] at h'


    --         sorry
    --       have h₂ : r = ((e.eval.val % 256) : ℕ) := by sorry
    --       rw [h₁, h₂]
    --       exact ih _
    --     · exact rw_bisim.none _
    --   · rw [@fail₂ p _ _ 8 bits (Exp.v r) _ h']
    --     exact rw_bisim.none _
    -- · rw [fail₁ h]
    --   exact rw_bisim.none _

-------------------------------------------------------------------

--       have := @fail₁

--     split
--     case _ he0 =>
--       convert h _
--       rw [sub_eq_zero] at he0
--       have hr: r=0 := sorry
--       simp [hr] at he0
--       rw [he0]

--       rw [mul_div_cancel_left₀]
--       sorry
--       sorry
--       -- TODO where is this Coe coming from?
-- --      have hr : (r:F) = ↑(Coe.coe e.eval % 256) := sorry
-- --      rw [<-hr]
--     sorry

theorem soundness' : ∀ (c : Circuit' p),
  rw_bisim (Circuit.eval' c) (Cs.eval' (to_cs' c)) := by
  intro c
  apply soundness

def completeness : ∀ (c : Circuit p (ZMod p)),
  Circuit.eval c = Cs.eval (wrap (to_wg c) (to_cs c)) := by
  intro c
  induction c with
  | nil =>
    simp [Circuit.eval,to_cs,to_wg,wrap]
    constructor
  | lam k h =>
    simp [Circuit.eval,Cs.eval,to_cs,to_wg,wrap]
    funext
    apply h
  | eq0 e c h =>
    simp [Circuit.eval,Cs.eval,to_cs,to_wg,wrap]
    split
    exact h
    constructor
  | share e c h =>
    simp [Exp.eval,Circuit.eval,Cs.eval,to_cs,to_wg,wrap]
    apply h
  | is_zero e c h =>
    simp [Exp.eval,Circuit.eval,Cs.eval,to_cs,to_wg,wrap]
    split
    case is_zero.isTrue he0 =>
      simp
      split <;> apply h
    case is_zero.isFalse he0 =>
      split
      case isTrue he0' =>
        apply h
      case isFalse he0' =>
        simp [*] at *
  | assert_range w e c ih =>
    -- unfold to_wg to_cs wrap
    -- Circuit.eval, Cs.eval,
    simp only [Circuit.eval_assert_range, ih]
    split_ifs with h
    · conv =>
        right
        rw [to_wg, to_cs]
      -- unfold assert_bits_e assert_bit_e

      induction w with
      | zero =>
        have : e.eval = 0 := by
          simp only [pow_zero, Nat.lt_one_iff, ZMod.val_eq_zero] at h
          exact h
        simp [num2bits, Cs.curry, assert_bits_e, bits2num_e, wrap, Cs.eval, Exp.eval, this]
      | succ w ih =>
        have := @List.foldl_append


        unfold num2bits Cs.curry
        simp
        -- simp [num2bits]

        sorry



      -- have : wrap (to_wg (Circuit.assert_range w e c)) (to_cs (Circuit.assert_range w e c)) = sorry := by
      --   unfold to_wg to_cs wrap
      --   simp only
      --   sorry


      -- sorry
    · rw [not_lt] at h


      sorry
  | div_rem e c h =>
    -- simp [Exp.eval,Circuit.eval,Cs.eval,to_cs,to_wg,wrap]
    sorry
