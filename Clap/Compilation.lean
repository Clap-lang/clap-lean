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
  | n+1 => .lam (fun x:var => Cs.curry (fun l => k (l.push x)))


def assert_bit_e (rest : Cs p var) (b : var) : Cs p var :=
  .eq0 (.v b * (.c 1 - .v b)) rest

def assert_bits_e {w : ℕ} (bs : Vector var w) (rest : Cs p var) : Cs p var :=
  Vector.foldl assert_bit_e rest bs

def bits2num_e {w : ℕ} (bits : Vector var w) : Exp p var :=
  Vector.foldl (fun acc b => .v b + .c 2 * acc) (.c 0) bits

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
    num2bits w.succ v = (num2bits w (v - b * 2 ^ w)) ++ [b] := by
    revert v
    induction w with
    | zero =>
      intros v p_cond h
      simp only [Nat.succ_eq_add_one, zero_add, pow_one] at h
      split_ifs with cond
      · have : v = 1 := by
          have : v.val = 1 := by linarith
          refine (ZMod.val_eq_one ?_ v).mp this
          apply Nat.Prime.one_lt
          exact inst.out
        simp [num2bits, this, ZMod.val_one]
      · have : v = 0 := by
          simp only [pow_zero, not_le, Nat.lt_one_iff, ZMod.val_eq_zero] at cond
          exact cond
        simp [num2bits, this]
      -- have : v = 1 := by
      --   have : v.val = 1 := by linarith
      --   refine (ZMod.val_eq_one ?_ v).mp this
      --   apply Nat.Prime.one_lt
      --   exact inst.out
      -- simp [num2bits, this, ZMod.val_one]
    | succ w ih =>
      intros v p_cond h
      split_ifs with cond
      swap
      · unfold num2bits
        simp only [Nat.succ_eq_add_one, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self,
          ↓reduceIte, add_tsub_cancel_right, List.cons_append, List.cons.injEq]
        have p_cond' : 2 ^ (w + 1) < p := by
          refine lt_trans ?_ p_cond
          refine Nat.pow_lt_pow_succ ?_
          decide
        have v_div_2_le_p: v.val / 2 < p := by
          apply lt_of_le_of_lt (Nat.div_le_self v.val 2)
          exact lt_trans h p_cond
        have : ((v.val / 2 : ℕ) : ZMod p).val < 2 ^ w.succ := by
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt v_div_2_le_p]
          apply lt_of_le_of_lt (Nat.div_le_self v.val 2)
          simp at cond
          exact cond
        specialize @ih (v.val / 2 : ℕ) p_cond' this

        have importantFact : (2 ^ (w + 1) : ZMod p).val = 2 ^ (w + 1) := by
          have : (2 : ZMod p).val = 2 := by
            refine ZMod.val_ofNat_of_lt ?_
            by_contra h'
            simp only [not_lt] at h'
            have := inst.out
            have := inst'.out
            omega
          rw [ZMod.val_pow]
          · rw [this]
          · rw [this]
            exact p_cond'
        apply And.intro
        · simp
        · rw [ih]
          split_ifs with cond'
          · have : (v - 2 ^ (w + 1)).val = v.val - 2 ^ (w + 1) := by
              rw [ZMod.val_sub (by rw [importantFact]; exact cond)]
              have two_eq_two: (2 : ZMod p).val = 2 := by
                  apply ZMod.val_ofNat_of_lt
                  by_contra h''
                  simp only [not_lt] at h''
                  have : p = 0 ∨ p = 1 ∨ p = 2 := by
                    omega
                  rcases this with h | h | h
                  · have fct := inst.out
                    rw [h] at fct
                    exact Nat.prime_zero_false fct
                  · have fct := inst.out
                    rw [h] at fct
                    exact Nat.prime_one_false fct
                  · have fct := inst'.out
                    rw [h] at fct
                    simp at fct
              have : (2 ^ (w + 1) : ZMod p).val = 2 ^ (w + 1) := by
                rw [ZMod.val_pow] <;> rw [two_eq_two]
                nlinarith
              rw [this]
            rw [this]
            have : (v.val - 2 ^ (w + 1)) / 2 = v.val / 2 - 2 ^ w := by
              rw [Nat.pow_succ, mul_comm, Nat.sub_mul_div_of_le]
              rw [mul_comm,←Nat.pow_succ]
              exact cond
            rw [this, one_mul]
            have : (((v.val / 2 - 2 ^ w) : ℕ) : ZMod p) = ((v.val / 2 : ℕ) : ZMod p) - 2 ^ w := by
              rw [Nat.cast_sub]
              simp only [Nat.cast_pow, Nat.cast_ofNat]
              convert cond'
              simp only [ZMod.val_natCast]
              rw [Nat.div_mod_eq_div (ZMod.val_lt v)]
            rw [this]

          · simp only [ZMod.val_natCast, not_le] at cond'
            have : v.val / 2 < p := by
              exact lt_of_le_of_lt (Nat.div_le_self v.val 2) (ZMod.val_lt v)
            rw [Nat.mod_eq_of_lt this] at cond'
            have : v.val / 2 < v.val / 2 := by
              apply lt_of_lt_of_le
              exact cond'
              rw [Nat.le_div_iff_mul_le, ←Nat.pow_succ]
              exact cond
              decide
            simp at this


      · sorry

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
    List.foldl (fun acc b => .cons b acc) (to_wg c) bits
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

def bits2num {w:ℕ} (bits : Vector (ZMod p) w) : (ZMod p) :=
  Vector.foldl (fun acc b => b + 2 * acc) 0 bits

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

lemma Vector_succ_eq_head_cons_tail {α : Type} {n : ℕ} {args : Vector α n.succ} : args = Vector.insertIdx args.tail 0 args.head := by
    simp only [Vector.insertIdx_zero]
    ext i h
    match i with
    | .zero =>
      simp
      rfl
    | .succ i =>
      simp [add_comm]

omit inst' in
lemma reduce₁ :
  ∀ {w : ℕ} {args : Vector (ZMod p) w} {cs : Cs p (ZMod p)},
    assert_bits args -> (assert_bits_e args cs).eval = cs.eval := by
intros w
induction w with
| zero =>
  intros args
  have : args = #v[] := by simp
  simp [this, assert_bits_e]
| succ w ih =>
  intros args cs h
  have := Vector_succ_eq_head_cons_tail (n := w) (args := args)
  simp only [Nat.add_one_sub_one, Vector.tail_eq_cast_extract, Vector.insertIdx_zero] at this
  rw [this] at h ⊢
  unfold assert_bits_e Vector.foldl at ih ⊢
  unfold assert_bits at h
  simp only [Vector.toArray_cast, Vector.toArray_append, Vector.toArray_extract, Array.size_append,
    List.size_toArray, List.length_cons, List.length_nil, zero_add, Array.size_extract,
    Vector.size_toArray, min_self,
    Array.foldl_append', List.foldl_toArray', List.foldl_cons, List.foldl_nil]
  simp only [beq_iff_eq, Bool.decide_or, Vector.all_cast, Vector.all_append, Vector.all_mk,
    List.size_toArray, List.length_cons, List.length_nil, zero_add, List.all_toArray',
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, Vector.all_eq_true, min_self,
    Vector.getElem_extract] at h
  have : args.toArray.extract 1 (w + 1) = (args.extract 1 (w + 1)).toArray := by rfl
  rw [assert_bit_e, this]
  have : min (w + 1) (w + 1) - 1 = w := by simp
  rw [←this] at ih
  have : assert_bits (args.extract 1) = true := by
    unfold assert_bits
    simp only [beq_iff_eq, Bool.decide_or, Vector.all_eq_true, min_self, add_tsub_cancel_right,
      Vector.getElem_extract, Bool.or_eq_true, decide_eq_true_eq]
    exact h.2
  specialize @ih (args.extract 1) (Cs.eq0 (Exp.v args.head * (Exp.c 1 - Exp.v args.head)) cs) this
  have :
    (Array.foldl assert_bit_e (Cs.eq0 (Exp.v args.head * (Exp.c 1 - Exp.v args.head)) cs) (args.extract 1).toArray) =
       (Array.foldl assert_bit_e (Cs.eq0 (Exp.v args.head * (Exp.c 1 - Exp.v args.head)) cs) (args.extract 1).toArray 0 w) := by
    simp
  rw [this] at ih
  simp only [Nat.succ_eq_add_one, add_tsub_cancel_right]
  rw [ih, Cs.eval]
  have : args.head * (1 - args.head) = 0 := by
    simp [sub_eq_zero]
    rcases h.1 with h' | h'
    · left; exact h'
    · right; exact h'.symm
  unfold Exp.eval Exp.eval Exp.eval
  simp [this]

omit inst' in
lemma reduce₂ :
  ∀ {w : ℕ} {args : Vector (ZMod p) w} {e : Expₑ p} {cs : Cs p (ZMod p)},
    e.eval = bits2num args -> (Cs.eq0 (bits2num_e args - e) cs).eval = cs.eval := by
  intros w args e cs h
  have : (bits2num_e args).eval - (bits2num args) = 0 := by
    simp [sub_eq_zero]
    unfold bits2num_e bits2num Vector.foldl
    generalize h_eq : Exp.c (0 : ZMod p) = v
    have : 0 = v.eval := by
      rw [←h_eq, Exp.eval]
    rw [this]
    clear h_eq this
    revert v e
    induction w with
    | zero =>
      have : args = #v[] := by simp
      simp [this]
    | succ w ih =>
      intros e _ v
      have := Vector_succ_eq_head_cons_tail (n := w) (args := args)
      simp only [Nat.add_one_sub_one, Vector.tail_eq_cast_extract, Vector.insertIdx_zero] at this
      rw [this]
      have : min (w + 1) (w + 1) - 1 = w := by simp
      rw [←this] at ih
      specialize @ih (args.extract 1) (Exp.c (bits2num (args.extract 1))) rfl
      simp only [Vector.toArray_extract, Array.size_extract, Vector.size_toArray, min_self,
        add_tsub_cancel_right] at ih
      simp [ih, Exp.eval]
  simp [Cs.eval, h, this]

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
  unfold assert_bits at h
  simp only [beq_iff_eq, Bool.decide_or, Vector.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    not_forall, not_or] at h
  rcases h with ⟨i, h, h', h''⟩
  match w with
  | .zero =>
    simp at h
  | .succ w =>
    have : ∀ j : ℕ, j > i → (assert_bits_e (args.extract 0 j) cs).eval = denotation.n := by
      intros j j_ge_i
      unfold assert_bits_e Vector.foldl
      rw [
        ←Array.foldl_toList, Vector.toArray_extract,
        Array.toList_extract, List.extract_eq_drop_take,
        Nat.sub_zero, List.drop_zero
      ]

      have h₀ : args.toArray.toList.get ⟨i, by convert h; simp⟩ ≠ 0 := by
        simp only [Nat.succ_eq_add_one, Array.length_toList, List.get_eq_getElem,
          Array.getElem_toList, Vector.getElem_toArray, ne_eq]
        exact h'
      have h₁ : args.toArray.toList.get ⟨i, by convert h; simp⟩ ≠ 1 := by
        simp only [Nat.succ_eq_add_one, Array.length_toList, List.get_eq_getElem,
          Array.getElem_toList, Vector.getElem_toArray, ne_eq]
        exact h''

      generalize h_eq : args.toArray.toList = ls
      simp only [Nat.succ_eq_add_one, Array.length_toList, List.get_eq_getElem, h_eq,
        ne_eq] at h₀ h₁

      have h_len : ls.length = w.succ := by
        simp [←h_eq]


      rw [←h_len] at h
      revert cs
      induction j with
      | zero =>
        simp at j_ge_i
      | succ j ih =>
        intro cs
        rcases Order.lt_succ_iff_eq_or_gt.mp j_ge_i with h' | h'
        · simp only [Nat.add_eq, add_zero] at h'
          rw [h']
          rw [List.take_succ_eq_append_getElem h, List.foldl_append, List.foldl_cons, List.foldl_nil]
          unfold assert_bit_e Cs.eval
          split_ifs with h''
          · exfalso
            simp only [Exp.eval] at h''
            rw [mul_eq_zero] at h''
            rcases h'' with h'' | h''
            · exact h₀ h''
            · apply h₁
              have h'' := add_eq_of_eq_sub h''.symm
              rw [zero_add] at h''
              exact h''
          · rfl
        · simp only [Nat.add_eq, add_zero] at h'
          specialize @ih h'
          by_cases h' :  j < ls.length
          · rw [List.take_succ_eq_append_getElem h', List.foldl_append, List.foldl_cons, List.foldl_nil]
            unfold assert_bit_e Cs.eval
            split_ifs with h''
            · exact ih
            · rfl
          · rw [not_lt] at h'
            have : List.take (j + 1) ls = List.take j ls := by
              rw [List.take_eq_take_iff]
              simp only [h', inf_of_le_right, inf_eq_right]
              exact Nat.le_add_right_of_le h'
            rw [this]
            exact ih

    specialize this w.succ h
    simp only [Nat.succ_eq_add_one, Nat.sub_zero, Vector.extract_size] at this
    convert this using 1

omit inst' in
lemma fail₂ :
  ∀ {w : ℕ} {args : Vector (ZMod p) w} {e : Expₑ p} {cs : Cs p (ZMod p)},
    e.eval ≠ (bits2num args) -> (Cs.eq0 (bits2num_e args - e) cs).eval = .n := by
  intros w args e cs h
  unfold Cs.eval Exp.eval
  split_ifs with h'
  · exfalso
    apply h
    rw [sub_eq_zero, eq_comm] at h'
    rw [h']
    unfold bits2num bits2num_e Vector.foldl
    rw [
        ←Array.foldl_toList, ←Array.foldl_toList
      ]
    generalize z_eq : (0 : ZMod p) = x
    generalize h_exp : (Exp.c x) = x_exp
    generalize arr_exp : args.toArray.toList = ls
    have h'' : x_exp.eval = x := by
      rw [←h_exp, Exp.eval]
    clear z_eq arr_exp h_exp
    revert x x_exp
    induction ls with
    | nil =>
      simp
    | cons l ls ih =>
      intros x x_exp h
      simp only [List.foldl_cons]
      apply ih
      simp only [Exp.eval, h]
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
        unfold assert_bits Vector.all at cond₁
        rw [cond₂]
        unfold bits2num Vector.foldl
        have h' := args.2
        revert h'
        rw [←Array.all_toList] at cond₁
        rw [←Array.foldl_toList, Array.size]
        have : 2 ^ w = 2 ^ w + 2 ^ w * 0 := by ring
        rw [this]
        generalize arr_def : args.toArray.toList = ls
        rw [arr_def] at cond₁
        generalize tmp : (0 : ZMod p) = acc'
        have equiv : 0 = acc'.val := by
          rw [←tmp]
          simp
        rw [equiv]
        revert cond₁
        simp only [beq_iff_eq, Bool.decide_or, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
          gt_iff_lt]
        clear arr_def cond₂ args tmp this equiv
        revert w acc'
        induction ls with
        | nil =>
          intros w acc'
          simp
          intros h
          rw [←h]
          simp
        | cons l ls ih =>
          intros w acc h' h''
          simp only [List.mem_cons, forall_eq_or_imp] at h'
          match w with
          | .zero => simp at h''
          | .succ w =>
            simp only [List.length_cons, Nat.succ_eq_add_one, Nat.add_right_cancel_iff] at h''
            specialize ih w  (l + 2 * acc) h'.2 h''
            simp only [List.foldl_cons, Nat.succ_eq_add_one, gt_iff_lt]
            apply lt_of_lt_of_le
            exact ih
            have eq2 : ZMod.val (2 : ZMod p) = 2 := by
              rw [ZMod.val_two_eq_two_mod]
              match heq : p with
              | 0 => rfl
              | 1 =>
                rw [heq] at inst
                exfalso
                exact Nat.not_prime_one inst.out
              | 2 =>
                exfalso
                apply inst'.out
                exact heq
              | .succ (.succ (.succ _)) => rfl
            have p_eq : (p - 1) + 1 = p := by
                    apply Nat.sub_add_cancel
                    by_contra h'
                    simp only [not_le, Nat.lt_one_iff] at h'
                    apply Nat.not_prime_zero (h' ▸ inst.out)
            rcases h'.1 with h' | h'
            · rw [h', zero_add]
              apply Nat.add_le_add
              · exact
                  Nat.pow_le_pow_right (by decide)
                    (Nat.le_add_right _ _)
              · have : 2 ^ (w + 1) = 2 ^ w * 2 := by ring
                rw [this, mul_assoc]
                apply Nat.mul_le_mul_left
                rw [@ZMod.val_mul]
                rw [eq2]
                exact Nat.mod_le _ _
            · rw [h']
              have : (1 + 2 * acc).val = (2 * acc).val + 1 ∨ (1 + 2 * acc).val = 0 := by
                rw [ZMod.val_add]
                by_cases h : (2 * acc).val = p - 1
                · rw [h]
                  right
                  rw [ZMod.val_one]
                  rw [Nat.add_comm]
                  rw [p_eq]
                  exact Nat.mod_self _
                · have : (2 * acc).val < p - 1 := by
                    have : (2 * acc).val < p := by
                      exact ZMod.val_lt (2 * acc)
                    rw [←Nat.add_one_le_iff, le_iff_eq_or_lt] at this
                    rcases this with this | this
                    · simp [←this] at h
                    · linarith
                  left
                  rw [ZMod.val_one, add_comm]
                  apply Nat.mod_eq_of_lt
                  linarith
              rcases this with this | this <;> rw [this]
              · rw [Nat.mul_add, mul_one, add_comm _ (2 ^ w), ←add_assoc, ←Nat.two_pow_succ, add_le_add_iff_left]
                have : 2 ^ (w + 1) = 2 ^ w * 2 := by ring
                rw [this, mul_assoc]
                apply Nat.mul_le_mul_left
                rw [@ZMod.val_mul, eq2]
                exact Nat.mod_le _ _
              · rw [mul_zero, add_zero]
                exact
                  Nat.le_add_right_of_le
                    (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
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

#check List.foldr

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
