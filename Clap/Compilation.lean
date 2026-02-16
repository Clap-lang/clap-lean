import Mathlib.FieldTheory.Finite.Basic -- field operations

import Clap.Wheels
import Clap.Circuit
import Clap.Simulation

namespace Clap

/-
  This file introduces our "target language" `Cs` for Constraint System.
  Cs is a strict subset of Circuit and so is its evaluation function.
  A Circuit can be compiled to a Cs using `to_cs`, which introduces
  extra inputs (`lam`) to receive all the values that could be
  computed by the Circuit but can only be checked by a Cs.

  Soundness.
  In order to show that a Cs is not more accepting that its original
  Circuit, i.e. that it won't accept more inputs, we show that there
  is a right-weak bisimulation `wrBisim` between them.
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
  | nil
  | eq0 (_ : Exp p var) (_ : Cs p var)
  | lam (_ : var -> Cs p var)

def Csₑ (p : ℕ) : Type := Cs p (ZMod p)
def Cs' (p : ℕ) : Type _ := (var : Type) -> Cs p var

variable {p : ℕ} {var : Type} [inst : Fact (Nat.Prime p)] [inst' : Fact (p > 2)]

open Clap.Circuit in
def Cs.repr [Repr var] [Clap.Circuit.Index var]
  (l : ℕ) (c : Cs p var) : Std.Format :=
  letI go (l : ℕ) (k : var → Cs p var) := repr (l+1) (k (index l))
  match c with
  | .nil => "nil"
  | .lam k => s!"λ{l} {go l k}"
  | .eq0 e c => s!"eq0 {_root_.repr e} {repr l c}"

instance [Repr var] [Clap.Circuit.Index var] : Repr (Cs p var) where
  reprPrec c _ := c.repr 0

instance [Repr var] [Clap.Circuit.Index var] : ToString (Cs p var) :=
  ⟨Std.Format.pretty ∘ Cs.repr 0⟩

def Cs.eval (c : Cs p (ZMod p)) : denotation (ZMod p) :=
  match c with
  | .nil => .u
  | .lam k => .l fun x => (k x).eval
  | .eq0 e c => if e.eval = 0 then c.eval else .n

def eval' (cs:Cs' p) : denotation (ZMod p) := (cs (ZMod p)).eval

@[reducible]
def Cs.curry (n : ℕ) (k : Vector var n -> Cs p var) : Cs p var :=
  match n with
  | 0 => k #v[]
  | n+1 => .lam (fun (x : var) => Cs.curry n (fun l => k (l.push x) ))

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

omit inst in
omit inst' in
lemma rw_bisim_uncurry : ∀ (w : ℕ) (d : denotation (ZMod p)) (k : Vector (ZMod p) w -> Cs p (ZMod p)),
 (∀ args : Vector (ZMod p) w, Simulation.wrBisim d (k args).eval) ->
 Simulation.wrBisim d (Cs.curry _ k).eval := by
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
  generalize e_eq : Exp.c 0 = e
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
  unfold Exp.eval
  rw [bits2num_spec] at h
  rw [bits2num_eq_eval_bits2num_e, h, bits2num_spec]
  simp

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
  unfold Cs.eval Exp.eval
  rw [bits2num_eq_eval_bits2num_e]
  split_ifs with h'
  · exfalso
    apply h
    rw [sub_eq_zero, eq_comm] at h'
    rw [h']
  · rfl

omit inst' in
lemma fail : ∀ {args : List (ZMod p)} {e : Expₑ p} {cs : Cs p (ZMod p)},
 (¬ (assert_bits args /\ e.eval = bits2num args)) ->
 (assert_bits_e args (.eq0 (bits2num_e args - e) cs)).eval = denotation.n := by
  intros args e cs h
  by_cases h' : assert_bits args
  · rw [reduce₁ h', fail₂ (by tauto)]
  · rw [fail₁ h']

def Circuit.toCs (c : Circuit p var) : Cs p var :=
  match c with
  | .nil =>
      .nil
  | .eq0 e c =>
      .eq0 e c.toCs
  | .lam k =>
      .lam fun x => (k x).toCs
  | .share e k =>
      .lam fun o => .eq0 (e - .v o) (k o).toCs
  | .is_zero e k =>
    .lam fun inv =>
      .lam fun o =>
        .eq0 (.c 1 - .v inv * e - .v o)
          (.eq0 (.v o * e) (k o).toCs)
     -- e=0          o=1
     -- e≠0 inv=e^-1 o=0
  | .num2bits w e c =>
    Cs.curry w (fun bits =>
      let ls := bits.toArray.toList
      letI rest := (c bits.toList).toCs
      letI rest := Cs.eq0 (bits2num_e ls - e) rest
      assert_bits_e ls rest)

def toCs' (c : Circuit' p) : Cs' p := fun var => (c var).toCs

inductive Wg (p : ℕ) : Type where
  | nil
  | cons (_ : ZMod p) (_ : Wg p)
  | input (_ : ZMod p → Wg p)

def Wg.repr (l : ℕ) (c : Wg p) : Std.Format :=
  letI go (l : ℕ) (k : (ZMod p) → Wg p) := repr (l+1) (k l)
  match c with
  | .nil => "[]"
  | .cons e c => s!"{_root_.repr e} :: {repr l c}"
  | .input k => s!"λ{l} {go l k}"

instance : Repr (Wg p) where
  reprPrec c _ := c.repr 0

instance : ToString (Wg p) :=
  ⟨Std.Format.pretty ∘ Wg.repr 0⟩

def Circuit.toWg (c : Circuitₑ p) : Wg p :=
  match c with
  | .nil => Wg.nil
  | .eq0 _ c => c.toWg
  | .lam k => Wg.input fun i => (k i).toWg
  | .share e k =>
    letI e := e.eval
    .cons e (k e).toWg
  | .is_zero e k =>
    letI e := e.eval
    let o : ZMod p := if e = 0 then 1 else 0
    .cons e⁻¹ (.cons o (k o).toWg)
  | .num2bits w e c =>
    letI bits := num2bitsLsbPure w (Exp.eval e)
    List.foldl (fun acc b => .cons b acc) (c bits).toWg bits

def toWg' (c:Circuit' p) : Wg p := (c (ZMod p)).toWg

def Wg.run {p : Nat} [Fact (Nat.Prime p)] (wg : Wg p) (ins : Array (ZMod p)) : Array (ZMod p) :=
  match wg with
  | .nil => #[]
  | .cons x wg => ⟨x::(wg.run ins).toList⟩
  | .input k =>
    match ins with
    | ⟨[]⟩ => #[]
    | ⟨i::ins⟩ => (k i).run ins.toArray

def wrap (wg : Wg p) (cs : Cs p (ZMod p)) : Cs p (ZMod p) :=
  match wg,cs with
  |         .nil , .nil      => .nil
  |           wg , .eq0 e cs => .eq0 e (wrap wg cs)
  | Wg.input kwg , .lam k    => .lam fun x => wrap (kwg x) (k x)
  |   .cons x wg , .lam k    => wrap (wg : Wg p) (k x)
  |            _ , _         => .eq0 (.c 1) .nil -- needed because we don't have typed wg and cs

open Simulation

def circuitWF : Circuitₑ p → Prop
| .nil => True
| .eq0 _ c => circuitWF c
| .lam c => ∀ i, circuitWF (c i)
| .share _ c => ∀ i, circuitWF (c i)
| .is_zero _ c => ∀ i, circuitWF (c i)
| .num2bits w _ c => 2 ^ w < p ∧ ∀ i, circuitWF (c i)


theorem soundness {c : Circuitₑ p} : circuitWF c → wrBisim c.eval c.toCs.eval := by
  induction c with
  | nil =>
    intros h
    simp [Circuit.eval,Circuit.toCs]
    constructor
  | lam k ih =>
    intros h
    unfold circuitWF at h
    simp [Circuit.eval,Circuit.toCs]
    constructor
    exact fun x ↦ ih _ (h x)
  | eq0 e c ih =>
    intros h
    simp [Circuit.eval,Cs.eval,Circuit.toCs]
    split
    apply ih h
    constructor
  | share e c ih =>
    intros h
    simp [Circuit.eval,Cs.eval,Circuit.toCs]
    apply wrBisim.right
    intro x
    simp [Exp.eval]
    split
    have hmy : x = Exp.eval e := by grind
    rw [<-hmy]
    apply ih _ (h x)
    constructor
  | is_zero e c ih =>
    intros h
    apply wrBisim.right
    intro inv
    apply wrBisim.right
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
          apply ih _ (h 1)
        case isFalse hmul => constructor
      case isFalse hsub => constructor
    case is_zero.h.h.isFalse he0 =>
      split
      case isTrue hsub =>
        split
        case isTrue hmul => aesop
        case isFalse hmul => constructor
      case isFalse hsub => constructor
  | num2bits w e c ih =>
      rintro ⟨inv, h⟩
      simp [Circuit.eval, Circuit.toCs]
      apply rw_bisim_uncurry
      intros args
      by_cases cond₁ : assert_bits args.toArray.toList <;> by_cases cond₂ : Exp.eval e = bits2num args.toArray.toList
      · rw [reduce ⟨cond₁, cond₂⟩]
        have : e.eval.val < 2 ^ w := by
          have : w = args.toArray.toList.length := by
            rw [Array.length_toList, Vector.size_toArray]
          simp only [cond₂, this]
          exact bits2num_val_lt_2_pow_w_of_assert_bits cond₁
        simp [this]
        have : (num2bitsLsbPure w (bits2num args.toList)) = args.toList := by
          rw [assert_bits_spec] at cond₁
          have : args.toArray.toList.length = w := by simp
          convert num2bitsLsbPure_of_bits2num_eq (by convert inv) cond₁
          exact this.symm
        unfold Vector.toList at this
        rw [cond₂, this]
        exact ih _ (h args.toArray.toList)
      · rw [reduce₁ cond₁, fail₂ cond₂]
        exact wrBisim.none
      · rw [fail₁ cond₁]
        exact wrBisim.none
      · rw [fail₁ cond₁]
        exact wrBisim.none


theorem soundness' {c : Circuit' p} :
  circuitWF (c (ZMod p)) → wrBisim (Circuit.eval' c) (eval' (toCs' c)) := by
  apply soundness


def completeness [Fact (Nat.Prime p)] {c : Circuitₑ p} :
  c.eval = (wrap c.toWg c.toCs).eval := by
  induction c with
  | nil =>
    simp [Circuit.eval,Circuit.toCs,Circuit.toWg,wrap]
    constructor
  | lam k h =>
    simp [Circuit.eval,Cs.eval,Circuit.toCs,Circuit.toWg,wrap]
    funext
    apply h
  | eq0 e c h =>
    simp [Circuit.eval,Cs.eval,Circuit.toCs,Circuit.toWg,wrap]
    split
    exact h
    constructor
  | share e c h =>
    simp [Exp.eval,Circuit.eval,Cs.eval,Circuit.toCs,Circuit.toWg,wrap]
    apply h
  | is_zero e c h =>
    simp [Exp.eval,Circuit.eval,Cs.eval,Circuit.toCs,Circuit.toWg,wrap]
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
  | num2bits e c h =>
    sorry
