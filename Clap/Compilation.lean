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

def Csₑ (p:Nat) : Type := Cs p (ZMod p)
def Cs' (p:Nat) : Type _ := (var:Type) -> Cs p var

variable {p : ℕ} {var : Type} [inst : Fact (Nat.Prime p)] [inst' : Fact (p ≠ 2)]

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
def Cs.curry (n:ℕ) (k:Vector var n -> Cs p var) : Cs p var :=
  match n with
  | 0 => k #v[]
  | n+1 => .lam (fun x:var => Cs.curry n (fun l => k (l.push x) ))

def assert_bit_e (b:var) (rest: Cs p var) : Cs p var :=
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

def assert_bits_e {w:ℕ} (bs:Vector var w) (rest: Cs p var) : Cs p var :=
  Vector.foldr assert_bit_e rest bs

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

def assert_bits (args : List (ZMod p)) : Bool :=
  List.all args (fun (x : ZMod p) => x == 0 ∨ x == 1)

lemma bits2num_val_lt_2_pow_w_of_assert_bits  {args : List (ZMod p)} : assert_bits args → (bits2num args).val < 2 ^ args.length := by
        intro cond₁
        unfold assert_bits at cond₁
        simp only [beq_iff_eq, Bool.decide_or, List.all_eq_true, Bool.or_eq_true,
          decide_eq_true_eq] at cond₁
        rw [bits2num_spec]
        have {w : ℕ} {f : Fin w → ZMod p} : (∑ i, f i).val = (∑ i, (f i).val) % p := by
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
        have : ∑ i : Fin args.length, (2 ^ i.1 * args[i]).val ≤ ∑ i : Fin args.length, 2 ^ i.1 := by
          have {α : Type} [Fintype α] {f g : α → ℕ} : (∀ i, f i ≤ g i) → ∑ i, f i ≤ ∑ i, g i :=
            fun a => Finset.sum_le_sum fun i a_1 => a i
          apply this
          intros i
          specialize cond₁ args[i] (by simp)
          rcases cond₁ with cond₁ | cond₁
          · simp [cond₁]
          · simp [cond₁]
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
        clear this
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
      letI rest := (c bits.toList).toCs
      letI rest := Cs.eq0 (bits2num_e bits.toArray.toList - e) rest
      assert_bits_e bits rest)

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

theorem soundness {c : Circuitₑ p} : wrBisim c.eval c.toCs.eval := by
  induction c with
  | nil =>
    simp [Circuit.eval,Circuit.toCs]
    constructor
  | lam k h =>
    simp [Circuit.eval,Circuit.toCs]
    constructor
    exact h
  | eq0 e c h =>
    simp [Circuit.eval,Cs.eval,Circuit.toCs]
    split
    apply h
    constructor
  | share e c h =>
    simp [Circuit.eval,Cs.eval,Circuit.toCs]
    apply wrBisim.right
    intro x
    simp [Exp.eval]
    split
    have hmy : x = Exp.eval e := by grind
    rw [<-hmy]
    apply h
    constructor
  | is_zero e c h =>
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
          apply h
        case isFalse hmul => constructor
      case isFalse hsub => constructor
    case is_zero.h.h.isFalse he0 =>
      -- aesop
      split
      case isTrue hsub =>
        split
        case isTrue hmul =>
          aesop
        case isFalse hmul => constructor
      case isFalse hsub => constructor
  | num2bits w e c h =>
      sorry

theorem soundness' {c:Circuit' p} :
  wrBisim (Circuit.eval' c) (eval' (toCs' c)) := by
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
