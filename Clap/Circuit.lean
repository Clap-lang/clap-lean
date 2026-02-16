import Clap.BitVec
import Clap.Wheels
import Mathlib.FieldTheory.Finite.Basic -- field operations

/-
  This file introduces the main data structure of the project, the
  Circuit. We follow the Phoas (Parametric higher-order abstract
  syntax) approach developed by Chlipala in his book
  [CPDT](http://adam.chlipala.net/cpdt/html/Cpdt.ProgLang.html)

  An important distinction is that our language is first-order, our
  continuations cannot take circuits as argument, they can only take
  Field element or something equivalent, like an expression.
  For this reason we have a distinction between Exp, which contains
  the important constructor `var`, and Circuit, which has continuation
  that receive `var` as argument.

  We follow the Phoas approach of using type-theoretic semantics where
  definitional compilers lower our syntax into Lean's objects.
  See the `denotation` type for more details.

  Importantly the language supports partial functions, as Circuits can
  have assertions.

  Equality (≈) between circuits is defined over their denotations and
  it's shown to be a congruence with respect to the Circuit
  constructors.
-/

namespace Clap

inductive Exp (p : ℕ) (var : Type) where
  | v   (_ : var)
  | c   (_ : ZMod p)
  | add (_ _ : Exp p var)
  | mul (_ _ : Exp p var)
  | sub (_ _ : Exp p var)
  deriving DecidableEq

abbrev Expₑ (p : Nat) := Exp p (ZMod p)

namespace Exp

variable {p : ℕ} {var : Type} {n : ℕ}

instance [Repr var] : Repr (Exp p var) where
  reprPrec expr _ := go expr
  where go (e : Exp p var) : Std.Format :=
    match e with
    | .v s => s!"v{repr s}"
    | .c n => s!"{repr n}"
    | .add e1 e2 => s!"({go e1} + {go e2})"
    | .mul e1 e2 => s!"({go e1} * {go e2})"
    | .sub e1 e2 => s!"({go e1} - {go e2})"

instance : Add (Exp p var) where
  add a b := .add a b

instance : Mul (Exp p var) where
  mul a b := .mul a b

instance : Sub (Exp p var) where
  sub a b := .sub a b

-- The typeclasses above add an abstraction layer,
-- these lemmas show how to go through it
section

variable {e₁ e₂ : Exp p var}

lemma add_def : e₁ + e₂ = .add e₁ e₂ := rfl

lemma mul_def : e₁ * e₂ = .mul e₁ e₂ := rfl

lemma sub_def : e₁ - e₂ = .sub e₁ e₂ := rfl

end

instance : Coe (ZMod p) (Exp p var) where
  coe := .c

instance : OfNat (Exp p var) n where
  ofNat := (n : ZMod p)

/- In this example, variables can only be substitued by Field elements,
   so .v and .c are equivalent, which is ok for evaluation -/
example : Expₑ p := (.c 1) + (.v 2)

/- In this example, variables can be substitued by expressions,
   which is what we need for some optimizations. -/
example : Exp p (Exp p var) := (.c 1) + (.v ((.c 2) + (.c 2)))

def eval (e : Expₑ p) : ZMod p :=
  match e with
  | .v f => f
  | .c i => i
  | .add l r => eval l + eval r
  | .mul l r => eval l * eval r
  | .sub l r => eval l - eval r

section

variable {x x₁ x₂ : ZMod p} {e e₁ e₂ e₃ e₄: Expₑ p} {k : ℕ}

def equiv (e₁ e₂ : Expₑ p) : Prop := e₁.eval = e₂.eval

instance : Setoid (Expₑ p) where
  r := Exp.equiv
  iseqv := Equivalence.comap eq_equivalence Exp.eval -- Just pullback the proof.

lemma equiv_iff_eval_eq_eval : e₁ ≈ e₂ ↔ e₁.eval = e₂.eval := by rfl

@[simp]
lemma eval_ofNat : (no_index(OfNat.ofNat k) : Expₑ p).eval = k := rfl

@[simp]
lemma eval_add : (e₁ + e₂).eval = e₁.eval + e₂.eval := rfl

@[simp]
lemma eval_mul : (e₁ * e₂).eval = e₁.eval * e₂.eval := rfl

@[simp]
lemma eval_sub : (e₁ - e₂).eval = e₁.eval - e₂.eval := rfl

@[simp, grind .]
lemma c_add_c_equiv_c_add : Exp.c (var := ZMod p) (x₁ + x₂) ≈ Exp.c x₁ + Exp.c x₂ := rfl

@[grind =]
lemma coe_eq_c : (x : Expₑ p) = .c x := rfl


@[simp, grind =]
lemma ofNat_eq_coe_coe : OfNat.ofNat (α := Expₑ p) n = ((n : ZMod p) : Expₑ p) := rfl

@[gcongr]
theorem add_congr (h1 : e₁ ≈ e₂) (h2 : e₃ ≈ e₄) :
  e₁ + e₃ ≈ e₂ + e₄ := by
  aesop (add simp [equiv_iff_eval_eq_eval])

example (h₁ : e₁ ≈ e₂) (h₂ : e₃ ≈ e₄) : e₁ + e₃ ≈ e₂ + e₄ := by
  grw [h₁, h₂]

@[gcongr]
theorem mul_congr (h1 : e₁ ≈ e₂) (h2 : e₃ ≈ e₄) :
  e₁ * e₃ ≈ e₂ * e₄ := by
    aesop (add simp [equiv_iff_eval_eq_eval])

@[gcongr]
theorem sub_congr (h1 : e₁ ≈ e₂) (h2 : e₃ ≈ e₄) :
    e₁ - e₃ ≈ e₂ - e₄ := by
  aesop (add simp [equiv_iff_eval_eq_eval])

example : 3 + 4 ≈ (7 : Expₑ p) := by
  simp
  symm
  convert c_add_c_equiv_c_add
  grind

end

end Exp

inductive denotation (F : Type) : Type where
  | n
  | u
  | l (_ : F → denotation F)

inductive Circuit (p : ℕ) (var : Type) : Type where
  | nil
  | eq0 (e : Exp p var) (c : Circuit p var)
  | lam (cont : var → Circuit p var)
  | share (e : Exp p var) (cont : var → Circuit p var)
  | is_zero (e : Exp p var) (cont : var → Circuit p var)
  | num2bits (w : ℕ) (e : Exp p var) (cont : List var → Circuit p var)

abbrev Circuitₑ (p : ℕ) := Circuit p (ZMod p)
-- TODO remove all ' definitions
abbrev Circuit' (p : ℕ) : Type _ := (var : Type) -> Circuit p var

/-
  Warning: var must be kept abstract, if var is fixed we can write bogus examples
-/

-- E.g. here v 0 is not bound by any lam
example {p} : Circuit p Nat := Circuit.eq0 (.v 0) Circuit.nil

-- This is the right way, keeping var abstract
example {p} {var} : Circuit p var := .lam fun x => .eq0 (.v x) .nil

namespace Circuit

variable {p : ℕ} {var : Type}

/--
In order to print a Circuit we need to turn variables into Debrujin levels. We need a family of types that map from ℕ.

One could argue that `OfNat` might do, but it's dependent on a value so there's more friction.
-/
class Index (var : outParam Type) where
  index : ℕ → var

instance [Index var] : Coe ℕ var := ⟨Index.index⟩

instance : Index String := ⟨ToString.toString⟩

instance : Index ℕ := ⟨id⟩

export Index (index)

def repr [Repr var] [Index var]
  (l : ℕ) (c : Circuit p var) : Std.Format :=
  letI go (l : ℕ) (k : var → Circuit p var) := repr (l+1) (k (index l)) -- `k ∘ index : ℕ (→ var) → Circuit ..`
  letI gos (w l : ℕ) (k : List var → Circuit p var) := repr (l+w) (k ((List.range w).map index))
  match c with
  | .nil => "nil"
  | .lam k => s!"λ{l} {go l k}"
  | .eq0 e c => s!"eq0 {_root_.repr e} {repr l c}"
  | .share e k => s!"share {_root_.repr e} {go l k}"
  | .is_zero e k => s!"is_zero {_root_.repr e} {go l k}"
  | .num2bits w e k => s!"num2bits {w} {_root_.repr e} {gos w l k}"

instance [Repr var] [Index var] : Repr (Circuit p var) where
  reprPrec c _ := c.repr 0

instance [Repr var] [Index var] : ToString (Circuit p var) :=
  ⟨Std.Format.pretty ∘ repr 0⟩

namespace Test

def a : Circuit' 7 := fun _ => .lam (fun x => .lam (fun y => .eq0 (.v x + .v y) .nil))

#guard s!"{a Nat}" = "λ0 λ1 eq0 (v0 + v1) nil"

end Test

variable [Fact (Nat.Prime p)]

def eval : Circuitₑ p → denotation (ZMod p)
  | .nil =>
      .u
  | .lam k =>
      .l fun x => eval (k x)
  | .eq0 e c =>
      if e.eval = 0 then eval c else .n
  | .share e k =>
      (k e.eval).eval
  | .is_zero e k =>
      if e.eval = 0 then (k 1).eval else (k 0).eval
  | .num2bits w e k =>
      if e.eval.val < 2^w then (k (num2bitsLsbPure w e.eval)).eval else .n

def eval' (c : Circuit' p) : denotation (ZMod p) := eval (c (ZMod p))

variable {e : Expₑ p} {c : Circuitₑ p} {cont : ZMod p → Circuitₑ p}

@[simp]
lemma eval_eq0 :
  (eq0 e c).eval = if e.eval = 0 then c.eval else .n := rfl

@[simp]
lemma eval_lam : (lam cont).eval = .l fun x ↦ (cont x).eval := rfl

@[simp]
lemma eval_share : (share e cont).eval = (cont e.eval).eval := rfl

@[simp]
lemma eval_is_zero :
  (is_zero e cont).eval = if e.eval = 0 then (cont 1).eval else (cont 0).eval := rfl

@[simp]
lemma eval_num2bits {w : ℕ} {k: List (ZMod p) -> Circuitₑ p} :
  (num2bits w e k).eval = if e.eval.val < 2^w then (k (num2bitsLsbPure w e.eval)).eval else .n := by rfl

def equiv (c₁ c₂ : Circuitₑ p) : Prop := c₁.eval = c₂.eval

instance : Setoid (Circuitₑ p) where
  r := equiv
  iseqv := Equivalence.comap eq_equivalence eval -- Just pullback the proof.

lemma equiv_iff_eval_eq_eval {c₁ c₂ : Circuitₑ p} :
  c₁ ≈ c₂ ↔ c₁.eval = c₂.eval := by rfl

section

variable {el er : Expₑ p} {cl cr : Circuitₑ p} {kl kr : ZMod p → Circuitₑ p}

attribute [local simp] Exp.equiv_iff_eval_eq_eval Circuit.equiv_iff_eval_eq_eval

@[gcongr]
theorem eq0_congr (he : el ≈ er) (hc: cl ≈ cr) :
  eq0 el cl ≈ eq0 er cr := by
   aesop

@[gcongr]
theorem lam_congr (h: ∀ x, kl x ≈ kr x) :
  lam kl ≈ lam kr := by
  aesop

@[gcongr]
theorem share_congr (he : el ≈ er) (h : ∀ x, kl x ≈ kr x) :
  share el kl ≈ share er kr := by
  aesop

@[gcongr]
theorem is_zero_congr (he : el ≈ er) (h: ∀ x, kl x ≈ kr x) :
  is_zero el kl ≈ is_zero er kr := by
  aesop

@[gcongr]
theorem num2bits_congr {w : ℕ} {kl kr : List (ZMod p) -> Circuitₑ p} (he: el ≈ er) (hk: ∀ x, kl x ≈ kr x) :
  num2bits w el kl ≈ num2bits w er kr := by
  aesop

end

def equiv' (c1 c2 : Circuit' p) : Prop := eval' c1 = eval' c2

instance : Setoid (Circuit' p) where
  r := equiv'
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

instance : IsRefl (Circuit' p) (· ≈ ·) where
  refl := Setoid.refl

end Circuit

end Clap
