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

-- This Field instance is used for examples and tests
namespace F7
abbrev F := ZMod 7
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Coe F Nat where
  coe f := f.val
end F7

variable {p : ℕ}
variable {var : Type}

inductive Exp (p:ℕ) (var : Type) where
  | v : var -> Exp p var
  | c : ZMod p -> Exp p var
  | add : Exp p var -> Exp p var -> Exp p var
  | mul : Exp p var -> Exp p var -> Exp p var
  | sub : Exp p var -> Exp p var -> Exp p var
  deriving DecidableEq

abbrev Expₑ (p : Nat) := Exp p (ZMod p)

namespace Exp

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

instance {n : ℕ} : OfNat (Exp p var) n where
  ofNat := (n : ZMod p)

/- In this example, variables can only be substitued by Field elements,
   so .v and .c are equivalent, which is ok for evaluation -/
example : Expₑ p := (.c 1) + (.v 2)

/- In this example, variables can be substitued by expressions,
   which is what we need for some optimizations. -/
example : Exp p (Exp p var) := (.c 1) + (.v ((.c 2) + (.c 2)))

variable [Fact (Nat.Prime p)]

def eval (e : Expₑ p) : ZMod p :=
  match e with
  | .v f => f
  | .c i => i
  | .add l r => eval l + eval r
  | .mul l r => eval l * eval r
  | .sub l r => eval l - eval r

section

variable {x₁ x₂ : ZMod p} {e e₁ e₂ e₃ e₄: Expₑ p} {k : ℕ}

def equiv (e₁ e₂ : Expₑ p) : Prop := e₁.eval = e₂.eval

instance : Setoid (Expₑ p) where
  r := Exp.equiv
  iseqv := Equivalence.comap eq_equivalence Exp.eval -- Just pullback the proof.

private lemma equiv_iff_eval_eq_eval : e₁ ≈ e₂ ↔ e₁.eval = e₂.eval := by rfl

@[simp]
lemma eval_ofNat : (no_index(OfNat.ofNat k) : Expₑ p).eval = k := rfl

@[simp]
lemma eval_add : (e₁ + e₂).eval = e₁.eval + e₂.eval := rfl

@[simp]
lemma eval_mul : (e₁ * e₂).eval = e₁.eval * e₂.eval := rfl

@[simp]
lemma eval_sub : (e₁ - e₂).eval = e₁.eval - e₂.eval := rfl

@[simp]
lemma c_add_c_equiv_c_add : Exp.c (var := ZMod p) (x₁ + x₂) ≈ Exp.c x₁ + Exp.c x₂ := rfl

example : 3 + 4 ≈ (7 : Expₑ p) := by
  -- show eval _ = eval _
  -- simp [eval]
  -- norm_num
  symm
  convert c_add_c_equiv_c_add
  norm_num
  rfl

-- for grw and gcongr
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

end

end Exp

inductive denotation (F : Type) : Type where
  | n : denotation F
  | u : denotation F
  | l : (F -> denotation F) -> denotation F

inductive Circuit (p : ℕ) (var : Type) : Type where
  | nil : Circuit p var
  | eq0 : Exp p var -> Circuit p var -> Circuit p var
  | lam : (var -> Circuit p var) -> Circuit p var
  | share : Exp p var -> (var -> Circuit p var) -> Circuit p var
  | is_zero : Exp p var -> (var -> Circuit p var) -> Circuit p var
  | assert_range : (w : ℕ) -> Exp p var -> Circuit p var -> Circuit p var
  | div_rem : Exp p var -> (var × var -> Circuit p var) -> Circuit p var

abbrev Circuitₑ (p : ℕ) := Circuit p (ZMod p)
-- TODO remove all ' definitions
abbrev Circuit' (p : ℕ) : Type _ := (var:Type) -> Circuit p var

/-
  Warning: var must be kept abstract, if var is fixed we can write bogus examples
-/

-- E.g. here v 0 is not bound by any lam
example : Circuit p Nat := Circuit.eq0 (.v 0) Circuit.nil

-- This is the right way, keeping var abstract
example : Circuit p var := .lam (fun x => .eq0 (.v x) .nil)


namespace Circuit

@[reducible]
def curry (n : ℕ) (body : Vector var n -> Circuit p var) : Circuit p var :=
  match n with
  | 0 => body ⟨#[], by rfl⟩
  | n+1 => .lam (fun x:var => curry n (fun l => body (l.append ⟨#[x],by rfl⟩) ))


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
  letI go2 (l : ℕ) (k : var × var → Circuit p var) := repr (l+2) (k (index l, index (l+1))) -- `k ∘ index : ℕ (→ var) → Circuit ..`
  match c with
  | .nil => "nil"
  | .lam k => s!"λ{l} {go l k}"
  | .eq0 e c => s!"eq0 {_root_.repr e} {repr l c}"
  | .share e k => s!"share {_root_.repr e} {go l k}"
  | .is_zero e k => s!"is_zero {_root_.repr e} {go l k}"
  | .assert_range w e c => s!"assert_range {w} {_root_.repr e} {repr l c}"
  | .div_rem e k => s!"div_rem {_root_.repr e} {go2 l k}"

instance [Repr var] [Index var] : Repr (Circuit p var) where
  reprPrec c _ := c.repr 0

instance [Repr var] [Index var] : ToString (Circuit p var) :=
  ⟨Std.Format.pretty ∘ repr 0⟩

namespace Test

instance : Fact (Prime 7) := by
  refine { out := ?_ }
  decide

def a : Circuit' 7 := fun _ => .lam (fun x => .lam (fun y => .eq0 (.v x + .v y) .nil))

#guard s!"{a Nat}" = "λ0 λ1 eq0 (v0 + v1) nil"

end Test

variable [Fact (Nat.Prime p)]

def eval (c : Circuitₑ p) : denotation (ZMod p) :=
  match c with
  | .nil => .u
  | .lam k => .l (fun x => eval (k x))
  | .eq0 e c =>
    if Exp.eval e = 0 then eval c else .n
  | .share e k => eval (k (Exp.eval e))
  | .is_zero e k =>
    if Exp.eval e = 0 then eval (k 1) else eval (k 0)
  | .assert_range w e c =>
    let e := Exp.eval e
    if e.val < 2^w then eval c else .n
  | .div_rem e k =>
    let e := Exp.eval e
    let d := e / 256
    let r := e % 256
    eval (k (d,r))

def eval' (c : Circuit' p) : denotation (ZMod p) := eval (c (ZMod p))

@[simp]
lemma eval_eq0 {e : Expₑ p} {c : Circuitₑ p} :
  (eq0 e c).eval = if e.eval = 0 then c.eval else .n := by
  simp [Circuit.eval]

@[simp]
lemma eval_lam {c : ZMod p → Circuitₑ p} :
  (lam c).eval = .l fun x ↦ (c x).eval := by
  simp [Circuit.eval]

@[simp]
lemma eval_share {e : Expₑ p} {k : ZMod p → Circuitₑ p} :
  (share e k).eval = (k e.eval).eval := by
  simp [Circuit.eval]

@[simp]
lemma eval_is_zero {e : Expₑ p} {k : ZMod p → Circuitₑ p} :
  (is_zero e k).eval = if e.eval = 0 then (k 1).eval else (k 0).eval := by
  simp [Circuit.eval]

@[simp]
lemma eval_assert_range {w:ℕ} {e : Expₑ p} {c : Circuitₑ p} :
  (assert_range w e c).eval =
    let e := Exp.eval e
    if e.val < 2^w then eval c else .n := by
  simp [Circuit.eval]

def equiv (c₁ c₂ : Circuitₑ p) : Prop := eval c₁ = eval c₂

instance : Setoid (Circuitₑ p) where
  r := equiv
  iseqv := Equivalence.comap eq_equivalence eval -- Just pullback the proof.

private lemma Circuit.equiv_iff_eval_eq_eval {c₁ c₂ : Circuitₑ p} :
  c₁ ≈ c₂ ↔ c₁.eval = c₂.eval := by rfl

instance : IsRefl (Circuitₑ p) (· ≈ ·) := inferInstance -- This is by `inferInstance`, which means it need not exist altogether.

section

variable {el er : Expₑ p} {cl cr : Circuitₑ p} {kl kr : ZMod p → Circuitₑ p}

@[gcongr]
theorem eq0_congr (he : el ≈ er) (hc: cl ≈ cr) :
  eq0 el cl ≈ eq0 er cr := by
   aesop (add simp [Exp.equiv_iff_eval_eq_eval, Circuit.equiv_iff_eval_eq_eval])

@[gcongr]
theorem lam_congr : (∀ x, kl x ≈ kr x) ->
  lam kl ≈ lam kr := by
  aesop (add simp [Exp.equiv_iff_eval_eq_eval, Circuit.equiv_iff_eval_eq_eval])

@[gcongr]
theorem share_congr (he: el ≈ er) (h : ∀ x, kl x ≈ kr x) :
  share el kl ≈ share er kr := by
  aesop (add simp [Exp.equiv_iff_eval_eq_eval, Circuit.equiv_iff_eval_eq_eval])

@[gcongr]
theorem is_zero_congr (he: el ≈ er) (h: ∀ x, kl x ≈ kr x) :
  is_zero el kl ≈ is_zero er kr := by
  aesop (add simp [Exp.equiv_iff_eval_eq_eval, Circuit.equiv_iff_eval_eq_eval])

@[gcongr]
theorem assert_range_congr w (he: el ≈ er) (hc: cl ≈ cr) :
  assert_range w el cl ≈ assert_range w er cr := by
  aesop (add simp [Exp.equiv_iff_eval_eq_eval, Circuit.equiv_iff_eval_eq_eval])

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
