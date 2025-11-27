import Mathlib.Data.ZMod.Basic
-- import Mathlib.Data.ZMod.Defs
-- import Mathlib.FieldTheory.Finite.Basic -- field operations
-- import Mathlib.Algebra.Field.Defs
-- import Mathlib.Algebra.Field.Basic  -- Field typeclass instances
-- import Mathlib.Data.Set.Basic
import Mathlib.Tactic

-- import Mathlib.Data.List.Basic

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

inductive Exp (F var : Type) where
  | v : var → Exp F var
  | c : F → Exp F var
  | add : Exp F var → Exp F var → Exp F var
  | mul : Exp F var → Exp F var → Exp F var
  | sub : Exp F var → Exp F var → Exp F var

variable {F var : Type}

variable {e : Exp F var}

instance instReprExp [Repr F] [Repr var] : Repr (Exp F var) where
  reprPrec expr _ := go expr
  where go (e : Exp F var) : Std.Format :=
    match e with
    | .v s => s!"v{repr s}"
    | .c n => s!"{repr n}"
    | .add e1 e2 => s!"({go e1} + {go e2})"
    | .mul e1 e2 => s!"({go e1} * {go e2})"
    | .sub e1 e2 => s!"({go e1} - {go e2})"

instance : Add (Exp F var) where
  add a b := .add a b

instance : Mul (Exp F var) where
  mul a b := .mul a b

instance : Sub (Exp F var) where
  sub a b := .sub a b

section

variable {e₁ e₂ : Exp F var}

namespace Exp

lemma add_def : e₁ + e₂ = .add e₁ e₂ := rfl

lemma mul_def : e₁ * e₂ = .mul e₁ e₂ := rfl

lemma sub_def : e₁ - e₂ = .sub e₁ e₂ := rfl

end Exp

section

variable [OfNat F 1] [OfNat F 2] [OfNat var 2]

-- we can only substitute F for variables so .v and .c are equivalent, which is ok for evaluation
private example : Exp F var := .c 1 + .v 2
-- we can substitute expressions for variables, which is what we need for optimizations
private example : Exp F (Exp F var) := .c 1 + .v (.c 2 + .c 2)

end

-- Separate note:
-- I just assume `Ring F` to get `+`, `*` and `-`. There are more general interpretations.
section

variable [Ring F]

/--
`Expₑ` once we start `eval`uating.
-/
abbrev Expₑ (F : Type) := Exp F F

def Exp.eval (e : Expₑ F) : F := 
  match e with
  | .v val => val
  | .c i => i
  | .add l r => l.eval + r.eval
  | .mul l r => l.eval * r.eval
  | .sub l r => l.eval - r.eval

instance : Coe F (Exp F var) where
  coe := .c

instance {n : ℕ} : OfNat (Exp F var) n where
  ofNat := (n : F)

namespace Exp

section

variable {x₁ x₂ : F} {e e₁ e₂ e₃ e₄: Expₑ F} {k : ℕ}

def equiv (e₁ e₂ : Expₑ F) : Prop := e₁.eval = e₂.eval

instance : Setoid (Expₑ F) where
  r := Exp.equiv
  iseqv := Equivalence.comap eq_equivalence Exp.eval -- Just pullback the proof.

private lemma equiv_iff_eval_eq_eval : e₁ ≈ e₂ ↔ e₁.eval = e₂.eval := by rfl

@[simp]
lemma eval_ofNat : (no_index(OfNat.ofNat k) : Expₑ F).eval = k := rfl

@[simp]
lemma eval_add : (e₁ + e₂).eval = e₁.eval + e₂.eval := rfl

@[simp]
lemma eval_mul : (e₁ * e₂).eval = e₁.eval * e₂.eval := rfl

@[simp]
lemma eval_sub : (e₁ - e₂).eval = e₁.eval - e₂.eval := rfl

@[simp]
lemma c_add_c_equiv_c_add : Exp.c (var := F) (x₁ + x₂) ≈ Exp.c x₁ + Exp.c x₂ := rfl

open Exp in
example : 3 + 4 ≈ (7 : Expₑ F) := by
  symm
  convert c_add_c_equiv_c_add
  norm_num
  rfl

-- Note, we can use generalised congruence tag if we so desire.
-- I am not sure why you were going for congruence, but it is useful to tag for further use
-- with `grw`.
@[gcongr]
theorem add_congr (h₁ : e₁ ≈ e₂) (h₂ : e₃ ≈ e₄) : e₁ + e₃ ≈ e₂ + e₄ := by
  aesop (add simp [equiv_iff_eval_eq_eval])

/--
Note this proof is `aesop` but I wanted to have a proof with `grw` that works because of `gcongr`.
(The one from `add_congr`.)
-/
example (h₁ : e₁ ≈ e₂) (h₂ : e₃ ≈ e₄) : (Exp.add e₁ e₃ : Expₑ F) ≈ Exp.add e₂ e₄ := by
  change e₁ + e₃ ≈ e₂ + e₄
  grw [h₁, h₂]

@[gcongr]
theorem mul_congr (h₁ : e₁ ≈ e₂) (h₂ : e₃ ≈ e₄) : e₁ * e₃ ≈ e₂ * e₄ := by
  aesop (add simp [equiv_iff_eval_eq_eval])

@[gcongr]
theorem sub_congr (h₁ : e₁ ≈ e₂) (h₂ : e₃ ≈ e₄) : e₁ - e₃ ≈ e₂ - e₄ := by
  aesop (add simp [equiv_iff_eval_eq_eval])

end

end Exp

end

inductive Circuit (F var : Type) : Type where
  | nil : Circuit F var
  | eq0 : Exp F var → Circuit F var → Circuit F var
  | lam : (var → Circuit F var) → Circuit F var
  | share : Exp F var → (var → Circuit F var) → Circuit F var
  | is_zero : Exp F var → (var → Circuit F var) → Circuit F var

section

variable {F var : Type}

/-
Warning: var must be kept abstract, if var is fixed we can write bogus examples
-/

-- E.g. here v 0 is not bound by any lam
example : Circuit F Nat := Circuit.eq0 (.v 0) Circuit.nil

-- This is the right way, keeping var abstract, don't even need to name it
example : Π var, Circuit F var := fun _ ↦ .lam fun x ↦ .eq0 (.v x) .nil

-- Surely we can keep it abstract this way, right? Reduces some amount of lambda yoga.
example : Circuit F var := .lam fun x ↦ .eq0 (.v x) .nil

abbrev Circuitₑ (F : Type) := Circuit F F

/--
We need a family of types that map from ℕ.

One could argue that `OfNat` might do, but it's dependent on a value so there's more friction.
-/
class Index (var : outParam Type) where
  index : ℕ → var

instance [Index var] : Coe ℕ var := ⟨Index.index⟩

/--
This is 'the' `toString` from the old `Circuit.repr`.
-/
instance : Index String := ⟨ToString.toString⟩

instance : Index ℕ := ⟨id⟩

export Index (index)

def Circuit.repr [Repr F] [Repr var] [Ring F] [Index var]
  (l : ℕ) (c : Circuit F var) : Std.Format :=
  letI go (l : ℕ) (k : var → Circuit F var) := repr (l+1) (k (index l)) -- `k ∘ index : ℕ (→ var) → Circuit ..`
  match c with
  | .nil => "nil"
  | .lam k => s!"λ{l} {go l k}"
  | .eq0 e c => s!"eq0 {_root_.repr e} {repr l c}"
  | .share e k => s!"share {_root_.repr e} {go l k}"
  | .is_zero e k => s!"is_zero {_root_.repr e} {go l k}"

-- Had to define a separate function. The recursion was preventing the class inference?
-- Note: See `instReprExp`.
instance [Repr F] [Repr var] [Ring F] [Index var] : Repr (Circuit F var) where
  reprPrec c _ := c.repr 0

instance [Repr F] [Repr var] [Ring F] [Index var] : ToString (Circuit F var) :=
  ⟨Std.Format.pretty ∘ repr⟩

-- Can drop the leading lambda here.
def a (F var : Type) : Circuit F var := .lam fun x ↦ .lam fun y ↦ .eq0 (.v x + .v y) .nil

section

abbrev a' := a (ZMod 41) ℕ

#guard s!"{a'}" = "λ0 λ1 eq0 (v0 + v1) nil"

end

section

-- do we need to prove additional properties of this semantics?
-- I'll need to drop further down the rabbit hole to form any coherent thought on this :).
inductive denotation (var : Type) : Type where
  | n : denotation var
  | u : denotation var
  | l : (var → denotation var) → denotation var

section eval

/-
`DecidableEq F` for `e.eval = 0`.
-/

variable [DecidableEq F] [Ring F]

def Circuit.eval : Circuitₑ F → denotation F
  | .nil => .u
  | .lam k => .l fun x ↦ (k x).eval
  | .eq0 e c =>
    if e.eval = 0 then c.eval else .n
  | .share e k => (k e.eval).eval
  | .is_zero e k =>
    if e.eval = 0 then (k 1).eval else (k 0).eval

/-
Technically we want all of these dudes.
-/
@[simp]
lemma Circuit.eval_eq0 {e : Expₑ F} {c : Circuitₑ F} :
  (Circuit.eq0 e c).eval = if e.eval = 0 then c.eval else .n := by
  simp [Circuit.eval]

@[simp]
lemma Circuit.eval_lam {c : F → Circuitₑ F} :
  (Circuit.lam c).eval = .l fun x ↦ (c x).eval := by
  simp [Circuit.eval]

@[simp]
lemma Circuit.eval_share {e : Expₑ F} {k : F → Circuitₑ F} :
  (Circuit.share e k).eval = (k e.eval).eval := by
  simp [Circuit.eval]

@[simp]
lemma Circuit.eval_is_zero {e : Expₑ F} {k : F → Circuitₑ F} :
  (Circuit.is_zero e k).eval =  if e.eval = 0 then (k 1).eval else (k 0).eval := by
  simp [Circuit.eval]

def Circuit.equiv [DecidableEq F] [Ring F] (c₁ c₂ : Circuitₑ F) : Prop := c₁.eval = c₂.eval

instance [DecidableEq F] [Ring F] : Setoid (Circuitₑ F) where
  r := Circuit.equiv
  iseqv := Equivalence.comap eq_equivalence Circuit.eval -- Just pullback the proof.

private lemma Circuit.equiv_iff_eval_eq_eval {c₁ c₂ : Circuitₑ F} :
  c₁ ≈ c₂ ↔ c₁.eval = c₂.eval := by rfl

instance : IsRefl (Circuitₑ F) (· ≈ ·) := inferInstance -- This is by `inferInstance`, which means it need not exist altogether.
                                                        -- i.e. it is safe to delete this instance completely

section

variable {el er : Expₑ F} {cl cr : Circuitₑ F} {kl kr : F → Circuitₑ F}

@[gcongr]
theorem eq0_congr (h₁ : el ≈ er) (h₂ : cl ≈ cr) : Circuit.eq0 el cl ≈ .eq0 er cr := by
  aesop (add simp [Exp.equiv_iff_eval_eq_eval, Circuit.equiv_iff_eval_eq_eval])

@[gcongr]
theorem lam_congr (h : ∀ x, kl x ≈ kr x) : Circuit.lam kl ≈ Circuit.lam kr := by
  aesop (add simp [Exp.equiv_iff_eval_eq_eval, Circuit.equiv_iff_eval_eq_eval]) 

@[gcongr]
theorem share_congr (h₁ : el ≈ er) (h₂ : ∀ x, kl x ≈ kr x) :
  Circuit.share el kl ≈ Circuit.share er kr := by
  aesop (add simp [Exp.equiv_iff_eval_eq_eval, Circuit.equiv_iff_eval_eq_eval])

@[gcongr]
theorem is_zero_congr (h₁ : el ≈ er) (h₂ : ∀ x, kl x ≈ kr x) :
  Circuit.is_zero el kl ≈ Circuit.is_zero er kr := by
  aesop (add simp [Exp.equiv_iff_eval_eq_eval, Circuit.equiv_iff_eval_eq_eval])

end

def evalCps (c : Circuitₑ F) (k : denotation F → denotation F) : denotation F :=
  match c with
  | .nil => k .u
  | .eq0 e c => evalCps c fun c ↦ k (if e.eval = 0 then c else .n)
  | .lam k' => .l fun x ↦ evalCps (k' x) k
  | .share e k' => evalCps (k' e.eval) k
  | .is_zero e k' => if e.eval = 0 then evalCps (k' 1) k else evalCps (k' 0) k

instance : Setoid (Circuitₑ F) where
  r := Circuit.equiv
  iseqv := Equivalence.comap eq_equivalence Circuit.eval -- Just pullback the proof.

-- instance : IsRefl (Circuitₑ F) (· ≈ ·) := inferInstance -- Can be deleted no problem.

def Exp.decideEq (e₁ e₂ : Expₑ F) : Bool :=
  match e₁, e₂ with
  | .v n₁, v n₂ | .c n₁, .c n₂ => n₁ == n₂
  | .add ll lr, .add rl rr
  | .mul ll lr, .mul rl rr
  | .sub ll lr, .sub rl rr => ll.decideEq rl && lr.decideEq rr
  | _, _ => false

omit [Ring F] in
lemma Exp.decideEq_eq_true_iff_eq {e₁ e₂ : Expₑ F} :
  Exp.decideEq e₁ e₂ = true ↔ e₁ = e₂ := by
  induction' e₁ generalizing e₂ <;> cases e₂ <;> try aesop (add simp Exp.decideEq)

def Exp.decEq : DecidableEq (Expₑ F) := fun e₁ e₂ ↦
  if h : e₁.decideEq e₂
  then isTrue (Exp.decideEq_eq_true_iff_eq.1 h)
  else isFalse (by aesop (add simp decideEq_eq_true_iff_eq))

instance [DecidableEq F] : DecidableEq (Expₑ F) := Exp.decEq

end eval

end

end

end

end Clap
