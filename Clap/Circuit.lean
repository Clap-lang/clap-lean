import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum -- norm_num

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

def p : Nat := 7
abbrev F := ZMod p
instance : Fact (Nat.Prime p) := ⟨by decide⟩

inductive Exp (var:Type) where
  | v : var -> Exp var
  | c : F -> Exp var
  | add : Exp var -> Exp var -> Exp var
  | mul : Exp var -> Exp var -> Exp var
  | sub : Exp var -> Exp var -> Exp var
  deriving DecidableEq

def Exp' : Type _ := (var:Type) -> Exp var

namespace Exp

def reprString (e:Exp String) : Std.Format :=
  match e with
  | .v s => s!"v{s}"
  | .c n => repr n
  | .add e1 e2 => s!"({reprString e1} + {reprString e2})"
  | .mul e1 e2 => s!"({reprString e1} * {reprString e2})"
  | .sub e1 e2 => s!"({reprString e1} - {reprString e2})"

instance : Repr (Exp String) where
  reprPrec e _ := reprString e

instance : Repr (Exp') where
  reprPrec e _ := reprString (e String)

instance (var:Type) : Add (Exp var) where
  add a b := .add a b

instance (var:Type) : Mul (Exp var) where
  mul a b := .mul a b

instance (var:Type) : Sub (Exp var) where
  sub a b := .sub a b

-- we can only substitute F for variables so .v and .c are equivalent, which is ok for evaluation
example : Exp F := (.c 1) + (.v 2)
-- we can substitute expressions for variables, which is what we need for optimizations
example : Exp (Exp F) := (.c 1) + (.v ((.c 2) + (.c 2)))

def eval (e: Exp F) : F :=
  match e with
  | .v f => f
  | .c i => i
  | .add l r => eval l + eval r
  | .mul l r => eval l * eval r
  | .sub l r => eval l - eval r

def eval' (e:Exp') : F := Exp.eval (e F)

instance : Coe (Exp F) F where
  coe := eval

instance : Coe F (Exp F) where
  coe := .c

instance (n:Nat) : OfNat (Exp F) n where
  ofNat := (↑n:F)

def equiv (e1 e2 : Exp F) : Prop := Exp.eval e1 = Exp.eval e2

instance : Setoid (Exp F) where
  r := Exp.equiv
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

example : 3 + 4 ≈ (7 : Exp F) := by
  show eval _ = eval _
  simp [eval]
  norm_num

@[gcongr]
theorem add_congr (e1 e2 e3 e4 : Exp F) (h1 : e1 ≈ e2) (h2 : e3 ≈ e4) :
  e1 + e3 ≈ e2 + e4 := by
  show eval _ = eval _
  simp [eval]
  rw [h1, h2]

example e1 e2 e3 e4 (h1 : e1 ≈ e2) (h2 : e3 ≈ e4) : (add e1 e3 : Exp F) ≈ add e2 e4 := by
  apply add_congr
  repeat assumption

@[gcongr]
theorem mul_congr (e1 e2 e3 e4 : Exp F) (h1 : e1 ≈ e2) (h2 : e3 ≈ e4) :
    e1 * e3 ≈ e2 * e4 := by
  show eval _ = eval _
  simp [eval]
  rw [h1, h2]

@[gcongr]
theorem sub_congr (e1 e2 e3 e4 : Exp F) (h1 : e1 ≈ e2) (h2 : e3 ≈ e4) :
    e1 - e3 ≈ e2 - e4 := by
  show eval _ = eval _
  simp [eval]
  rw [h1, h2]

end Exp

inductive denotation : Type where
  | n : denotation
  | u : denotation
  | l : (F -> denotation) -> denotation

inductive Circuit (var:Type) : Type where
  | nil : Circuit var
  | eq0 : Exp var -> Circuit var -> Circuit var
  | lam : (var -> Circuit var) -> Circuit var
  | share : Exp var -> (var -> Circuit var) -> Circuit var
  | is_zero : Exp var -> (var -> Circuit var) -> Circuit var

def Circuit' : Type _ := (var:Type) -> Circuit var

/-
Warning: var must be kept abstract, if var is fixed we can write bogus examples
-/

-- E.g. here v 0 is not bound by any lam
example : Circuit Nat := Circuit.eq0 (.v 0) Circuit.nil

-- This is the right way, keeping var abstract, don't even need to name it
example : Circuit' := fun _ => (.lam (fun x => .eq0 (.v x) .nil))
-- TODO
-- example : Circuit' := fun _ => Circuit.lam (fun x => Circuit.eq0 (Exp.v x) Circuit.nil)

namespace Circuit

def reprString (l:Nat) : Circuit String → Std.Format
  | .nil => "nil"
  | .lam k => s!"λ{(toString l)} {reprString (l+1) (k (toString l))}"
  | .eq0 e c => s!"eq0 {repr e} {reprString l c}"
  | .share e k => s!"share {repr e} {reprString (l+1) (k (toString l))}"
  | .is_zero e k => s!"is_zero {repr e} {reprString (l+1) (k (toString l))}"

-- Had to define a separate function. The recursion was preventing the class inference?
instance : Repr (Circuit') where
  reprPrec c _ := reprString 0 (c String)

instance : ToString (Circuit') where
  toString c := toString (reprString 0 (c String))

def a : Circuit' := fun _ => .lam (fun x => .lam (fun y => .eq0 (.v x + .v y) .nil))

#guard s!"{a}" = "λ0 λ1 eq0 (v0 + v1) nil"

-- do we need to prove additional properties of this semantics?

def eval (c:Circuit F) : denotation :=
  match c with
  | .nil => .u
  | .lam k => .l (fun x => eval (k x))
  | .eq0 e c =>
    if Exp.eval e = 0 then eval c else .n
  | .share e k => eval (k (Exp.eval e))
  | .is_zero e k =>
    if Exp.eval e = 0 then eval (k 1) else eval (k 0)

def eval' (c:Circuit') : denotation := eval (c F)

def equiv (c1 c2 : Circuit F) : Prop := eval c1 = eval c2

instance : Setoid (Circuit F) where
  r := equiv
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

instance : IsRefl (Circuit F) (· ≈ ·) where
  refl := Setoid.refl

theorem nil_congr :
  nil ≈ (nil : Circuit F) := by
  show eval _ = eval _
  simp [eval]

@[gcongr]
theorem eq0_congr : ∀ (el er:Exp F) (cl cr:Circuit F),
  el ≈ er -> cl ≈ cr ->
  eq0 el cl ≈ eq0 er cr := by
  intro el er kl kr he hk
  show eval _ = eval _
  simp [eval]
  rw [he,hk]

@[gcongr]
theorem lam_congr : ∀ (kl kr:F -> Circuit F),
  (∀ x, kl x ≈ kr x) ->
  lam kl ≈ lam kr := by
  intro kl kr hk
  show eval _ = eval _
  simp [eval]
  funext
  apply hk

@[gcongr]
theorem share_congr : ∀ (el er:Exp F) (kl kr:F -> Circuit F),
  el ≈ er -> (∀ x, kl x ≈ kr x) ->
  share el kl ≈ share er kr := by
  intro el er kl kr he hk
  show eval _ = eval _
  simp [eval]
  rw [he]
  apply hk

@[gcongr]
theorem is_zero_congr : ∀ (el er:Exp F) (kl kr:F -> Circuit F),
  el ≈ er -> (∀ x, kl x ≈ kr x) ->
  is_zero el kl ≈ is_zero er kr := by
  intro el er kl kr he hk
  show eval _ = eval _
  simp [eval]
  rw [he,hk 0,hk 1]

def equiv' (c1 c2 : Circuit') : Prop := eval' c1 = eval' c2

instance : Setoid (Circuit') where
  r := equiv'
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

instance : IsRefl (Circuit') (· ≈ ·) where
  refl := Setoid.refl

end Circuit
