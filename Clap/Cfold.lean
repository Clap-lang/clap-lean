import Clap.Circuit

namespace Clap

/-
  Constant folding.

  This optimization does not depend on any choice of var.
-/

variable {var : Type} {p : ℕ} [Fact (Nat.Prime p)]

/-
  Note: this function contains some pattern matchings that don't look ideal
  because of https://github.com/leanprover/lean4/issues/9803
  Typically "| l,.c 0 => " is replaced by "| l,r => if r=0 then"
-/
def Exp.cfold (e : Exp p var) : Exp p var :=
  match e with
  | .v var => .v var
  | .c i => .c i
  | .add l r =>
    match l.cfold, r.cfold with
    | .c l , .c r => .c (l+r)
    |    l , .c r => if r = 0 then l else .add l r
    | .c l , r    => if l = 0 then r else .add l r
    |    _ , _    => .add l r
  | .mul l r =>
    match l.cfold, r.cfold with
    | .c l , .c r => .c (l * r)
    | .c l , r    =>
      if l = 0 then .c 0 else
      if l = 1 then r
      else .mul l r
    |    l , .c r =>
      if r = 0 then .c 0 else
      if r = 1 then l
      else .mul l r
    |    _ , _    => .mul l r
  | .sub l r =>
    match l.cfold, r.cfold with
    | .c l , .c r => .c (l-r)
    |    l , .c r => if r = 0 then l else .sub l r
    |    _ , _    => .sub l r

def Circuit.cfold {var : Type} (c : Circuit p var) : Circuit p var :=
  match c with
  | .nil => .nil
  | .eq0 e c => .eq0 e.cfold fun _ ↦ cfold (c ())
  | .lam k => .lam fun x => (k x).cfold
  | .share e k => .share e.cfold fun x => (k x).cfold
  | .isZero e k => .isZero e.cfold fun x => (k x).cfold
  | num2bits w e c => num2bits w e.cfold fun bits => (c bits).cfold

def cfold' (c : Circuit' p) : Circuit' p := fun var => Circuit.cfold (c var)

@[simp]
theorem Exp.cfold_sem_pre {e : Expₑ p} : e.cfold ≈ e := by
  induction e <;> aesop (add simp [Exp.equiv_iff_eval_eq_eval, Exp.eval, Exp.cfold])

theorem cfold_sem_pre {c : Circuitₑ p} : c ≈ c.cfold := by
  induction c <;> unfold Circuit.cfold
  all_goals gcongr; try grw [Exp.cfold_sem_pre]
  all_goals sorry

theorem cfold'_sem_pre : ∀ (c : Circuit' p),
  Circuit.eval' c = Circuit.eval' (cfold' c) := by
  intros
  apply cfold_sem_pre

end Clap
