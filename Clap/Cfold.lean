import Clap.Circuit

/-
  Constant folding.

  This optimization does not depend on any choice of var.
-/

namespace Cfold

def cfold_e {var} (e: Exp var) : Exp var :=
  match e with
  | .v v => .v v
  | .c i => .c i
  | .add l r =>
    match cfold_e l, cfold_e r with
    | .c l , .c r => .c (l+r)
    |    l , .c 0 => l
    | .c 0 , r    => r
    |    _ , _    => .add l r
  | .mul l r =>
    match cfold_e l, cfold_e r with
    | .c l , .c r => .c (l * r)
    |    _ , .c 0
    | .c 0 , _    => .c 0
    |    l , .c 1 => l
    | .c 1 , r    => r
    |    _ , _    => .mul l r
  | .sub l r =>
    match cfold_e l, cfold_e r with
    | .c l , .c r => .c (l-r)
    |    l , .c 0 => l
    |    _ , _    => .sub l r

def cfold {var} (c:Circuit var) : Circuit var :=
  match c with
  | .nil => .nil
  | .eq0 e c => .eq0 (cfold_e e) (cfold c)
  | .lam k => .lam (fun x => cfold (k x))
  | .share e k => .share (cfold_e e) (fun x => cfold (k x))
  | .is_zero e k => .is_zero (cfold_e e) (fun x => cfold (k x))

def cfold' (c:Circuit') : Circuit' := fun var => cfold (c var)

theorem cfold_e_sem_pre : ∀ (e:Exp F), (eval_e e) = (eval_e (cfold_e e)) := by
  intros e
  induction e with
  | v f
  | c f =>
    simp [cfold_e,eval_e]
  | add l r hl hr =>
    simp [cfold_e,eval_e]
    split
    repeat simp [*,eval_e]
  | mul l r hl hr =>
    simp [cfold_e,eval_e]
    split
    repeat simp [*,eval_e]
  | sub l r hl hr =>
    simp [cfold_e,eval_e]
    split
    repeat simp [*,eval_e]

theorem cfold_sem_pre : ∀ (c:Circuit F), c ≈ (cfold c) := by
  intros c
  induction c with
  | nil =>
    constructor
  | lam k h =>
    simp [cfold]
    apply lam_congr
    exact h
  | eq0 e c h
  | share e c h
  | is_zero e c h =>
    simp [cfold]
    first | apply eq0_congr | apply share_congr | apply is_zero_congr
    apply cfold_e_sem_pre
    exact h

theorem cfold'_sem_pre : ∀ (c:Circuit'), eval' c = eval' (cfold' c) := by
  intros
  apply cfold_sem_pre

end Cfold
