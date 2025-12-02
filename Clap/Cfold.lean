import Clap.Circuit

namespace Clap

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

theorem cfold_e_sem_pre : ∀ (e:Exp F), (Exp.eval e) = (Exp.eval (cfold_e e)) := by
  intros e
  induction e with
  | v f
  | c f =>
    simp [cfold_e,Exp.eval]
  | add l r hl hr =>
    simp [cfold_e,Exp.eval]
    split
    repeat simp [*,Exp.eval]
  | mul l r hl hr =>
    simp [cfold_e,Exp.eval]
    split
    repeat simp [*,Exp.eval]
  | sub l r hl hr =>
    simp [cfold_e,Exp.eval]
    split
    repeat simp [*,Exp.eval]

theorem cfold_sem_pre : ∀ (c:Circuit F), c ≈ (cfold c) := by
  intros c
  induction c with
  | nil =>
    constructor
  | lam k h
  | eq0 e c h
  | share e c h
  | is_zero e c h =>
    simp [cfold]
    gcongr
    repeat (first | apply cfold_e_sem_pre | apply h)

theorem cfold'_sem_pre : ∀ (c:Circuit'), Circuit.eval' c = Circuit.eval' (cfold' c) := by
  intros
  apply cfold_sem_pre

end Cfold
