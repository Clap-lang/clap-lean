import Clap.Circuit

namespace Clap

/-
  Constant folding.

  This optimization does not depend on any choice of var.
-/

namespace Cfold

variable {F : Type}
variable [Field F]

def cfold_e {var} (e: Exp F var) : Exp F var :=
  match e with
  | .v v => .v v
  | .c i => .c i
  | .add l r =>
    match cfold_e l, cfold_e r with
    | .c l , .c r => .c (l+r)
-- TODO
--    |    l , .c 0 => l
--    | .c 0 , r    => r
    |    _ , _    => .add l r
  | .mul l r =>
    match cfold_e l, cfold_e r with
    | .c l , .c r => .c (l * r)
--    |    _ , .c 0
--    | .c 0 , _    => .c 0
--    |    l , .c 1 => l
--    | .c 1 , r    => r
    |    _ , _    => .mul l r
  | .sub l r =>
    match cfold_e l, cfold_e r with
    | .c l , .c r => .c (l-r)
--    |    l , .c 0 => l
    |    _ , _    => .sub l r

def cfold {var} (c:Circuit F var) : Circuit F var :=
  match c with
  | .nil => .nil
  | .eq0 e c => .eq0 (cfold_e e) (cfold c)
  | .lam k => .lam (fun x => cfold (k x))
  | .share e k => .share (cfold_e e) (fun x => cfold (k x))
  | .is_zero e k => .is_zero (cfold_e e) (fun x => cfold (k x))

def cfold' (c:Circuit' F) : Circuit' F := fun var => cfold (c var)

-- TODO change to ≈
theorem cfold_e_sem_pre : ∀ (e:Exp F F), Exp.eval e = Exp.eval (cfold_e e) := by
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

theorem cfold_sem_pre [DecidableEq F] : ∀ (c:Circuit F F), c ≈ (cfold c) := by
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

variable [DecidableEq F]

theorem cfold'_sem_pre : ∀ (c:Circuit' F),
  Circuit.eval' c = Circuit.eval' (cfold' c) := by
  intros
  apply cfold_sem_pre

end Cfold
