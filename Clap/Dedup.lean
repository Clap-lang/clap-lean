import Clap.Circuit
import Clap.Simulation
import Clap.Id

namespace Clap

/-
  This file introduces an optimization to remove duplicate checks.
  The current version eliminates any `eq0` with an expression that has
  already been met before. The same optimization should be applicable
  to boolean checks, limb checks and other lookup arguments with minor
  modifications.

  Dedup is extremely valuable as it allows to write composable
  circuits with many redundant checks without having to pay the price
  in term of constraints.
-/

variable {p : ℕ} {var : Type} [Fact (Nat.Prime p)]

def Exp.toNat : Exp p (ℕ × var) → Exp p ℕ
  | .v (var, _) => .v var
  | .c f => .c f
  | .add l r => l.toNat + r.toNat
  | .mul l r => l.toNat * r.toNat
  | .sub l r => l.toNat - r.toNat

def Exp.toVar : Exp p (ℕ × var) → Exp p var
  | .v (_, var) => .v var
  | .c f => .c f
  | .add l r => l.toVar + r.toVar
  | .mul l r => l.toVar * r.toVar
  | .sub l r => l.toVar - r.toVar

def Exp.beq : Exp p Nat → Exp p Nat → Bool
  | .v n1, .v n2
  | .c n1, .c n2 => n1 = n2
  | .add ll lr, .add rl rr => beq ll rl && beq lr rr
  | .mul ll lr, .mul rl rr => beq ll rl && beq lr rr
  | .sub ll lr, .sub rl rr => beq ll rl && beq lr rr
  | _, _ => false

-- TODO we are mixing expressions from eq0 and assert_range, they should be in different sets
def dedupAux (c : Circuit (ℕ × var)) (n : ℕ) (set : Finset (Exp p ℕ)) : Circuit var :=
  match c with
  | .nil => .nil
  | .eq0 e c =>
    if e.toNat ∈ set
    then dedupAux c n set
    else .eq0 e.toVar (dedupAux c n ({e.toNat} ∪ set))
  | .lam k => .lam fun x => dedupAux (k (n, x)) (n + 1) set
  | .share e k => .share e.toVar fun x => dedupAux (k (n, x)) (n + 1) set
  | .isZero e k => .isZero e.toVar fun x => dedupAux (k (n, x)) (n + 1) set
  | .num2bits w e k => .num2bits w e.toVar fun xs => (dedupAux (k ((List.range' n w 1).zip xs)) n ({e.toNat} ∪ set))

def dedup (c : Circuit (Nat × var)) : Circuit var := dedupAux c 0 ∅

def dedup' (c : Circuit' p) : Circuit' p := fun var => dedup (c (Nat × var))

namespace Test

def a        : Circuit' 7 := fun _ => .lam (fun x => .eq0 (.v x + .c 1) (.eq0 (.v x + .c 2) (.eq0 (.v x + .c 1) .nil )))
def expected : Circuit' 7 := fun _ => .lam (fun x => .eq0 (.v x + .c 1) (.eq0 (.v x + .c 2) .nil ))

#guard s!"{dedup' a Nat}" = s!"{expected Nat}"

end Test

open Id

theorem dedup_sem_pre {cl : Circuitₑ p} {cr : Circuit (ℕ × ZMod p)} {G}
  (h₁ : Circuit.wf G cl cr)
  (h₂ : ∀ entry ∈ G, entry.1 = Exp.eval entry.2.2) : -- TODO(Marco): Do we really want eval here on the const?
  cl ≈ (dedup cr) := sorry

-- theorem dedup_sem_pre' : ∀ (cl: Circuit' F),
--   wf' cl ->
--    cl ≈ (dedup' cl) := by
--   intro cl wf
--   apply dedup_sem_pre
--   apply wf
--   simp

end Clap
