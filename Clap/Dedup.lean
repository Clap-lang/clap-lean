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

namespace Dedup

def to_nat {var} (e:Exp (Nat × var)) : Exp Nat :=
  match e with
  | .v (v,_) => .v v
  | .c f => .c f
  | .add l r => to_nat l + to_nat r
  | .mul l r => to_nat l * to_nat r
  | .sub l r => to_nat l - to_nat r

def to_var {var} (e:Exp (Nat × var)) : Exp var :=
  match e with
  | .v (_,v) => .v v
  | .c f => .c f
  | .add l r => to_var l + to_var r
  | .mul l r => to_var l * to_var r
  | .sub l r => to_var l - to_var r

def beq : (e1 e2 : Exp Nat) -> Bool
  | .v n1, .v n2
  | .c n1, .c n2 => n1 = n2
  | .add ll lr, .add rl rr => beq ll rl && beq lr rr
  | .mul ll lr, .mul rl rr => beq ll rl && beq lr rr
  | .sub ll lr, .sub rl rr => beq ll rl && beq lr rr
  | _,_ => false

-- #check (inferInstance : DecidableEq (Exp Nat))

def dedup_ {var} (c:Circuit (Nat × var)) (n:Nat) (set: List (Exp Nat)) : Circuit var :=
  match c with
  | .nil => .nil
  | .eq0 e c =>
    if (to_nat e) ∈ set
    then dedup_ c n set
    else .eq0 (to_var e) (dedup_ c n ((to_nat e)::set))
  | .lam k => .lam (fun x => dedup_ (k (n,x)) (n+1) set)
  | .share e k => .share (to_var e) (fun x => dedup_ (k (n,x)) (n+1) set)
  | .is_zero e k => .is_zero (to_var e) (fun x => dedup_ (k (n,x)) (n+1) set)

def dedup {var} (c:Circuit (Nat × var)) : Circuit var := dedup_ c 0 []

def dedup' (c:Circuit') : Circuit' := fun var => dedup (c (Nat × var))

def a        : Circuit' := fun _ => .lam (fun x => .eq0 (.v x + .c 1) (.eq0 (.v x + .c 2) (.eq0 (.v x + .c 1) .nil )))
def expected : Circuit' := fun _ => .lam (fun x => .eq0 (.v x + .c 1) (.eq0 (.v x + .c 2) .nil ))

#guard s!"{dedup' a}" = s!"{expected}"

open Id

theorem dedup_sem_pre : ∀ (cl: Circuit F) (cr:Circuit (Nat × F)) G,
  wf G cl cr ->
    List.Forall (fun entry => entry.l = (Exp.eval entry.r.2)) G ->
      cl ≈ (dedup cr) := sorry

theorem dedup_sem_pre' : ∀ (cl: Circuit'),
  wf' cl ->
   cl ≈ (dedup' cl) := by
  intro cl wf
  apply dedup_sem_pre
  apply wf
  simp

end Dedup
