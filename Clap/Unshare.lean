import Clap.Circuit
import Clap.Simulation
import Clap.Id

set_option autoImplicit false
set_option linter.unusedVariables true

namespace Unshare

/-
  Unshare optimization - inlines an expression previously shared.

  While Cfold did not depend on any choice of var, unshare needs to
  pass an argument to a continuation, which expects a var.
-/

/-
  As a first attempt, it is easy to write (and prove correct!) a
  version where var is already fixed to F.
  However the var cannot be generalized again, so for example the
  resulting circuit cannot be printed or passed to another
  optimization that requires a different type.
  I's basically like in the Hoas case.
-/

def unshare_all_F (c:Circuit F) : Circuit F :=
  match c with
  | .nil => .nil
  | .eq0 e c => .eq0 e (unshare_all_F c)
  | .lam k => .lam (fun x => unshare_all_F (k x))
  | .is_zero e k => .is_zero e (fun x => unshare_all_F (k x))
  --
  | .share e k => k (eval_e e)

theorem unshare_all_sem_pre : ∀ (c:Circuit F),
  c ≈ unshare_all_F c := by
  intros c
  induction c with
  | lam k h =>
    apply lam_congr
    exact h
  | nil =>
    simp [unshare_all_F]
  | eq0 e c h =>
    apply eq0_congr
    simp
    assumption
  | share e c h =>
    apply share_congr
    simp
    simp
  | is_zero e c h =>
    apply is_zero_congr
    simp
    assumption

/-
  Id presents a simple example of optimization pass that does not use
  the function argument `var` in any interesting way, like Cfold, but
  that takes circuits with different `var` instantiations.
  In particular Circuit (Exp var) is the right type for passing around
  expressions, which is what `unshare` needs.
  `unshare_all` is identical to Id except in the share case, where
  instead of replicating the structure, it passes the expression to
  the continuation, effectively executing a step of `eval`.
-/
open Id

def unshare_all {var} (c:Circuit (Exp var)) : Circuit var :=
  match c with
  | .nil => .nil
  | .eq0 e c => .eq0 (unwrap_e e) (unshare_all c)
  | .lam k => .lam (fun x => unshare_all (k (.v x)))
  | .is_zero e k => .is_zero (unwrap_e e) (fun x => unshare_all (k (.v x)))
  --
  | .share e k => unshare_all (k (unwrap_e e))

def unshare_all' (c:Circuit') : Circuit' := fun var => unshare_all (c (Exp var))

def a : Circuit' := fun _ => Circuit.lam (fun x => Circuit.share (.c 1 + .v x) (fun x => Circuit.eq0 (.v x) Circuit.nil))
def expected_a : Circuit' := fun _ => Circuit.lam (fun x => Circuit.eq0 (.c 1 + .v x) Circuit.nil)

#guard s!"{unshare_all' a}" = s!"{expected_a}"

theorem unshare_sem_pre : ∀ (cl: Circuit F) (cr:Circuit (Exp F)) G,
  wf G cl cr ->
   List.Forall (fun entry => entry.l = (eval_e entry.r)) G ->
   cl ≈ (unshare_all cr)
:= by
  intros cl
  induction cl with
  -- only interesting case
  | share el kl h =>
    intros cr G wf FA
    cases wf
    case _ kr wf_e wf =>
    simp [unshare_all]
    apply h
    . apply wf
    . rw [List.forall_cons]
      constructor
      simp
      apply unwrap_e_sem_pre
      repeat assumption
  -- all other cases are like Id
  | nil =>
    intros cr G wf FA
    cases wf
    simp [unshare_all]
  | lam kl h =>
    intros cr G wf FA
    cases wf
    case _ kr wf =>
    apply lam_congr
    intro x
    apply h
    apply wf
    rw [List.forall_cons]
    simp [eval_e]
    assumption
  | eq0 el cl h =>
    intros cr G wf FA
    cases wf
    case _ er cr wf_e wf =>
    apply eq0_congr
    . apply unwrap_e_sem_pre
      repeat assumption
    . apply h
      repeat assumption
  | is_zero el kl h =>
    intro cr G wf FA
    cases wf
    case _ er kr' wf_e wf =>
    apply is_zero_congr
    . apply unwrap_e_sem_pre
      repeat assumption
    . intro x
      apply h
      apply wf
      rw [List.forall_cons]
      simp [eval_e]
      assumption

/-
  Unsharing/Inlining all expressions leads to constraints of arbitrary
  degree. In order to only inline if the resulting expression is below
  a certain degree threshold, the `unshare_deg` has two main changes
  wrt `unshare_all`.
  1. the share case cannot compute in advance the degree of all the
     possible places where the expression is going to be inlined, so all
     inlinings are performed and if later an expression has too high
     degree, the function aborts and backtracks.
  2. TODO CPS

  Shares are inlined following the order in which they appear, a
  different order might lead to more inlining.
  Possible heuristic: inline first expressions that participate in less
  constraints. For that we could rearrange the rows.
  This is exactly the opposite of how to determine which expressions
  should be inlined: those that are shared by many constraints.

  Worst-case complexity is quadratic in the number of shares.

  Example: `a` takes part in two constraints, so it's a good candidate
  for sharing, while `b` and `c` appear in only one constraint each,
  so they should definitely by inlined.
  In a bad ordering `a` could appear first and get inlined, while `b`
  and `c` won't be inlined if the degree limit is 2. Saving only 1
  constraint.
  In a good ordering `a` would appear last and remain shared after `b`
  and `c` are inlined. Saving 2 constraints.

  TODO does the degree of the expression to be inlined affect the heuristic? is it better to inline smaller degrees first?

bad order
```
a = x
b = x
c = x
d = x * a * b
e = x * a * c
```
```
b = x
c = x
d = x^2 * b
e = x^2 * c
```

good order
```
b = x
c = x
a = x
d = x * a * b
e = x * a * c
```
```
a = x
d = x^2 * a
e = x^2 * a
```
-/

def degree {var} (e:Exp var) : Nat :=
  match e with
  | .v _ => 1
  | .c _ => 0
  | .add l r
  | .sub l r => max (degree l) (degree r)
  | .mul l r => (degree l) + (degree r)

def unshare_deg_cps {var} (c:Circuit (Exp var)) (k : Bool × Circuit var -> Circuit var) : Circuit var :=
  match c with
  | .nil => k (true,.nil)
  | .eq0 e c =>
     let be := degree e <= 2
     unshare_deg_cps c (fun (b,c) => k (b && be, .eq0 (unwrap_e e) c))
  | .lam k' => .lam (fun x => unshare_deg_cps (k' (.v x)) k)
  | .is_zero e k' =>
     let be := degree e <= 2
    .is_zero (unwrap_e e) (fun x => unshare_deg_cps (k' (.v x)) (fun (b,c) => k (b && be, c)))
  --
  | .share e k' =>
    let be := degree e <= 2
    unshare_deg_cps (k' (unwrap_e e)) (fun (b,c) =>
      if b && be
      then k (true, c)
      else .share (unwrap_e e) (fun x => unshare_deg_cps (k' (.v x)) k))

def unshare_deg {var} (c:Circuit (Exp var)) : Circuit var := unshare_deg_cps c (fun (b,x) => if b then x else id c)

def unshare_deg' (c:Circuit') : Circuit' := fun var => unshare_deg (c (Exp var))

-- tests

def do_optimize : Circuit' := fun _ => Circuit.lam (fun x => Circuit.share (.v x * .v x) (fun x => Circuit.eq0 (.v x) Circuit.nil))

def expected_optimized : Circuit' := fun _ => Circuit.lam (fun x => Circuit.eq0 (.v x * .v x) Circuit.nil)

def do_not_optimize : Circuit' := fun _ => Circuit.lam (fun x => Circuit.share (.v x * .v x * .v x) (fun x => Circuit.eq0 (.v x) Circuit.nil))

#guard s!"{unshare_deg' do_optimize}" = s!"{expected_optimized}"
#guard s!"{unshare_deg' do_not_optimize}" = s!"{do_not_optimize}"

--

end Unshare
