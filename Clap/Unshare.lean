import Clap.Circuit
import Clap.Simulation
import Clap.Id

namespace Clap

variable {p : ℕ} [Fact (Nat.Prime p)]

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

def Circuit.unshareAllF (c : Circuitₑ p) : Circuitₑ p :=
  match c with
  | .nil => .nil
  | .eq0 e c => .eq0 e c.unshareAllF
  | .lam k => .lam fun x => (k x).unshareAllF
  | .is_zero e k => .is_zero e fun x => (k x).unshareAllF
  | .num2bits w e k => .num2bits w e fun x => (k x).unshareAllF
  | .swap c a b k => .swap c a b fun ab => (k ab).unshareAllF
  | .share e k => k e.eval

theorem unshare_all_sem_pre_F {c : Circuitₑ p} : c ≈ c.unshareAllF := by
  induction c <;> unfold Circuit.unshareAllF
  any_goals gcongr
  grind
  constructor
  grind
  grind
  grind

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

def Circuit.unshareAll {var} (c : Circuit p (Exp p var)) : Circuit p var :=
  match c with
  | .nil => .nil
  | .eq0 e c => .eq0 e.unwrap c.unshareAll
  | .lam k => .lam fun x ↦ (k (.v x)).unshareAll
  | .is_zero e k => .is_zero e.unwrap fun x ↦ unshareAll (k (.v x))
  | .num2bits w e k => .num2bits w e.unwrap fun x ↦ (k (x.map .v)).unshareAll
  | .swap c a b k => .swap c.unwrap a.unwrap b.unwrap fun ab ↦ (k (.v ab.1, .v ab.2)).unshareAll
  | .share e k => (k e.unwrap).unshareAll

def unshareAll' (c:Circuit' p) : Circuit' p := fun var => Circuit.unshareAll (c (Exp p var))

namespace TestUnshare

def a : Circuit' 7 := fun _ => Circuit.lam (fun x => Circuit.share (.c 1 + .v x) (fun x => Circuit.eq0 (.v x) Circuit.nil))
def expected_a : Circuit' 7 := fun _ => Circuit.lam (fun x => Circuit.eq0 (.c 1 + .v x) Circuit.nil)

#guard s!"{unshareAll' a Nat}" = s!"{expected_a Nat}"

end TestUnshare

theorem unshareAll_sem_pre {cl : Circuitₑ p} {cr : Circuit p (Expₑ p)} {G}
  (h₁ : Circuit.wf G cl cr)
  (h₂ : ∀ entry ∈ G, entry.1 = entry.2.eval) : cl ≈ cr.unshareAll := by
  induction cl generalizing cr G <;> cases h₁ <;> unfold Circuit.unshareAll
  · rfl
  · gcongr <;> grind [<= Exp.unwrap_sem_pre]
  next ih _ h => gcongr; apply ih; apply h; grind [= Exp.eval]
  next ih _ _ wf h =>
    simp [Circuit.equiv_iff_eval_eq_eval]
    apply ih _ (h _ _) _; simp
    exact ⟨Exp.unwrap_sem_pre wf h₂, by grind⟩
  next ih _ _ wf h =>
    gcongr <;> [grind [<= Exp.unwrap_sem_pre]; skip]
    apply ih _ (h _ _) _; simp
    exact ⟨by simp [Exp.eval], by grind⟩

theorem unshare_sem_pre' : ∀ (cl: Circuit' p),
  wf' cl ->
   cl ≈ (unshareAll' cl) := by
  intro cl wf
  apply unshareAll_sem_pre
  apply wf
  simp

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

def Exp.degree {var} : Exp p var → Nat
  | .v _ => 1
  | .c _ => 0
  | .add l r | .sub l r => max l.degree r.degree
  | .mul l r => l.degree + r.degree

def Circuit.unshareDegCps {var} (c : Circuit p (Exp p var))
                                (k : Bool × Circuit p var → Circuit p var) : Circuit p var :=
  match c with
  | .nil => k (true, .nil)
  | .eq0 e c =>
     c.unshareDegCps fun (b, c) => k (b && e.degree <= 2, .eq0 e.unwrap c)
  | .lam k' => .lam fun x => (k' (.v x)).unshareDegCps k
  | .is_zero e k' =>
    .is_zero e.unwrap fun x => unshareDegCps (k' (.v x)) (fun (b, c) => k (b && e.degree <= 2, c))
  | .num2bits w e k' =>
    .num2bits w e.unwrap fun x => (k' (x.map .v)).unshareDegCps (fun (b,c) => k (b && e.degree <= 2, c))
  | .swap c a b k' =>
    letI d := c.degree <=2 && a.degree <=2 && b.degree <=2
    .swap c.unwrap a.unwrap b.unwrap fun ab => (k' (.v ab.1, .v ab.2)).unshareDegCps (fun (b,c) => k (b && d, c))
  | .share e k' =>
    unshareDegCps (k' e.unwrap) fun (b,c) =>
      if b && e.degree <= 2
      then k (true, c)
      else .share e.unwrap fun x => unshareDegCps (k' (.v x)) k

def Circuit.unshareDeg {var} (c : Circuit p (Exp p var)) : Circuit p var :=
  unshareDegCps c fun (b, x) ↦ if b then x else id c

def unshareDeg' (c : Circuit' p) : Circuit' p := fun var => Circuit.unshareDeg (c (Exp p var))

namespace TestUnshare

def do_optimize : Circuit' 7 := fun _ => .lam (fun x => .share (.v x * .v x) (fun x => .eq0 (.v x) .nil))

def expected_optimized : Circuit' 7 := fun _ => .lam (fun x => .eq0 (.v x * .v x) .nil)

def do_not_optimize : Circuit' 7 := fun _ => .lam (fun x => .share (.v x * .v x * .v x) (fun x => .eq0 (.v x) .nil))

#guard s!"{unshareDeg' do_optimize Nat}" = s!"{expected_optimized Nat}"
#guard s!"{unshareDeg' do_not_optimize Nat}" = s!"{do_not_optimize Nat}"

end TestUnshare

-- namespace TestUnshare2

-- def do_optimize : Circuit' 7 := fun _ => .lam (fun x => .share (.v x * .v x) (fun x => .assert_range 2 (.v x) (fun xs => .eq0 (.v xs[0]) .nil)))

-- def expected_optimized : Circuit' 7 := fun _ => .lam (fun x => .eq0 (.v x * .v x) .nil)

-- def do_not_optimize : Circuit' 7 := fun _ => .lam (fun x => .share (.v x * .v x * .v x) (fun x => .eq0 (.v x) .nil))

-- #guard s!"{unshareDeg' do_optimize Nat}" = s!"{expected_optimized Nat}"
-- #guard s!"{unshareDeg' do_not_optimize Nat}" = s!"{do_not_optimize Nat}"

-- end TestUnshare2

end Clap
