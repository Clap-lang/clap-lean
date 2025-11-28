import Mathlib.Control.Monad.Cont
import Clap.Circuit

set_option autoImplicit false
set_option linter.unusedVariables true

/-
  Phoas uses continuations, it may seem natural to look into the continuation monad.
  However notice that we don't need true continuation, in the sense of returning an arbitrary type, and we don't do any fancy control flow.
  True continuations seem overkill and additionally we'd need to reason over a Cont monad!
-/

namespace Cont_monad

abbrev C var a := Cont (Circuit var) a -- = (a -> Circuit var) -> Circuit var

def lam {var} : C var var := fun k =>
  Circuit.lam k

def eq0 {var} (e:Exp var) : C var Unit := fun k =>
  Circuit.eq0 e (k ())

def share {var} (e:Exp var) : C var var := fun k =>
  Circuit.share e k

def is_zero {var} (e:Exp var) : C var var := fun k =>
  Circuit.is_zero e k

example {var} : C var Unit := do
  let i <- lam
  let zero <- share (.c 0)
  eq0 (.v zero + .v i) ;
  eq0 (.v zero + .v i)

end Cont_monad

/-
  We can achieve something similar using just notation.
  Again, under the notation we still need to reason about
  continuations, but there is no bind at least.
-/

namespace Notation

-- these are just sketched, probably wrong in many corner cases
scoped notation "let" x ":=" "input" "()" "in" body => Circuit.lam (fun x => body)
scoped notation "eq0" e => Circuit.eq0 e Circuit.nil
scoped notation "eq0" e ";" rest => Circuit.eq0 e rest
scoped notation "let" x ":=" "share" e "in" body => Circuit.share e (fun x => body)

def x : Circuit' := fun _ =>
  let i := input () in
  let zero := share (.c 0) in
  eq0 (.v zero + .v i) ;
  eq0 (.v zero + .v i)

set_option pp.notation false
example : x = x := by
  unfold x
  sorry

end Notation

/-
  This is the ideal specification language that we'd like to work with.
  some () can be seen as true and none as false, using Option α
  however allows functions to return more interesting things than ().
-/

namespace Spec

def eq0 (e:F) : Option Unit :=
  if e = 0 then some () else none

-- just the identity
def share (e:F) : F := e

def is_zero (e:F) : F := if e = 0 then 1 else 0

/-
  A circuit is a function from any number of F arguments to Option Unit.
-/

def ex (i:F) : Option Unit := do
  let zero := share 0
  eq0 (zero + i)
  eq0 (zero + i)

end Spec

/-
  Our Circuit type has its own `denotation` which is different than Option Unit.
  We can however take a denotation and map it to a corresponding Spec type.
-/

def deno2spec (d:denotation) : Type :=
  match d with
  | .u => Option Unit
  | .n => Option Unit
  | .l f => (x:F) -> deno2spec (f x)

/-
  Now we can define a notion of equivalence between our Spec programs and the denotation of our Circuits.
-/

inductive s_bisim : (l: denotation) -> (r:deno2spec l) -> Prop where
  | none
      : s_bisim .n none
  | unit
      : s_bisim .u (some ())
  | lam
      (kl:F -> denotation)
      (kr:deno2spec (.l kl))
      (h: ∀ x, s_bisim (kl x) (kr x))
      : s_bisim (.l kl) kr

notation : 65 t:65 "≡" s:66 => s_bisim t s

/-
  Given a Source program, there exists a denotation that is equivalent to it.
  - We just have to find it -
-/

example : ∃ (c:Circuit'), eval' c ≡ Spec.ex := by
/-
  eval' ?c ≡ ex
unfold eval'
  eval (?d F) ≡ ex
era-espand
  eval ((fun var => ?e) F) ≡ ex
simp
  eval ?f ≡ ex
unfold ex, ?f can only be a .lam
  eval (.lam ?k) ≡ fun i => rest
simp eval
  .l (fun x -> eval (?k x)) ≡ fun i => rest
s_bisim.lam
  ∀ x, eval (?k x) ≡ rest
unfold rest right to left
  eval ((fun y => ?g (eq0 (zero + x) nil)) x) ≡ rest' ; eq0 (zero+x)
unfold rest right to left
  eval ((fun y => ?h (eq0 (zero + x) (eq0 (zero + x) nil)) x) ≡ rest'' ; eq0 (zero+x) ; eq0 (zero+x)
  eval ((fun y => share (.c 0) (fun zero -> (eq0 (zero + x) (eq0 (zero + x) nil)))) x) ≡ let zero = share 0 ; eq0 (zero+x) ; eq0 (zero+x)

-/

  sorry
