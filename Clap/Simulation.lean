import Clap.Circuit

namespace Clap

namespace Simulation

variable {F : Type}

/-
  This file contains the bisimulations that might be needed when
  equality between denotations is too strict.
  For example the right-weak bisimulation is needed to prove soundness
  of compilation to Cs.
-/

/-
  Strong bisimulation. This is just for illustrative purposes as it
  (should) be equivalent to equality with functional extensionality.
-/
inductive strong_bisim : (l r: denotation F) -> Prop where
  | none
      : strong_bisim .n .n
  | unit
      : strong_bisim .u .u
  | lam
      (kl kr:F -> denotation F)
      (h: ∀ x, strong_bisim (kl x) (kr x))
      : strong_bisim (.l kl) (.l kr)

/--
  Spec bisimulation between a Lean term of type `(F -> ... -> Option
  Unit` and a denotation, typically produced by the evaluation of a
  Circuit.
-/
inductive s_bisim : {t:Type} -> (l:t) -> (r: denotation F) -> Prop where
  | none
      : s_bisim none .n
  | unit
      : s_bisim (some ()) .u
  | lam
      {t':Type}
      (kl:F -> t')
      (kr:F -> denotation F)
      (h: ∀ x, s_bisim (kl x) (kr x))
      : s_bisim kl (.l kr)

/-
  Right-weak bisimulation.
  Allows the right player, typically the Cs, to receive more inputs
  than the left one.
-/
inductive rw_bisim : (c cs: denotation F) -> Prop where
  | none
      (c:denotation F)
      : rw_bisim c .n
  | same
      (c:denotation F)
      : rw_bisim c c -- not sure we need the generalization, maybe .u .u is enough
  | lam
      (kl kr:F -> denotation F)
      (h: ∀ x, rw_bisim (kl x) (kr x))
      : rw_bisim (.l kl) (.l kr)
  | right
      (l:denotation F)
      (kr:F -> denotation F)
      (h: ∀ x, rw_bisim l (kr x))
      : rw_bisim l (.l kr)

end Simulation
