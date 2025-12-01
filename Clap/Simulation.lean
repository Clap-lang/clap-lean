import Clap.Circuit

namespace Simulation

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
inductive s_bisim : (l r: denotation) -> Prop where
  | none
      : s_bisim .n .n
  | unit
      : s_bisim .u .u
  | lam
      (kl kr:F -> denotation)
      (h: ∀ x, s_bisim (kl x) (kr x))
      : s_bisim (.l kl) (.l kr)

/-
  Right-weak bisimulation.
  Allows the right player, typically the Cs, to receive more inputs
  than the left one.
-/
inductive rw_bisim : (c cs: denotation) -> Prop where
  | none
      (c:denotation)
      : rw_bisim c .n
  | same
      (c:denotation)
      : rw_bisim c c -- not sure we need the generalization, maybe .u .u is enough
  | lam
      (kl kr:F -> denotation)
      (h: ∀ x, rw_bisim (kl x) (kr x))
      : rw_bisim (.l kl) (.l kr)
  | right
      (l:denotation)
      (kr:F -> denotation)
      (h: ∀ x, rw_bisim l (kr x))
      : rw_bisim l (.l kr)

end Simulation
