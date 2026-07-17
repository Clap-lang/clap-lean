import Clap.Compiler.Back.Circuit

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
inductive strongBisim : denotation F → denotation F → Prop where
  | none : strongBisim .n .n
  | unit : strongBisim .u .u
  | lam {kl kr : F → denotation F}
        (h : ∀ x, strongBisim (kl x) (kr x)) : strongBisim (.l kl) (.l kr)

/--
  Spec bisimulation between a Lean term of type `(F -> ... -> Option
  Unit` and a denotation, typically produced by the evaluation of a
  Circuit.
-/
inductive sBisim : Π {t : Type}, t → denotation F → Prop where
  | none : sBisim none .n
  | unit : sBisim (some ()) .u
  | lam {t' : Type} {kl : F → t'} {kr : F → denotation F}
        (h : ∀ x, sBisim (kl x) (kr x)) : sBisim kl (.l kr)

attribute [simp] sBisim.none sBisim.unit

scoped infix:51 " ~ₛ " => sBisim

/-
  Weak-right bisimulation.
  Allows the right player, typically the Cs, to receive more inputs
  than the left one.
-/
inductive wrBisim : denotation F → denotation F → Prop where
  | none {c : denotation F} : wrBisim c .n
  | same {c : denotation F} : wrBisim c c -- not sure we need the generalization, maybe .u .u is enough
  | lam {kl kr : F → denotation F}
        (h : ∀ x, wrBisim (kl x) (kr x)) : wrBisim (.l kl) (.l kr)
  | right {l : denotation F} {kr : F → denotation F}
          (h : ∀ x, wrBisim l (kr x)) : wrBisim l (.l kr)

attribute [simp] wrBisim.none wrBisim.same

end Simulation

end Clap
