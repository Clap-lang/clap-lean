import Mathlib.Data.Nat.Basic

@[irreducible]
def eq0 (n : ℕ) : Option Unit :=
  if n == 0 then some () else none

def repeatN_inner (p : ℕ) : Option Unit := do
  (List.range 100).foldlM (init := ()) fun _ n ↦ do
    eq0 n
