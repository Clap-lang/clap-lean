import Clap.Spec

open Clap Spec Compiler

def repeatN_inner (p : ℕ) : Option Unit := do
  (List.range 100).foldlM (init := ()) fun _ n ↦ do
    eq0 (n : ZMod p)

variable {p : ℕ}

def repeatN (x : ZMod p) : Option Unit := do
  eq0 x
  repeatN_inner p
