import Clap.Spec
import Clap.Compiler.Cimplol

open Clap Spec Compiler

def repeatN_inner_raw (p : ℕ) : Option Unit := do
  (List.range 10).foldlM (init := ()) fun _ n ↦ do
    eq0 (n : ZMod p)

set_option trace.Clap.Compiler true
set_option trace.Clap.Compiler.preprocess true
set_option Clap.Compiler.cimplolIdentity false

@[simpSynthetic]
def repeatN_inner :=
  cimplol(repeatN_inner_raw, Primes.babybear, simpSynthetic)

variable {p : ℕ}

#print repeatN_inner

def repeatN_raw (x : ZMod p) : Option Unit := do
  eq0 x
  repeatN_inner p
  repeatN_inner p
  repeatN_inner p
  repeatN_inner p
  repeatN_inner p

def repeatN :=
  cimplol(repeatN_raw, Primes.babybear, simpSynthetic)

#print repeatN
