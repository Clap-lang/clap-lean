import Clap.Spec
import Clap.Compiler.Cimplol

open Clap Spec Compiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000

def repeatN_inner_raw (p : ℕ) (x : ℕ) : Option Unit := do
  eq0 (x + (List.range' (800 * x) 800).sum : ZMod p)
  -- (List.range 100).map Nat.succ |>.map Nat.succ |>.map Nat.succ |>.foldlM (init := ()) fun _ n ↦ do
  --   eq0 (n : ZMod p)

set_option trace.Clap.Compiler true
set_option trace.Clap.Compiler.preprocess true
set_option Clap.Compiler.cimplolIdentity false

attribute [simpSynthetic]
  List.sum List.foldr_nil List.foldr_cons List.range'_succ List.range'_zero


set_option profiler true

@[simpSynthetic]
def repeatN_inner :=
  cimplol(repeatN_inner_raw, Primes.babybear, simpSynthetic)

variable {p : ℕ}

#print repeatN_inner

def repeatN_raw (x : ZMod p) : Option Unit := do
  eq0 x
  repeatN_inner p 0
  repeatN_inner p 1
  repeatN_inner p 2
  repeatN_inner p 3

attribute [simpSynthetic] bind_assoc Option.bind_assoc

set_option debug.skipKernelTC true
-- set_option profiler.threshold 0

set_option Clap.Compiler.cimplolIdentity false

def repeatN :=
  cimplol(repeatN_raw, Primes.babybear, simpSynthetic)

#print repeatN

-- #print repeatN
