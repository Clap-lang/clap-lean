import Clap.Spec
import Clap.Compiler.Cimplol

open Clap Spec Compiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000

attribute [simp] Option.some_bind Option.bind_some bind_pure pure_bind Option.bind_assoc

def repeatN_inner_raw (p : ℕ) (x : ℕ) : Option Unit := do
  eq0 (x + (List.range' (800 * x) 800).sum : ZMod p)
  -- (List.range 100).map Nat.succ |>.map Nat.succ |>.map Nat.succ |>.foldlM (init := ()) fun _ n ↦ do
  --   eq0 (n : ZMod p)

set_option trace.Clap.Compiler true
set_option trace.Clap.Compiler.preprocess true

attribute [simpSynthetic]
  List.sum List.foldr_nil List.foldr_cons List.range'_succ List.range'_zero

set_option profiler true

set_option Clap.Compiler.cimplolIdentity true in
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

set_option Clap.Compiler.cimplolIdentity true in
def repeatN :=
  cimplol(repeatN_raw, Primes.babybear, simpSynthetic)

#print repeatN

def vectorInput_raw (p : ℕ) (x : Vector ℕ 4) : Option (Vector ℕ 4) := do
  eq0 (x[0] : ZMod p)
  eq0 (x[1] : ZMod p)
  eq0 (x[2] : ZMod p)
  eq0 (x[3] : ZMod p)
  return x.map (·+42)
  -- return #v[x[0], x[1], x[2], x[3]].map (·+42)

set_option Clap.Compiler.cimplolIdentity false in
@[simp]
def vectorInput :=
  cimplol(vectorInput_raw, Primes.babybear, simpAll)

#print vectorInput

def vectorInput_outer_raw (p : ℕ) (x : Vector ℕ 4) : Option (Vector ℕ 4) := do
  let prog := do let y ← vectorInput p (x.map (·+2))
                 return y.map (·+3)
  by rcases x with ⟨x, h⟩
     rcases x with _ | ⟨hd, _ | ⟨hd', _ | ⟨hd'', _ | ⟨hd''', _ | _⟩⟩⟩⟩ <;> try simp at h
     exact prog

set_option Clap.Compiler.cimplolIdentity false in
def vectorInput_outer :=
  cimplol(vectorInput_outer_raw, Primes.babybear, simpAll)

#print vectorInput_outer
