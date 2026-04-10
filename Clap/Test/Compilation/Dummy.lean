import Clap.Spec
import Clap.Compiler.Cimplol

open Clap Spec Compiler

-- set_option debug.skipKernelTC true
-- set_option maxRecDepth 1000000
-- set_option maxHeartbeats 800000
-- set_option trace.Clap.Compiler true
-- set_option trace.Clap.Compiler.preprocess true
-- set_option profiler true
-- set_option profiler.threshold 0

-- attribute [simp] Option.some_bind Option.bind_some bind_pure pure_bind Option.bind_assoc

abbrev p := Primes.bn254

def mixS {n : ℕ} (r:ℕ) (x : Vector (ZMod p) n) : Option (Vector (ZMod p) n) := do
  eq0 (x[0]! + (List.range' (800 * r) 800).sum : ZMod p)
  x

-- attribute [simpSynthetic]
--   List.sum List.foldr_nil List.foldr_cons List.range'_succ List.range'_zero
-- set_option Clap.Compiler.cimplolIdentity true in
-- #cimplol(mixS, Primes.bn254, simpSynthetic)

def poseidon {n:ℕ} (x : Vector (ZMod p) n) : Option (ZMod p) := do
  let state ← (List.range 4).foldlM (fun state r ↦ mixS r state) (init:=x)
  state.sum

-- attribute [simpSynthetic] bind_assoc Option.bind_assoc
-- set_option Clap.Compiler.cimplolIdentity true in
-- def repeatN :=
--   cimplol(repeatN_raw, Primes.babybear, simpSynthetic)

def keyless (x : Vector (ZMod p) 2) (y : Vector (ZMod p) 4) : Option Unit := do
  let x ← poseidon x
  let y ← poseidon y
  eq0 (x+y)

-- set_option Clap.Compiler.cimplolIdentity false in
-- @[simp]
-- def vectorInput :=
--   cimplol(vectorInput_raw, Primes.babybear, simpAll)
