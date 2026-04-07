import Clap.Compiler.Basic

namespace Clap

@[irreducible]
def eq0 (n : ℕ) : Option Unit :=
  if n == 0 then some () else none

set_option maxRecDepth 1000000
set_option debug.skipKernelTC true

#check List.range_succ

-- attribute [local unfoldStuff] Option.some_bind List.foldlM_append List.foldlM_cons List.foldlM_nil List.range_zero List.range_succ -- pure_bind bind_pure bind_assoc Option.bind_assoc 

attribute [local unfoldStuff] List.reduceRange List.foldlM_cons List.foldlM Option.pure_def

set_option profiler true

def repeatN_inner (p : ℕ) : Option Unit := do
  (List.range 10000).foldlM (init := ()) fun _ n ↦ do
    eq0 n


#compile repeatN_inner using Primes.bn254 iters 1

#print repeatN_inner_circuit


-- def repeatN : Option Unit := repeatN_inner_circuit


def circuit (p : ℕ) (x : ℕ) : Option Unit := do
  let result : Option Unit :=
    (List.range 1000).foldlM (init := ()) fun _ _ ↦ do repeatN_inner_circuit
  eq0 x
  result
set_option profiler true
set_option profiler.threshold 50
-- set_option trace.Clap.Compiler.reduce.simplify true
-- set_option trace.Meta.Tactic.simp true
-- set_option pp.exprSizes true

-- Profiler --
-- set_option trace.Clap.Compiler true
-- set_option trace.profiler true
-- Profiler --

--       10 - 0.044258
--      100 - 0.234770 | 5 * 20 - 0.300000
--     1000 - simp maxRecDepth fail (set_option maxRecDepth 1000000 = 1.86s)
-- 100 * 30 - simp took 8.24s

-- attribute [local unfoldStuff] Option.some_bind List.reduceRange repeatN_inner_circuit -- pure_bind bind_pure bind_assoc Option.bind_assoc 

-- #compile circuit using Primes.bn254 iters 1 -- simp took 480ms 

-- -- #print circuit_circuit

end Clap
