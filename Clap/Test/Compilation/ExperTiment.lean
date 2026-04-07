import Clap.Compiler.Basic

namespace Clap

@[irreducible]
def eq0 (n : ℕ) : Option Unit :=
  if n == 0 then some () else none

set_option maxRecDepth 1000000

def circuit (p : ℕ) (x : ℕ) : Option Unit := do
  let result : Option Unit :=
    (List.range 1000).foldlM (init := ()) fun _ n ↦ do
      eq0 n
  eq0 x
  result
set_option profiler true
-- set_option trace.Clap.Compiler.reduce.simplify true

set_option pp.exprSizes true

-- Profiler --
-- set_option trace.Clap.Compiler true
-- set_option trace.profiler true
-- Profiler --

--       10 - 0.044258
--      100 - 0.234770
--     1000 - simp maxRecDepth fail (set_option maxRecDepth 1000000 = 1.86s)
#compile circuit using Primes.bn254 iters 1

end Clap
