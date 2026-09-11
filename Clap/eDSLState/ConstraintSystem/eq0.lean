import Clap.eDSLState.HashCons.Eval

namespace Clap

namespace ConstraintSystem

section Bob

open HashConsM

def eq0 {p : ℕ}
  (constraints : Array (BoundRef p)) (numAlloc : ℕ)
  (expr : BoundRef p)
:
  HashConsM p (Array (BoundRef p) × ℕ)
:= do
  return (constraints.push expr, numAlloc)

namespace eq0

def num_constraints : ℕ := 1
def numAllocStep : ℕ := 0

@[simp, grind =]
lemma num_constraints_eq
  {p : ℕ}
  {constraints} {numAlloc}
  {expr}
  {σ : HashConsSt p}
:
  ((eq0 constraints numAlloc expr).getResult σ).1.size =
  constraints.size + num_constraints
:= by
  simp [eq0, num_constraints]

@[simp, grind =]
lemma numAllocStep_eq
  {p : ℕ}
  {constraints} {numAlloc}
  {expr}
  {σ : HashConsSt p}
:
  ((eq0 constraints numAlloc expr).getResult σ).2 =
  numAlloc + numAllocStep
:= by
  simp [eq0, numAllocStep]

end eq0

end Bob

end ConstraintSystem

end Clap
