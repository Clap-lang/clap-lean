import Clap.eDSLState.HashCons.Eval

namespace Clap

namespace ConstraintSystem

section Bob

open HashConsM

def share {p : ℕ}
  (constraints : Array (BoundRef p)) (numAlloc : ℕ)
  (expr : BoundRef p)
:
  HashConsM p (BoundRef p × Array (BoundRef p) × ℕ)
:= do
  let v ← mkVar numAlloc
  let s ← expr - v
  return (v, constraints.push s, numAlloc + 1)

namespace share

def num_constraints : ℕ := 1
def numAllocStep : ℕ := 1

@[simp, grind =]
lemma num_constraints_eq
  {p : ℕ}
  {constraints} {numAlloc}
  {expr}
  {σ : HashConsSt p}
:
  ((share constraints numAlloc expr).getResult σ).2.1.size =
  constraints.size + num_constraints
:= by
  simp [share, num_constraints]

@[simp, grind =]
lemma numAllocStep_eq
  {p : ℕ}
  {constraints} {numAlloc}
  {expr}
  {σ : HashConsSt p}
:
  ((share constraints numAlloc expr).getResult σ).2.2 =
  numAlloc + numAllocStep
:= by
  simp [share, numAllocStep]

end share

end Bob

end ConstraintSystem

end Clap
