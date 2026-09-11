import Clap.eDSLState.HashCons.Eval

namespace Clap.ConstraintSystem

open HashConsM

def isZero {p}
  (constraints : Array ExprRef) (numAlloc : ℕ)
  (expr : ExprRef)
:
  HashConsM p (ExprRef × Array ExprRef × ℕ)
:= do
  let inv ← mkVar numAlloc
  let o ← mkVar (numAlloc + 1)
  let constraint1 ← (←((←mkConstant 1) - (←inv * expr))) - o
  let constraint2 ← o * expr
  return (o, constraints.append #[constraint1, constraint2], numAlloc + 2)

namespace isZero

def num_constraints : ℕ := 2
def numAllocStep : ℕ := 2

@[simp, grind =]
lemma num_constraints_eq
  {p : ℕ}
  {constraints} {numAlloc}
  {expr}
  {σ : HashConsSt p}
:
  ((isZero constraints numAlloc expr).getResult σ).2.1.size =
  constraints.size + num_constraints
:= by
  simp [isZero, num_constraints]

@[simp, grind =]
lemma numAllocStep_eq
  {p : ℕ}
  {constraints} {numAlloc}
  {expr}
  {σ : HashConsSt p}
:
  ((isZero constraints numAlloc expr).getResult σ).2.2 =
  numAlloc + numAllocStep
:= by
  simp [isZero, numAllocStep]

end isZero
end Clap.ConstraintSystem
