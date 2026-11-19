import Clap.Model.Asm

namespace Clap.ConstraintSystem

open HashConsM

def asm {p}
  (spec : GateSpec p)
  (constraints : Array ExprRef)
  (numAlloc : ℕ)
  (inputs : Vector ExprRef spec.numInputs) : HashConsM p (Array ExprRef × ℕ) := do
  let fresh ← Vector.ofFnM fun j ↦ mkVar (p := p) (numAlloc + j)
  let new ← Vector.ofFnM fun i ↦ spec.constraints[i].toHashConsSt inputs fresh
  return (constraints ++ new.toArray, numAlloc + spec.numTotalVariables)

def asmSilly {p p'}
  (spec : LawfulGateSpec p')
  (constraints : Array ExprRef)
  (numAlloc : ℕ)
  (inputs : Vector ExprRef spec.numInputs) : HashConsM p (Array ExprRef × ℕ) :=
  if h : p' = p then
    match p', spec, inputs, h with
    | _, spec, inputs, rfl => asm spec.toGateSpec constraints numAlloc inputs
  else do
    return (constraints.push (←mkConstant 1), numAlloc + spec.numTotalVariables)

namespace asm

variable {p : ℕ} {spec : GateSpec p}

variable {constraints : Array ExprRef} {numAlloc : ℕ} {inputs : Vector ExprRef spec.numInputs}
         {σ : HashConsSt p}

@[simp, grind =]
lemma num_constraints_eq :
  ((asm spec constraints numAlloc inputs).getResult σ).1.size =
  constraints.size + spec.numConstraints := by
  show (constraints ++ (Vector.toArray (n := spec.numConstraints) _)).size = _
  simp

@[simp, grind =]
lemma numAllocStep_eq :
  ((asm spec constraints numAlloc inputs).getResult σ).2 =
  numAlloc + spec.numTotalVariables :=
  rfl

end asm

end Clap.ConstraintSystem
