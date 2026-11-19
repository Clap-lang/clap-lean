import Clap.Model.Asm
import Clap.Model.CircuitEvalSt

import Clap.Model.ConstraintSystem.asm
import Clap.Model.ConstraintSystem.isZero

import Clap.Model.WitnessGenerator.asm
import Clap.Model.WitnessGenerator.isZero

import Clap.Model.WitnessGenerator.toWg
import Clap.Test.Backend

import Clap.Model.eDSL
import Clap.Lang.Gate.asm

namespace Clap

open HashConsM OhMyGodAnotherExpr

abbrev isZeroSpec (p : ℕ) [Fact p.Prime] : LawfulGateSpec p where
  numInputs      := 1
  numPrivate     := 1
  numPublic      := 1
  numConstraints := 2
  inputProp _    := True

  constraints    :=
    letI inv : OhMyGodAnotherExpr p 1 2 := local 0
    letI out : OhMyGodAnotherExpr p 1 2 := local 1
    letI x   : OhMyGodAnotherExpr p 1 2 := input 0
    #v[1 - inv * x - out, out * x]

  witness xs := (#v[xs[0]⁻¹], #v[if xs[0] = 0 then 1 else 0])

  sound := by
    intros inputs locals out h
    simp [
      constraintsHold, OhMyGodAnotherExpr.eval, BinaryOp.apply, sub_eq_binary_op,
      mul_eq_binary_op, ofNat_eq_const
    ] at h
    have : (locals ++ out)[0] = locals[0] := by grind
    simp [this] at *
    grind
  
  complete := by
    simp [
      constraintsHold, OhMyGodAnotherExpr.eval, BinaryOp.apply, sub_eq_binary_op,
      mul_eq_binary_op, ofNat_eq_const
    ]
    grind

namespace isZeroSpec

variable {p : ℕ} [Fact p.Prime]

/--
Sanity check 0: witness generator is witness generatoring
-/
lemma asmUnsafe_eq {cache : ValueCache p} {trace : Array (ZMod p)} {e : ExprRef} :
  WitnessGenerator.asmUnsafe (isZeroSpec p).toGateSpec cache trace #v[e] =
  WitnessGenerator.isZeroUnsafe cache trace e
:= by
  simp [WitnessGenerator.asmUnsafe, GateSpec.witnessInOrder, WitnessGenerator.isZeroUnsafe]
  rfl

/--
Sanity check 1: constraint system is constraint systeming
-/
lemma asm_eq {constraints : Array ExprRef} {numAlloc : ℕ} {e : ExprRef} :
  ConstraintSystem.asm (isZeroSpec p).toGateSpec constraints numAlloc #v[e] =
  (·.2) <$> ConstraintSystem.isZero constraints numAlloc e
:= by
  simp [ConstraintSystem.asm, GateSpec.numTotalVariables, Vector.ofFnM_succ, Vector.ofFnM_zero,
    OhMyGodAnotherExpr.toHashConsSt, sub_eq_binary_op, mul_eq_binary_op, ofNat_eq_const,
    ConstraintSystem.isZero, HashConsM.mul_def, HashConsM.sub_def, HashConsM.mkMul, HashConsM.mkSub]

@[simp, grind =]
lemma outputs_eq {inputs : Vector (ZMod p) 1} :
  (isZeroSpec p).outputs inputs = #v[if inputs[0] = 0 then 1 else 0] := rfl

@[simp, grind =]
lemma assertions_eq_true {inputs : Vector (ZMod p) 1} :
  (isZeroSpec p).assertions inputs = True := by trivial

/--
Sanity check 2: For an allocated expression, `stepAsm` for `isZeroSpec` _is_* `stepIsZero`

- * Technically, it's step is `stepIsZero ∧ True`. Don't tell anyone.
-/
@[grind .]
lemma stepAsm_eq_addConstraint_true_stepIsZero {st : EvalSt p} {σ : HashConsSt p} {e : ExprRef}
  (h : ⦃e, σ⦄ ∈ st) :
  st.stepAsm σ (isZeroSpec p).toGateSpec #v[e] = (st.stepIsZero σ e).addConstraint True := by
  obtain ⟨numAlloc, Γ, constraints⟩ := st
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  simp at hv
  simp [EvalSt.stepAsm, EvalSt.stepIsZero, GateSpec.outputs, GateSpec.assertions, hv]

/--
Sanity check 3: #2 but with mustache
-/
lemma step_asm_eq_addConstraint_true_step_isZero {st : EvalSt p} {σ : HashConsSt p} {e : ExprRef}
  (h : ⦃e, σ⦄ ∈ st) :
  st.step (.asm p (isZeroSpec p) #v[e]) σ = (st.step (.isZero e) σ).addConstraint True := by
  rw [EvalSt.step_asm, EvalSt.stepAsmSilly_eq_stepAsm, EvalSt.step_isZero]
  exact stepAsm_eq_addConstraint_true_stepIsZero h

/--
Sanity check 4: layout is layouting
-/
lemma layoutLayouts {e : ExprRef} :
  let asmGate := Gate.asm p (isZeroSpec p) #v[e]
  asmGate.numAllocStep = (Gate.isZero e).numAllocStep ∧
  ConstraintSystem.privateAllocs asmGate = ConstraintSystem.privateAllocs (.isZero e) ∧
  ConstraintSystem.num_constraints asmGate = ConstraintSystem.num_constraints (.isZero e) ∧
  WitnessGenerator.trace_capacity asmGate = WitnessGenerator.trace_capacity (.isZero e) :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
Sanity check 5: `ClapM` is `ClapM`ing
-/
lemma clapM_clapMs {numAlloc : ℕ} {σ : HashConsSt p} {e : ExprRef} :
  letI asmGate := asm (isZeroSpec p) #v[e]
  (asmGate.getResult numAlloc σ)[0]   = (isZero e).getResult numAlloc σ ∧
  asmGate.getNumAlloc numAlloc σ      = (isZero e).getNumAlloc numAlloc σ ∧
  asmGate.getHashConsState numAlloc σ = (isZero e).getHashConsState numAlloc σ := by
  unfold asm isZero
  refine ⟨?_, ?_, ?_⟩ <;> simp [Vector.ofFnM_succ, Vector.ofFnM_zero]

/--
Sanity check 6:

For an allocated expression,
`runAndEval` on `.asm isZeroSpec` _is the same_* as `runAndEval` on `isZero`,

- * Technically, there's a trailing `∧ True`. Don't tell anyone.
-/
lemma runAndEval_eq {numAlloc : ℕ} {Γ : VarStore p} {σ : HashConsSt p} {e : ExprRef}
  (h₁ : e < σ.size) (h₂ : ⦃e, σ⦄ ∈ unconstrained[numAlloc][Γ]) :
  letI asmGate := asm (isZeroSpec p) #v[e]
  letI asmGateRun := asmGate.runAndEval numAlloc Γ σ
  asmGateRun.1[0] = ((isZero e).runAndEval numAlloc Γ σ).1 ∧
  asmGateRun.2 = ((isZero e).runAndEval numAlloc Γ σ).2.addConstraint True := by
  have h_mem : ⦃e, (mkVar (p := p) numAlloc).getHashConsState σ⦄ ∈ unconstrained[numAlloc][Γ] := by
    simp only [EvalSt.membership_unconstrained] at h₂ ⊢
    exact isSome_eval_of_prefix (e₁ := ⦃e, σ⦄) h₁ h₂ rfl isPrefixOf_mkVar
  refine ⟨clapM_clapMs.1, ?_⟩
  rw [eval_edsl_asm, eval_edsl_isZero, Circuit.eval_isZero, EvalSt.step_isZero,
    ← stepAsm_eq_addConstraint_true_stepIsZero h_mem]
  simp [Vector.ofFnM_succ, Vector.ofFnM_zero]

end isZeroSpec

namespace Tests

-- Note the prime is 47 in the original test fine
-- def testCircuit : Circuit := #[
--   .isZero 4, -- (.v 0 + .v 1) - .v 2
--   .eq0 5 -- .v 2 ≠ .v 0 + .v 1
-- ]

def testCircuitAsm : Circuit := #[
  .asm 47 (isZeroSpec 47) #v[4], -- (.v 0 + .v 1) - .v 2
  .eq0 5 -- .v 2 ≠ .v 0 + .v 1
]

def testCsAsm := testCircuitAsm.toCs testCache 3
def testWgAsm := testCircuitAsm.toWg testCache 3

def witnessesAsm := inputs.map testWgAsm.run
def evaluationsAsm := witnessesAsm.map testCsAsm.run

#guard witnessesAsm == witnesses
#guard evaluationsAsm == evaluations

end Tests

namespace Lang

variable {p : ℕ} [Fact p.Prime]

def isZeroAsm (a : F p) : ClapM p (FB p) := (·[0]) <$> asm (isZeroSpec p) #v[a]

/-
 lemma convertsM
   [p.AtLeastTwo]
   {state}
   {a : F p}
   {a_val : ZMod p}
   (h_a : Converts F.conversion state a a_val)
 :
   ConvertsM FB.conversion (isZero a)
     state
     (a_val == 0)
     True
-/

namespace isZeroAsm

/--
`isZeroAsm` now behaves as `isZero` from the 'interface' perspective.
-/
lemma convertsM
  {state : ClapMState p}
  {a : F p}
  {a_val : ZMod p}
  (h : Converts F.conversion state a a_val) :
  ConvertsM FB.conversion (isZeroAsm a)
    state
    (a_val == 0)
    True := by
  have h_inputs : Converts FVec.conversion state (#v[a] : FVec p 1) #v[a_val] :=
    FVec.converts_iff_F_converts.mpr fun i ↦ by
      obtain rfl := Fin.eq_zero i
      simpa using h
  have h_asm := asm.convertsM (spec := isZeroSpec p) h_inputs
  refine convertsM_map h_asm ?_ (by simp)
  exact converts_cast (FVec.converts_iff_F_converts.mp h_asm.result 0) rfl
    (by simp [GateSpec.outputs])

end isZeroAsm

end Lang

end Clap
