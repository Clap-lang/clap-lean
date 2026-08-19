import Mathlib.Data.ZMod.Basic
import Clap.eDSLState.Monad
import Clap.eDSLState.Varstore

import Clap.eDSLState.Convert

namespace Clap

abbrev withΓ (p : ℕ) (α ω : Type) := (VarStore p) → α → ω

def unaryFunctionResultIsValidIff (p : ℕ)
  {funIn funOut : Type}
  [IsValid p funIn] [IsValid p funOut]
  (function : funIn → funOut)
: Prop :=
  ∀ (a : funIn) (varStorePre : VarStore p),
    (IsValid.isValid varStorePre a ↔
    IsValid.isValid varStorePre (function a))

@[grind .]
lemma unaryFunctionResultIsValidIff_def {p : ℕ}
  {funIn funOut : Type}
  [IsValid p funIn] [IsValid p funOut]
  {function : funIn → funOut}
  {a : funIn}
  {varStore : VarStore p}
  (h : unaryFunctionResultIsValidIff p function)
:
  (IsValid.isValid varStore a ↔
  IsValid.isValid varStore (function a))
:= h a varStore

def unaryFunctionResultIsCorrect (p : ℕ)
  {funIn funOut specIn specOut : Type}
  [Convert p funIn specIn] [Convert p funOut specOut]
  (spec_function : specIn → specOut)
  (function : funIn → funOut) : Prop :=
  ∀ (a : funIn) (varStorePre : VarStore p),
    letI aVal : Option specIn := Convert.toIdeal varStorePre a
    letI resultVal : Option specOut := Convert.toIdeal varStorePre (function a)
    letI wrapped : Option funOut := (aVal.map spec_function).map (Convert.toRepresents p)
    resultVal = wrapped.bind (Convert.toIdeal varStorePre)

def matchesUnaryFunction (p : ℕ)
  {funIn funOut specIn specOut : Type}
  [Convert p funIn specIn] [Convert p funOut specOut]
  (spec_function : specIn → specOut)
  (function : funIn → funOut)
: Prop :=
  unaryFunctionResultIsValidIff p function ∧
  unaryFunctionResultIsCorrect p spec_function function

@[grind .]
lemma matchesUnaryFunction_of_valid_ofs_correct {p : ℕ}
  {funIn funOut specIn specOut : Type}
  [Convert p funIn specIn] [Convert p funOut specOut]
  {spec_function : specIn → specOut}
  {function : funIn → funOut}
  (hValid : unaryFunctionResultIsValidIff p function)
  (hCorrect : unaryFunctionResultIsCorrect p spec_function function)
:
  matchesUnaryFunction p spec_function function
:= by
  unfold matchesUnaryFunction
  grind

@[grind →]
lemma resultIsValidIff_of_matchesUnaryFunction {p : ℕ}
  {funIn funOut specIn specOut : Type}
  [Convert p funIn specIn] [Convert p funOut specOut]
  {spec_function : specIn → specOut}
  {function : funIn → funOut}
  (h : matchesUnaryFunction p spec_function function)
:
  unaryFunctionResultIsValidIff p function
:= h.1

@[grind →]
lemma resultIsCorrect_of_matchesUnaryFunction {p : ℕ}
  {funIn funOut specIn specOut : Type}
  [Convert p funIn specIn] [Convert p funOut specOut]
  {spec_function : specIn → specOut}
  {function : funIn → funOut}
  (h : matchesUnaryFunction p spec_function function)
:
  unaryFunctionResultIsCorrect p spec_function function
:= h.2


def matchesBinaryFunction (p : ℕ)
  {funIn funOut specIn specOut : Type}
  [Convert p funIn specIn] [Convert p funOut specOut]
  (spec_function : specIn → specIn → specOut)
  (function : funIn → funIn → funOut) : Prop :=
  ∀ (a b : funIn) (varStorePre : VarStore p),
    (h₁ : IsValid.isValid varStorePre a) →
    (h₂ : IsValid.isValid varStorePre b) →
      letI aVal : specIn :=
        Convert.toIdeal varStorePre a |>.get ((Convert.isValid_iff_isSome_toIdeal _ _).mp h₁)
      letI bVal : specIn :=
        Convert.toIdeal varStorePre b |>.get ((Convert.isValid_iff_isSome_toIdeal _ _).mp h₂)
      letI resultVal : Option specOut := Convert.toIdeal varStorePre (function a b)
      letI wrapped : funOut := Convert.toRepresents p (spec_function aVal bVal)
      resultVal = Convert.toIdeal varStorePre wrapped

@[grind .]
lemma isValid_of_isValid_of_matchesUnaryFunction {p : ℕ}
  {funIn funOut specIn specOut : Type}
  [Convert p funIn specIn] [inst_out: Convert p funOut specOut]
  {spec_function : specIn → specOut}
  {function : funIn → funOut}
  {a : funIn}
  {varStore : VarStore p}
  (h_equiv : matchesUnaryFunction p spec_function function)
  (h_isValid : IsValid.isValid varStore a)
:
    IsValid.isValid varStore (function a)
:= by
  grind

def assertMatchesLast {k} {p}
  (varStore : VarStore p) (numAlloc : ℕ) (vec : Vector (ZMod p) k) : Prop :=
  ∀ i < k,
    letI varStoreIdx := numAlloc - k + i
    varStore[varStoreIdx]? = vec[i]?

-- TODO, this needs to consider constraints
-- Do we want results to always be valid if the inputs are valid?
-- Or only when the constraints also hold?
def unaryMonadFunctionResultIsValidIff (p : ℕ)
  {funIn funOut : Type}
  [IsValid p funIn] [IsValid p funOut]
  (function : funIn → ClapM p funOut)
  {varStorePre : VarStore p}
  {numAllocPre : ℕ}
  {σPre : HashConsSt p}
: Prop :=
  ∀ (a : funIn),
    (IsValid.isValid varStorePre a ↔
    IsValid.isValid varStorePre (function a))

open Convert VarStoreSize in
def commandMatchesSpec (p : ℕ)
  {funOut specOut : Type}
  [Convert p funOut specOut]
  [VarStoreSize p funOut]
  (spec : specOut)
  (cmd : ClapM p funOut)
  (varStore : VarStore p)
  (numAlloc : ℕ)
  (σ : HashConsSt p)
  (constraints : Prop)
: Prop :=
  Convert.toIdeal varStore (cmd.getResult numAlloc σ) = .some spec ∧
  let ⟨result, circuit⟩ : funOut × EvalSt p := ClapM.runAndEval cmd numAlloc varStore σ
  let constraintsCorrect := circuit.constraints ↔ constraints
  -- let allocatesCorrect := circuit.numAlloc = numAlloc + allocatesN -- hey, may or may not be needed at some point in the future
  let frameRule := ∀ n < numAlloc, circuit.varStore[n]? = varStore[n]?
  letI linearRepr := toLinear circuit.varStore result
  let resultInVarStore := assertMatchesLast circuit.varStore circuit.numAlloc linearRepr
  constraintsCorrect ∧
  -- allocatesCorrect ∧
  frameRule ∧
  resultInVarStore

def binaryFunctionResultIsValidIff (p : ℕ)
  {funIn₁ funIn₂ funOut : Type}
  [IsValid p funIn₁] [IsValid p funIn₂] [IsValid p funOut]
  (function : funIn₁ → funIn₂ → funOut)
: Prop :=
  ∀ (a₁ : funIn₁) (a₂ : funIn₂) (varStorePre : VarStore p),
    ((IsValid.isValid varStorePre a₁ ∧ IsValid.isValid varStorePre a₂) ↔
    (IsValid.isValid varStorePre (function a₁ a₂)))

-- open Convert VarStoreSize Edsl in
-- def matchesBinaryMonadFunction (p : ℕ)
--   {funIn₁ funIn₂ funOut specIn₁ specIn₂ specOut : Type}
--   [Convert p funIn₁ specIn₁] [Convert p funOut specOut]
--   [VarStoreSize p funOut]
--   [Convert p funIn₂ specIn₂]
--   (spec_function : specIn₁ → specIn₂ → specOut)
--   (function : funIn₁ → funIn₂ → CircuitM p funOut)
--   (allocatesN : ℕ)
--   (constraints : specIn₁ → specIn₂ → Prop)
-- : Prop :=
--   unaryFunctionResultIsValidIff p function ∧
--   (∀ numAllocPre, unaryFunctionResultIsCorrect p spec_function (λ a => (function a).getResult numAllocPre)) ∧
--   ∀ (a : funIn) (varStorePre : VarStore p) (numAllocPre : ℕ),
--     (h : IsValid.isValid varStorePre a) →
--       letI aVal : specIn := toIdeal varStorePre a |>.get ((Convert.isValid_iff_isSome_toIdeal _ _).mp h)
--       let ⟨result, circuit⟩ : funOut × CircuitResult p :=
--         CircuitM.runAndEval (function a) numAllocPre varStorePre
--       let constraintsCorrect := circuit.constraints = (constraints aVal)
--       let allocatesCorrect := circuit.numAlloc = numAllocPre + allocatesN
--       let frameRule := ∀ n < numAllocPre, circuit.varStore[n]? = varStorePre[n]?
--       letI linearRepr := toLinear circuit.varStore result
--       let resultInVarStore := assertMatchesLast circuit.varStore circuit.numAlloc linearRepr
--       constraintsCorrect ∧
--       allocatesCorrect ∧
--       frameRule ∧
--       resultInVarStore

namespace SpecGen

def preamble := "open Convert VarStoreSize Edsl in"

def signature (arity : ℕ) :=
  name
  where
    aritySuffix := s!"arity{arity}"
    name := s!"matchesNaryMonadFunction{aritySuffix}"
    argPrime := "(p : ℕ)"
    argInputs := Array.range arity |>.flatMap fun i ↦
      #[s!"\{funIn{i}} : Type", s!"\{specIn{i}} : Type"]
    argOutputs := #["{funOut : Type}", "{specOut : Type}"]

open Lean Meta Elab Term Command in
elab "#spec" spec:ident f:ident : command => liftTermElabM do
  let spec ← realizeGlobalConstNoOverload spec
  let f ← realizeGlobalConstNoOverload f

  let env ← getEnv
  let .some spec := env.find? spec | unreachable!
  let .some f := env.find? f | unreachable!

  let arity := spec.type.getForallArity

  logInfo m!"Spec (arity := {arity}) = {spec.name} : {spec.type}\n"
  logInfo m!"Function = {f.name} : {f.type}\n"

end SpecGen

end Clap
