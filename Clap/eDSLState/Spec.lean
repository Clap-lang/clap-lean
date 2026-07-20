import Mathlib.Data.ZMod.Basic
import Clap.eDSLState.Monad
import Clap.eDSLState.Varstore

namespace Clap

abbrev withΓ (p : ℕ) (α ω : Type) := (VarStore p) → α → ω

class IsValid (p : ℕ) (α : Type) where
  isValid : withΓ p α Prop

class VarStoreSize (p : ℕ) (α : Type) where
  size : ℕ
  toLinear : (VarStore p) → α → Vector (ZMod p) size

attribute [reducible] VarStoreSize.size

instance instVarStoreSizeUnit {p : ℕ} : VarStoreSize p Unit where
  size := 0
  toLinear _ _ := #v[]

@[grind =]
lemma instVarStoreSizeUnit_size {p : ℕ}:
  (@instVarStoreSizeUnit p).size = 0
:= rfl

@[grind =]
lemma instVarStoreSizeUnit_size' {p : ℕ}:
  @VarStoreSize.size p Unit instVarStoreSizeUnit = 0
:= rfl

-- set_option pp.all true in
@[grind =]
lemma instVarStoreSizeUnit_toLinear
  {p : ℕ}
  {varStore : VarStore p}
  {x : Unit}
:
  (@instVarStoreSizeUnit p).toLinear varStore x =
  @Vector.mk _ 0 #[] (by simp)
:= rfl

class Convert (p : ℕ) (representsT idealT : Type) extends IsValid p representsT where
  toIdeal : (VarStore p) → representsT → Option idealT
  toRepresents : idealT → representsT
  isValid_iff_isSome_toIdeal :
    ∀ (varStore : VarStore p) (x : representsT),
      isValid varStore x ↔ (toIdeal varStore x).isSome
  toIdeal_toRepresents :
    ∀ (varStore : VarStore p) (x : idealT),
      toIdeal varStore (toRepresents x) = .some x
  toRepresents_toIdeal :
    ∀ (varStore : VarStore p) (x : representsT),
      (h : isValid varStore x) →
        toIdeal varStore (toRepresents ((toIdeal varStore x).get ((isValid_iff_isSome_toIdeal varStore x).mp h))) =
        toIdeal varStore x

instance {p : ℕ} : Convert p Unit Unit where
  isValid := fun _ _ ↦ True
  toIdeal _ x := .some x
  toRepresents x := x
  isValid_iff_isSome_toIdeal _ _ := by grind
  toIdeal_toRepresents _ _ := by grind
  toRepresents_toIdeal _ _ _ := by grind

@[simp, grind .]
lemma isValid_iff_isSome_toIdeal {p} {α β : Type} [Convert p α β]
  {varStore : VarStore p} {x : α}
:
  (Convert.toIdeal (idealT := β) varStore x).isSome ↔
  IsValid.isValid varStore x
:= by
  aesop (add safe cases Convert)

@[grind .]
lemma isValid_of_toIdeal_eq_some {p} {α β : Type} [Convert p α β]
  {varStore : VarStore p} {x : α} {b : β}
  (h : (Convert.toIdeal (idealT := β) varStore x) = .some b)
:
  IsValid.isValid varStore x
:= by
  have := Option.isSome_of_eq_some h
  grind

@[simp, grind .]
lemma toIdealtoRepresents_of_convert {p} {α β : Type} [Convert p α β]
  {varStore : VarStore p} {x : β}
:
  Convert.toIdeal (representsT := α) varStore (Convert.toRepresents p x) = .some x
:= by
  aesop (add safe cases Convert)

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

instance (p : ℕ) {α} [IsValid p α] : IsValid p (Edsl.CircuitStateM p α) where
  isValid varStore x := ∀ numAlloc,
    IsValid.isValid varStore (x.getResult numAlloc) ∧
    [varStore,numAlloc|x.getCircuit numAlloc]ₑ.constraints

open Convert VarStoreSize Edsl in
def matchesUnaryMonadFunction (p : ℕ)
  {funIn funOut specIn specOut : Type}
  [Convert p funIn specIn] [Convert p funOut specOut]
  [VarStoreSize p funOut]
  (spec_function : specIn → specOut)
  (function : funIn → CircuitStateM p funOut)
  (allocatesN : ℕ)
  (constraints : specIn → Prop)
: Prop :=
  unaryFunctionResultIsValidIff p function ∧
  (∀ numAllocPre, unaryFunctionResultIsCorrect p spec_function (λ a => (function a).getResult numAllocPre)) ∧
  ∀ (a : funIn) (varStorePre : VarStore p) (numAllocPre : ℕ),
    (h : IsValid.isValid varStorePre a) →
      letI aVal : specIn := toIdeal varStorePre a |>.get ((Convert.isValid_iff_isSome_toIdeal _ _).mp h)
      let ⟨result, circuit⟩ : funOut × CircuitResult p :=
        CircuitStateM.runAndEval (function a) numAllocPre varStorePre
      let constraintsCorrect := circuit.constraints = (constraints aVal)
      let allocatesCorrect := circuit.numAlloc = numAllocPre + allocatesN
      let frameRule := ∀ n < numAllocPre, circuit.varStore[n]? = varStorePre[n]?
      letI linearRepr := toLinear circuit.varStore result
      let resultInVarStore := assertMatchesLast circuit.varStore circuit.numAlloc linearRepr
      constraintsCorrect ∧
      allocatesCorrect ∧
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
--   (function : funIn₁ → funIn₂ → CircuitStateM p funOut)
--   (allocatesN : ℕ)
--   (constraints : specIn₁ → specIn₂ → Prop)
-- : Prop :=
--   unaryFunctionResultIsValidIff p function ∧
--   (∀ numAllocPre, unaryFunctionResultIsCorrect p spec_function (λ a => (function a).getResult numAllocPre)) ∧
--   ∀ (a : funIn) (varStorePre : VarStore p) (numAllocPre : ℕ),
--     (h : IsValid.isValid varStorePre a) →
--       letI aVal : specIn := toIdeal varStorePre a |>.get ((Convert.isValid_iff_isSome_toIdeal _ _).mp h)
--       let ⟨result, circuit⟩ : funOut × CircuitResult p :=
--         CircuitStateM.runAndEval (function a) numAllocPre varStorePre
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
