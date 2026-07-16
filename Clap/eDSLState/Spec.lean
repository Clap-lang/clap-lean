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

instance {p : ℕ} {α} [VarStoreSize p α] : Convert p α α where
  isValid := fun _ _ ↦ True
  toIdeal _ x := .some x
  toRepresents x := x
  isValid_iff_isSome_toIdeal _ _ := by grind
  toIdeal_toRepresents _ _ := by grind
  toRepresents_toIdeal _ _ _ := by grind

@[grind .]
lemma isValid_iff_isSome_toIdeal_of_convert {p} {α β : Type} [Convert p α β]
  {varStore : VarStore p} {x : α} (h : IsValid.isValid varStore x) :
  (Convert.toIdeal (idealT := β) varStore x).isSome := by
  aesop (add safe cases Convert)

@[grind .]
lemma toIdealtoRepresents_of_convert {p} {α β : Type} [Convert p α β]
  {varStore : VarStore p} {x : β} :
  Convert.toIdeal (representsT := α) varStore (Convert.toRepresents p x) = .some x := by
  aesop (add safe cases Convert)

open Convert in
def matchesUnaryFunction (p : ℕ)
  {funIn funOut specIn specOut : Type}
  [Convert p funIn specIn] [Convert p funOut specOut]
  (spec_function : specIn → specOut)
  (function : funIn → funOut) : Prop :=
  ∀ (a : funIn) (varStorePre : VarStore p),
    (h : IsValid.isValid varStorePre a) →
      letI aVal : specIn := toIdeal varStorePre a |>.get ((isValid_iff_isSome_toIdeal _ _).mp h)
      letI resultVal : Option specOut := toIdeal varStorePre (function a)
      letI wrapped : funOut := toRepresents p (spec_function aVal)
      resultVal = toIdeal varStorePre wrapped

open Convert in
def matchesBinaryFunction (p : ℕ)
  {funIn funOut specIn specOut : Type}
  [Convert p funIn specIn] [Convert p funOut specOut]
  (spec_function : specIn → specIn → specOut)
  (function : funIn → funIn → funOut) : Prop :=
  ∀ (a b : funIn) (varStorePre : VarStore p),
    (h₁ : IsValid.isValid varStorePre a) →
    (h₂ : IsValid.isValid varStorePre b) →
      letI aVal : specIn :=
        toIdeal varStorePre a |>.get ((isValid_iff_isSome_toIdeal _ _).mp h₁)
      letI bVal : specIn :=
        toIdeal varStorePre b |>.get ((isValid_iff_isSome_toIdeal _ _).mp h₂)
      letI resultVal : Option specOut := toIdeal varStorePre (function a b)
      letI wrapped : funOut := toRepresents p (spec_function aVal bVal)
      resultVal = toIdeal varStorePre wrapped

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
  unfold matchesUnaryFunction at h_equiv
  specialize h_equiv a varStore h_isValid
  apply (inst_out.isValid_iff_isSome_toIdeal varStore (function a)).mpr
  grind

def assertMatchesLast {k} {p}
  (varStore : VarStore p) (numAlloc : ℕ) (vec : Vector (ZMod p) k) : Prop :=
  ∀ i < k,
    letI varStoreIdx := numAlloc - k + i
    varStore[varStoreIdx]? = vec[i]?

/-
Generalised the `Unit → Unit` `Convert` instance to `α → α`.
Removed `VarStoreSize` from `Convert`, it doesn't belong in there. Nothing from the class
needs its axioms, it's only subsequent defs. This furthermore loosens the requirements on
specs, because now we only need `VarStoreSize` on `funOut`, whereas before, it was also on `specOut`.
-/

open Convert VarStoreSize Edsl in
def matchesUnaryMonadFunction (p : ℕ)
  {funIn funOut specIn specOut : Type}
  [Convert p funIn specIn] [Convert p funOut specOut]
  [VarStoreSize p funOut]
  (spec_function : specIn → specOut)
  (function : funIn → CircuitStateM p funOut)
  (allocatesN : ℕ)
  (constraints : specIn → Prop) : Prop :=
  ∀ (a : funIn) (varStorePre : VarStore p) (numAllocPre : ℕ),
    (h : IsValid.isValid varStorePre a) →
      letI aVal : specIn := toIdeal varStorePre a |>.get ((isValid_iff_isSome_toIdeal _ _).mp h)
      let ⟨result, circuit⟩ : funOut × CircuitResult p :=
        CircuitStateM.runAndEval (function a) numAllocPre varStorePre
      let resultIsValid := IsValid.isValid circuit.varStore result
      letI resultVal : Option specOut := toIdeal circuit.varStore result
      letI wrapped : funOut := toRepresents p (spec_function aVal)
      let resultCorrect := resultVal = toIdeal varStorePre wrapped
      let constraintsCorrect := circuit.constraints = (constraints aVal)
      let allocatesCorrect := circuit.numAlloc = numAllocPre + allocatesN
      let frameRule := ∀ n < numAllocPre, circuit.varStore[n]? = varStorePre[n]?
      letI linearRepr := toLinear circuit.varStore result
      let resultInVarStore := assertMatchesLast circuit.varStore circuit.numAlloc linearRepr
      resultIsValid ∧
      resultCorrect ∧
      constraintsCorrect ∧
      allocatesCorrect ∧
      frameRule ∧
      resultInVarStore

end Clap
