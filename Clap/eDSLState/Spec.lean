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

class Convert (p : ℕ) (representsT idealT : Type) extends IsValid p representsT, VarStoreSize p representsT where
  toIdeal : (VarStore p) → representsT → Option idealT
  toRepresents : idealT → representsT
  someOfIsValid :
    ∀ (varStore : VarStore p) (x : representsT),
      isValid varStore x → (toIdeal varStore x).isSome
  toIdealtoRepresents :
    ∀ (varStore : VarStore p) (x : idealT),
      toIdeal varStore (toRepresents x) = .some x
  toRepresentstoIdeal :
    ∀ (varStore : VarStore p) (x : representsT),
      (h : isValid varStore x) →
        toIdeal varStore (toRepresents ((toIdeal varStore x).get (someOfIsValid varStore x h))) =
        toIdeal varStore x

def varStoreSize (p : ℕ) (α : Type) [φ : VarStoreSize p α] : ℕ := φ.size

@[grind .]
lemma someOfIsValid_of_convert {p} {α β : Type} [Convert p α β]
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
      letI aVal : specIn := toIdeal varStorePre a |>.get (someOfIsValid _ _ h)
      letI leftEval : Option specOut := toIdeal varStorePre (function a)
      letI wrapped : funOut := toRepresents p (spec_function aVal)
      leftEval = toIdeal varStorePre wrapped

def assertMatchesLast {k} {p}
  (varStore : VarStore p) (numAlloc : ℕ) (vec : Vector (ZMod p) k) : Prop :=
  ∀ i < k,
    letI varStoreIdx := numAlloc - k + i
    varStore[varStoreIdx]? = vec[i]?

open Convert VarStoreSize Edsl in
def matchesUnaryMonadFunction (p : ℕ)
  {funIn funOut specIn specOut : Type}
  [Convert p funIn specIn] [Convert p funOut specOut]
  (spec_function : specIn → specOut)
  (function : funIn → CircuitStateM p funOut)
  (allocatesN : ℕ)
  (constraints : Prop) : Prop :=
  ∀ (a : funIn) (varStorePre : VarStore p) (numAllocPre : ℕ),
    (h : IsValid.isValid varStorePre a) →
      letI aVal : specIn := toIdeal varStorePre a |>.get (someOfIsValid _ _ h)
      let ⟨result, circuit⟩ : funOut × CircuitResult p :=
        CircuitStateM.runAndEval (function a) numAllocPre varStorePre
      let resultIsValid := IsValid.isValid circuit.varStore result
      letI resultVal : Option specOut := toIdeal circuit.varStore result
      letI wrapped : funOut := toRepresents p (spec_function aVal)
      let resultCorrect := resultVal = toIdeal varStorePre wrapped
      let constraintsCorrect := circuit.constraints = constraints
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
