import Clap.Lang.F.F

namespace Clap.Edsl.Lang

abbrev FB p := F p

namespace FB

def true (p : ℕ) [Fact (p ≥ 2)] : FB p := .c 1
def false (p : ℕ) [Fact (p ≥ 2)] : FB p := .c 0

variable {p : ℕ} [Fact (p ≥ 2)]

def isValid (x : FB p) (varStore : ℕ → Option (ZMod p)) : Prop :=
  x.eval varStore = .some 0 ∨
  x.eval varStore = .some 1

def isAlwaysValid (x : FB p) : Prop :=
  ∀ varStore, x.isValid varStore

def toBool (x : FB p) (varStore : ℕ → Option (ZMod p)) : Bool :=
  x.eval varStore == .some 1

def ofBool (p : ℕ) [Fact (p ≥ 2)] (x : Bool) : FB p :=
  if x then FB.true p else FB.false p

@[simp, grind .] -- TODO(provisional `simp`)
lemma eval_ofBool_toBool_of_isValid
  {p : ℕ}
  {varStore : ℕ → Option (ZMod p)}
  (f: FB p)
  (h : f.isValid varStore)
  [Fact (p ≥ 2)]
:
  (FB.ofBool p (f.toBool varStore)).eval varStore = f.eval varStore
:= by
  aesop (add simp [toBool,FB.ofBool,FB.isValid])

@[simp, grind =]
lemma toBool_ofBool
  {p : ℕ}
  {varStore : ℕ → Option (ZMod p)}
  (b: Bool)
  [Fact (p ≥ 2)]
:
  (FB.ofBool p b).toBool varStore = b
:= by
  aesop (add simp [toBool,FB.ofBool,FB.true,FB.false])

namespace ofBool

lemma isAlwaysValid (b:Bool) : isAlwaysValid (FB.ofBool p b) := by
  unfold FB.isAlwaysValid isValid FB.ofBool
  aesop

lemma equiv (varStore) (b) : FixedExp.eval varStore (ofBool p b) =
  if b then .some 1 else .some 0
:= by
  simp [ofBool]
  cases b
  all_goals simp [FB.false, FB.true]

end ofBool

abbrev withΓ (p : ℕ) (α ω : Type) := (ℕ → Option (ZMod p)) → α → ω

class IsValid (p : ℕ) (α : Type) where
  isValid : withΓ p α Prop

def Result (p : ℕ) (α : Type) := α × CircuitResult p

def Result.isPure (result : Result p (ZMod p)) := result.2 = default

/--
`eval` is allowed to depend on `numAlloc`
-/
class Eval (p : ℕ) (α : Type) (β : outParam Type) where
  eval : ℕ → withΓ p α (Result p β)

instance : Eval p (FB p) (ZMod p) := ⟨fun _numAlloc Γ x ↦ ⟨x.eval Γ |>.getD 0, default⟩⟩

class VarStoreSize (p : ℕ) (α : Type) where
  size : ℕ
  toLinear : (ℕ → Option (ZMod p)) → α → Vector (ZMod p) size

class Convert (p : ℕ) (representsT idealT : Type) extends IsValid p representsT, VarStoreSize p representsT where
  toIdeal : (ℕ → Option (ZMod p)) → representsT → Option idealT
  toRepresents : idealT → representsT
  someOfIsValid :
    ∀ (varStore : ℕ → Option (ZMod p)) (x : representsT),
      isValid varStore x → (toIdeal varStore x).isSome
  toIdealtoRepresents :
    ∀ (varStore : ℕ → Option (ZMod p)) (x : idealT),
      toIdeal varStore (toRepresents x) = .some x
  toRepresentstoIdeal :
    ∀ (varStore : ℕ → Option (ZMod p)) (x : representsT),
      (h : isValid varStore x) →
        toIdeal varStore (toRepresents ((toIdeal varStore x).get (someOfIsValid varStore x h))) =
        toIdeal varStore x

def varStoreSize (p : ℕ) (α : Type) [φ : VarStoreSize p α] : ℕ := φ.size

@[grind .]
lemma someOfIsValid_of_convert {p} {α β : Type} [Convert p α β]
  {varStore : ℕ → Option (ZMod p)} {x : α} (h : FB.IsValid.isValid varStore x) :
  (Convert.toIdeal (idealT := β) varStore x).isSome := by
  aesop (add safe cases Convert)

@[grind .]
lemma toIdealtoRepresents_of_convert {p} {α β : Type} [Convert p α β]
  {varStore : ℕ → Option (ZMod p)} {x : β} :
  Convert.toIdeal (representsT := α) varStore (Convert.toRepresents p x) = .some x := by
  aesop (add safe cases Convert)

instance : IsValid p (FB p) := ⟨fun Γ a ↦ FB.isValid a Γ⟩

instance {p} : VarStoreSize p (FB p) where
  size := 1
  toLinear varStore x := #v[x.eval varStore |>.getD 42]

instance : Convert p (FB p) Bool where
  toIdeal Γ x := .some (FB.toBool x Γ)
  toRepresents := FB.ofBool p
  someOfIsValid := by simp
  toIdealtoRepresents := by simp
  toRepresentstoIdeal := by simp

-- class ΓConsistent (α : Type) where
--   Γconsistent : ℕ → Prop

-- instance : ΓConsistent (FB )

-- def matchesUnaryBitVecFunctionWithSideEffects
--   {length: ℕ}
--   (p : ℕ)
--   [Fact (p ≥ 2)]
--   (spec_function : (ZMod p) → Vector Bool length)
--   (function : (F p) → Edsl.CircuitStateM p (Vector (FB p) length))
--   (allocates : ℕ)
-- : Prop :=
--   ∀ (a : F p) varStorePre numAllocPre,
--   a.isValid (varStorePre.get?) →
--   let a_eval := (a.eval varStorePre.get?).getD 0
--   let ⟨result, numAllocPost, varStorePost, constraints⟩ := runAndEval (function a) numAllocPre varStorePre
--   result.map (FB.toBool · varStorePost.get?) = spec_function a_eval ∧
--   constraints = True ∧
--   numAllocPost = numAllocPre + allocates ∧
--   ∀ i < numAllocPre, varStorePost.get? i = varStorePre.get? i ∧
--   ∀ (i: Fin length),
--     varStorePost.get? (numAllocPost - i) =
--     .some (((spec_function a_eval).get ⟨length - 1 - i, by {
--       omega
--     }⟩).toNat)

open Convert in
def matchesUnaryFunction (p : ℕ)
  {funIn funOut specIn specOut : Type}
  [Convert p funIn specIn] [Convert p funOut specOut]
  (spec_function : specIn → specOut)
  (function : funIn → funOut) : Prop :=
  ∀ (a : funIn) (varStorePre : ℕ → Option (ZMod p)),
    (h : IsValid.isValid varStorePre a) →
      letI aVal : specIn := toIdeal varStorePre a |>.get (someOfIsValid _ _ h)
      letI leftEval : Option specOut := toIdeal varStorePre (function a)
      letI wrapped : funOut := toRepresents p (spec_function aVal)
      leftEval = toIdeal varStorePre wrapped

def assertMatchesLast {k} (varStore : ℕ → Option (ZMod p)) (numAlloc : ℕ) (vec : Vector (ZMod p) k) : Prop :=
  ∀ i < k,
    letI varStoreIdx := numAlloc - k + i
    varStore varStoreIdx = vec[i]?

open Convert VarStoreSize in
def matchesUnaryMonadFunction (p : ℕ)
  {funIn funOut specIn specOut : Type}
  [Convert p funIn specIn] [Convert p funOut specOut]
  (spec_function : specIn → specOut)
  (function : funIn → CircuitStateM p funOut)
  (allocatesN : ℕ)
  (constraints : Prop) : Prop :=
  ∀ (a : funIn) (varStorePre : Std.ExtTreeMap ℕ (ZMod p)) (numAllocPre : ℕ),
    (h : IsValid.isValid varStorePre.get? a) →
      letI aVal : specIn := toIdeal varStorePre.get? a |>.get (someOfIsValid _ _ h)
      let ⟨result, circuit⟩ : funOut × CircuitResult p :=
        CircuitStateM.runAndEval (function a) numAllocPre varStorePre
      let resultIsValid := IsValid.isValid circuit.varStore.get? result
      letI resultVal : Option specOut := toIdeal circuit.varStore.get? result
      letI wrapped : funOut := toRepresents p (spec_function aVal)
      let resultCorrect := resultVal = toIdeal varStorePre.get? wrapped
      let constraintsCorrect := circuit.constraints = constraints
      let allocatesCorrect := circuit.numAlloc = numAllocPre + allocatesN
      let frameRule := ∀ n < numAllocPre, circuit.varStore[n]? = varStorePre[n]?
      letI resultSize : ℕ := varStoreSize p funOut
      letI linearRepr := toLinear circuit.varStore.get? result
      let resultInVarStore := assertMatchesLast circuit.varStore.get? circuit.numAlloc linearRepr
      resultIsValid ∧
      resultCorrect ∧
      constraintsCorrect ∧
      allocatesCorrect ∧
      frameRule ∧
      resultInVarStore

end FB

end Clap.Edsl.Lang
