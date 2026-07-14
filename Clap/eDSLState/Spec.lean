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

open Convert Edsl in
def matchesBinaryPredicatePure (p : ℕ)
  {funInA funInB specInA specInB : Type}
  [Convert p funInA specInA] [Convert p funInB specInB]
  (spec_function : specInA → specInB → Prop)
  (function : funInA → funInB → CircuitStateM p Unit) : Prop :=
  ∀ (a : funInA) (b : funInB) (varStore : Std.ExtTreeMap ℕ (ZMod p)) (numAlloc : ℕ),
    (ha : IsValid.isValid varStore.get? a) → (hb : IsValid.isValid varStore.get? b) →
      letI aVal : specInA := toIdeal varStore.get? a |>.get (someOfIsValid _ _ ha)
      letI bVal : specInB := toIdeal varStore.get? b |>.get (someOfIsValid _ _ hb)
      let result : CircuitResult p :=
        CircuitState.eval ((function a b).run numAlloc).1.2 varStore numAlloc
      (result.constraints ↔ spec_function aVal bVal) ∧
      result.numAlloc = numAlloc ∧
      result.varStore = varStore

open Convert Edsl in
def matchesTernaryPredicatePure (p : ℕ)
  {funInA funInB funInC specInA specInB specInC : Type}
  [Convert p funInA specInA] [Convert p funInB specInB] [Convert p funInC specInC]
  (spec_function : specInA → specInB → specInC → Prop)
  (function : funInA → funInB → funInC → CircuitStateM p Unit) : Prop :=
  ∀ (a : funInA) (b : funInB) (c : funInC) (varStore : Std.ExtTreeMap ℕ (ZMod p)) (numAlloc : ℕ),
    (ha : IsValid.isValid varStore.get? a) → (hb : IsValid.isValid varStore.get? b) →
    (hc : IsValid.isValid varStore.get? c) →
      letI aVal : specInA := toIdeal varStore.get? a |>.get (someOfIsValid _ _ ha)
      letI bVal : specInB := toIdeal varStore.get? b |>.get (someOfIsValid _ _ hb)
      letI cVal : specInC := toIdeal varStore.get? c |>.get (someOfIsValid _ _ hc)
      let result : CircuitResult p :=
        CircuitState.eval ((function a b c).run numAlloc).1.2 varStore numAlloc
      (result.constraints ↔ spec_function aVal bVal cVal) ∧
      result.numAlloc = numAlloc ∧
      result.varStore = varStore

open Convert in
def matchesBinaryFunction (p : ℕ)
  {funInA funInB funOut specInA specInB specOut : Type}
  [Convert p funInA specInA] [Convert p funInB specInB] [Convert p funOut specOut]
  (spec_function : specInA → specInB → specOut)
  (function : funInA → funInB → funOut) : Prop :=
  ∀ (a : funInA) (b : funInB) (varStorePre : ℕ → Option (ZMod p)),
    (ha : IsValid.isValid varStorePre a) → (hb : IsValid.isValid varStorePre b) →
      letI aVal : specInA := toIdeal varStorePre a |>.get (someOfIsValid _ _ ha)
      letI bVal : specInB := toIdeal varStorePre b |>.get (someOfIsValid _ _ hb)
      letI leftEval : Option specOut := toIdeal varStorePre (function a b)
      letI wrapped : funOut := toRepresents p (spec_function aVal bVal)
      leftEval = toIdeal varStorePre wrapped

open Convert in
def matchesTernaryFunction (p : ℕ)
  {funInA funInB funInC funOut specInA specInB specInC specOut : Type}
  [Convert p funInA specInA] [Convert p funInB specInB] [Convert p funInC specInC]
  [Convert p funOut specOut]
  (spec_function : specInA → specInB → specInC → specOut)
  (function : funInA → funInB → funInC → funOut) : Prop :=
  ∀ (a : funInA) (b : funInB) (c : funInC) (varStorePre : ℕ → Option (ZMod p)),
    (ha : IsValid.isValid varStorePre a) → (hb : IsValid.isValid varStorePre b) →
    (hc : IsValid.isValid varStorePre c) →
      letI aVal : specInA := toIdeal varStorePre a |>.get (someOfIsValid _ _ ha)
      letI bVal : specInB := toIdeal varStorePre b |>.get (someOfIsValid _ _ hb)
      letI cVal : specInC := toIdeal varStorePre c |>.get (someOfIsValid _ _ hc)
      letI leftEval : Option specOut := toIdeal varStorePre (function a b c)
      letI wrapped : funOut := toRepresents p (spec_function aVal bVal cVal)
      leftEval = toIdeal varStorePre wrapped

-- From OneHotRaw

attribute [local grind _=_] Array.toList_mapM Vector.toArray_mapM
attribute [local grind =] Vector.map_id_fun Vector.map_id ZMod.val_natCast
attribute [local grind .] Vector.mem_toArray_iff

@[grind _=_]
lemma Vector_isSome_mapM_eq_all_isSome
  {elemT resultT} {length} {f : elemT → Option resultT} {xs : Vector elemT length} :
  (Vector.mapM f xs).isSome = (xs.map f).all Option.isSome := by
  have :
    (Vector.mapM f xs).isSome =
    (Vector.toArray <$> (Vector.mapM f xs)).isSome := by grind
  rewrite [this]; clear this
  simp
  rewrite [Array.mapM_eq_mapM_toList]
  have : xs.toArray.toList = xs.toList := rfl
  rewrite [this]; clear this
  have :
    (xs.all λ a => (f a).isSome) =
    xs.toList.all fun a => (f a).isSome := by
    rw [←Vector.all_toList]
  rewrite [this]; clear this
  induction xs.toList with
  | nil => simp
  | cons head tail h_tail =>
    simp
    cases (f head) with
    | none => simp
    | some head =>
      rewrite [←h_tail]
      simp
      cases (List.mapM f tail) with
      | none => grind
      | some rest => grind

@[grind =_]
lemma toIdeal_eq_pure_get_of_isValid {p} {representsT idealT}
  {varStore : ℕ → Option (ZMod p)} {x : representsT}
  [Convert p representsT idealT] (h : IsValid.isValid varStore x) :
  Convert.toIdeal varStore x = pure ((Convert.toIdeal varStore x).get (Convert.someOfIsValid varStore x h)) := by
  simp

@[grind =]
lemma List_mapM_toRepresentstoIdeal {p} {representsT idealT}
  {varStore : ℕ → Option (ZMod p)} {xs : List representsT}
  [base : Convert p representsT idealT] {h} :
  List.mapM (base.toIdeal varStore ∘ base.toRepresents) ((List.mapM (Convert.toIdeal varStore) xs).get h) =
  List.mapM (Convert.toIdeal varStore) xs := by
  induction xs with
  | nil => simp
  | cons head tail h_tail =>
    simp [h_tail, base.toIdealtoRepresents]

@[grind .]
lemma List_isSome_mapM_of_isSome
  {T T'} {list : List T} {f : T → Option T'} (h : ∀ x ∈ list, (f x).isSome) :
  (List.mapM f list).isSome := by
  induction list with
  | nil => simp
  | cons head tail h_tail =>
    have h_head := h head (by simp)
    obtain ⟨head, h_head⟩ := Option.isSome_iff_exists.mp h_head
    simp [h_head]
    simp_all
    obtain ⟨tail, h_tail⟩ := Option.isSome_iff_exists.mp h_tail
    simp [h_tail]

instance {p} {representsT idealT length} [base : Convert p representsT idealT] :
  Convert p (Vector representsT length) (Vector idealT length) where
  isValid varStore xs :=
    ∀ x ∈ xs, base.isValid varStore x
  size := length * base.size
  toLinear varStore xs :=
    xs.flatMap (base.toLinear varStore)
  toIdeal varStore xs :=
    let ideals := xs.map (base.toIdeal varStore)
    ideals.mapM id
  toRepresents xs :=
    xs.map base.toRepresents
  someOfIsValid varStore x h_isValid := by
    grind
  toIdealtoRepresents varStore xs := by
    simp only [Function.comp_def, Vector.mapM_map]
    have := Vector.mapM_pure (m := Option) (xs := xs) (id : idealT → idealT)
    grind
  toRepresentstoIdeal varStore xs h := by
    simp
    rewrite [←Vector.map_toArray_inj, ←Array.map_toList_inj]
    simp
    have (h : (Vector.mapM (Convert.toIdeal varStore) xs).isSome) (h') :
      ((Vector.mapM (base.toIdeal varStore) xs).get h).toArray.toList =
      (Array.toList <$> Vector.toArray <$> (Vector.mapM (base.toIdeal varStore) xs)).get h' := by
      grind
    grind

end Clap
