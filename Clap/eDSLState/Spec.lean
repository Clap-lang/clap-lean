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
    [varStore,numAlloc|(x.getCircuit numAlloc)]ₑ.constraints

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
