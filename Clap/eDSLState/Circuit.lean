import Mathlib.Control.Monad.Writer

import Clap.eDSLState.HashCons.CacheExpr
import Clap.eDSLState.HashCons.EvalButActuallyGood
import Clap.eDSLState.Varstore

namespace Clap

@[grind cases]
inductive CircuitusPlanus (p : ℕ) where
  | eq0 (e : ExprRef)
  | lam
  | share (e : ExprRef)
  | isZero (e : ExprRef)
  | num2bits (w : ℕ) (e : ExprRef)

def CircuitusPlanus.refsValid {p : ℕ} (c : CircuitusPlanus p) (bound : ℕ) : Prop := match c with
  | .eq0 e => e < bound
  | .lam => True
  | .share e => e < bound
  | .isZero e => e < bound
  | .num2bits _w e => e < bound

def CircuitusPlanus.varsAllocated {p : ℕ} (c : CircuitusPlanus p) (varStore : VarStore p) (σ : HashConsSt p) : Prop := match c with
    | .eq0 e => [varStore, σ|e].isSome
    | .lam => True
    | .share e => [varStore, σ|e].isSome
    | .isZero e => [varStore, σ|e].isSome
    | .num2bits _w e => [varStore, σ|e].isSome

instance {p: ℕ} {x : CircuitusPlanus p} {bound : ℕ}: Decidable (x.refsValid bound) := match x with
  | .eq0 e => e.decLt bound
  | .lam => .isTrue (by trivial)
  | .share e => e.decLt bound
  | .isZero e => e.decLt bound
  | .num2bits _w e => e.decLt bound


abbrev CircuitState (p : ℕ) := Array (CircuitusPlanus p)

def CircuitState.refsValid {p : ℕ} (c : CircuitState p) (bound : ℕ) : Prop :=
  c.all λ x => (decide (x.refsValid bound))

-- TODO decidable?
def CircuitState.varsAllocated {p : ℕ} (c : CircuitState p) (varStore : VarStore p) (σ : HashConsSt p) : Prop :=
  ∀ x ∈ c, x.varsAllocated varStore σ

-- isZero : input → Bool
-- need to allocate the output of this thing
-- the input is index 0, the output is index 1
-- this becomes 2x eq0 (this needs an auxiliary thing, the inverse or some such)
-- thus, wire 0 maps to 0 when you go down to cs
-- 1 maps to 2, and the inverse becomes 1
-- this 'invalidates' the mapping between input | output (careful)
-- this shift is statically known (we know that isZero will need an extra thing -
-- as such, we can already bump by two, if we so desire - thus, we'll keep 1:1 mapping between input|output)

namespace Edsl

structure CircuitResult (p : ℕ) where
  numAlloc : ℕ
  varStore : VarStore p
  constraints : Prop
  deriving Inhabited

namespace CircuitResult

section

-- TODO do we need all of these?
variable {p k numAlloc : ℕ} {result result' : CircuitResult p}
         {constraint : Prop} {vars : Vector (ZMod p) k} {e : HashConsM p ExprRef}
         {varStore : VarStore p}
         {σ : HashConsSt p}

def init (p : ℕ) : CircuitResult p := ⟨0, ∅, True⟩

def unconstrained (numAlloc : ℕ) (varStore : VarStore p) : CircuitResult p :=
  ⟨numAlloc, varStore, True⟩

notation (name := notationα) "unconstrained[" numAlloc:arg "]" "[" varStore:arg "]" => unconstrained numAlloc varStore

recommended_spelling "unconstrained" for "α" in [unconstrained, notationα]

@[simp, grind =]
lemma numAlloc_unconstrained : unconstrained[numAlloc][varStore].numAlloc = numAlloc := rfl

@[simp, grind =]
lemma varStore_unconstrained : unconstrained[numAlloc][varStore].varStore = varStore := rfl

@[simp, grind =]
lemma constraints_unconstrained : unconstrained[numAlloc][varStore].constraints = True := rfl

def addConstraint (result : CircuitResult p) (constraint : Prop) : CircuitResult p :=
  {result with constraints := result.constraints ∧ constraint}

@[simp, grind =]
lemma addConstraint_mk
  (numAlloc : ℕ)
  (varStore : VarStore p)
  (constraints constraint : Prop)
:
  (Edsl.CircuitResult.mk numAlloc varStore constraints).addConstraint constraint =
  Edsl.CircuitResult.mk numAlloc varStore (constraints ∧ constraint)
:= rfl

-- @[simp, grind =]
lemma addConstraint_unconstrained {constraint : Prop} :
  unconstrained[numAlloc][varStore].addConstraint constraint =
  ⟨numAlloc, varStore, constraint⟩ := by simp [unconstrained]

@[simp, grind =]
lemma numAlloc_addConstraint : (result.addConstraint constraint).numAlloc = result.numAlloc := rfl

@[simp, grind =]
lemma varStore_addConstraint : (result.addConstraint constraint).varStore = result.varStore := rfl

@[simp, grind =]
lemma constraints_addConstraint : (result.addConstraint constraint).constraints =
                                  (result.constraints ∧ constraint) := rfl

def allocAnonymous (result : CircuitResult p) : CircuitResult p :=
  {result with numAlloc := result.numAlloc + 1}

-- @[simp, grind =]
-- lemma allocAnonymous_mk
--   (numAlloc : ℕ)
--   (varStore : VarStore p)
--   (constraints : Prop)
-- :
--   (Edsl.CircuitResult.mk numAlloc varStore constraints).allocAnonymous =
--   Edsl.CircuitResult.mk (numAlloc + 1) varStore constraints
-- := rfl

-- @[simp, grind =]
-- lemma allocAnonymous_unconstrained :
--   unconstrained[numAlloc][varStore].allocAnonymous =
--   ⟨numAlloc + 1, varStore, True⟩ := by rfl

-- @[simp, grind =]
-- lemma numAlloc_allocAnonymous : result.allocAnonymous.numAlloc = result.numAlloc + 1 := rfl

-- @[simp, grind =]
-- lemma varStore_allocAnonymous : result.allocAnonymous.varStore = result.varStore := rfl

-- @[simp, grind =]
-- lemma constraints_allocAnonymous : result.allocAnonymous.constraints = result.constraints := rfl

@[grind =]
def get? (result : CircuitResult p) (e : ExprRef) (σ : HashConsSt p): (Option (ZMod p)) := do
  HashConsM.eval result.varStore e σ

@[grind =]
def getM? (result : CircuitResult p) (e : HashConsM p ExprRef) : HashConsM p (Option (ZMod p)) := do
  HashConsM.evalM result.varStore e

-- instance : Membership (HashConsM p ExprRef) (HashConsM p (CircuitResult p)) :=
--   ⟨fun Γ x ↦ (get? Γ x).isSome⟩

-- instance : GetElem (CircuitResult p) (CacheExpr p) (ZMod p) (fun Γ x ↦ x ∈ Γ) :=
--   ⟨fun Γ x h ↦ Γ.get? x |>.get h⟩

@[simp, grind =]
lemma get?_mk
  {varStore : VarStore p}
  {e : ExprRef}
  (numAlloc : ℕ)
  (constraints : Prop)
:
  (Edsl.CircuitResult.mk numAlloc varStore constraints).get? e σ =
  [varStore,σ|e]
:= rfl

@[simp, grind =]
lemma getM?_mk
  {varStore : VarStore p}
  {e : HashConsM p ExprRef}
  (numAlloc : ℕ)
  (constraints : Prop)
:
  ((Edsl.CircuitResult.mk numAlloc varStore constraints).getM? e).run σ =
  [varStore,σ|←e]
:= rfl

@[grind =>]
lemma getM?_of_varStore_eq_varStore (h : result.varStore = result'.varStore) : result.getM? e = result'.getM? e := by
  simp_all [CircuitResult.getM?]

def getD (result : CircuitResult p) (e : ExprRef) (σ : HashConsSt p) : ZMod p :=
  (result.get? e σ).getD (dflt := 0)

def getDM (result : CircuitResult p) (e : HashConsM p ExprRef) : HashConsM p (ZMod p) := do
  result.getM? e <&> Option.getD (dflt := 0)

-- instance {p} : GetElem? (CircuitResult p) (HashConsM p ExprRef) (ZMod p) (fun Γ x ↦ x ∈ Γ) :=
--   ⟨get?, getD⟩

@[simp, grind =]
lemma getD_eq_getM?_getD {e : ExprRef} : result.getD e σ = (result.get? e σ).getD (dflt := 0) := rfl

@[simp, grind =]
lemma getDM_eq_getM?_getD : result.getDM e = result.getM? e <&> Option.getD (dflt := 0) := rfl

@[simp, grind =]
lemma getM?_unconstrained:
  (unconstrained[numAlloc][varStore].getM? e).run σ =
  [varStore,σ|←e] := by simp [unconstrained]

-- Asserts that the expression that e points to does not use any variables that aren't in the varStore
-- Panics if e is outside of σ
def assertAllocated (result : CircuitResult p) (e : ExprRef) (σ : HashConsSt p) : CircuitResult p :=
  let val := result.get? e σ
  result.addConstraint val.isSome

def assertAllocatedM (result : CircuitResult p) (e : HashConsM p ExprRef) : HashConsM p (CircuitResult p) := do
  let val ← result.getM? e
  return result.addConstraint val.isSome

@[simp, grind =]
lemma assertAllocated_mk
  (e : ExprRef)
  (numAlloc : ℕ)
  (varStore : VarStore p)
  (constraints : Prop)
:
  (Edsl.CircuitResult.mk numAlloc varStore constraints).assertAllocated e σ =
  Edsl.CircuitResult.mk
    numAlloc
    varStore
    (constraints ∧ [varStore,σ|e].isSome = true)
:= rfl

@[simp, grind =]
lemma assertAllocatedM_mk
  (e : HashConsM p ExprRef)
  (numAlloc : ℕ)
  (varStore : VarStore p)
  (constraints : Prop)
:
  ((Edsl.CircuitResult.mk numAlloc varStore constraints).assertAllocatedM e).run σ =
  (
    Edsl.CircuitResult.mk
      numAlloc
      varStore
      (constraints ∧ [varStore,σ|←e].1.isSome = true)
    ,
    [varStore,σ|←e].2
  )
:= rfl


-- @[simp, grind =]
-- lemma numAlloc_assertAllocated :
--   (result.assertAllocated e).numAlloc = result.numAlloc := rfl

-- @[simp, grind =]
-- lemma varStore_assertAllocated :
--   (result.assertAllocated e).varStore = result.varStore := rfl

-- @[simp, grind =]
-- lemma constraints_assertAllocated :
--   (result.assertAllocated e).constraints = (result.constraints ∧ (result.get? e).isSome = true) := rfl

-- @[simp, grind =]
-- lemma assertAllocated_unconstrained :
--   unconstrained[numAlloc][varStore].assertAllocated e =
--   letI α := unconstrained[numAlloc][varStore]
--   α.addConstraint (e ∈ α) := rfl

def alloc {k p : ℕ} (result : CircuitResult p) (vals : Vector (ZMod p) k) : CircuitResult p :=
  let indexed := (Vector.range k).map (·+result.numAlloc) |>.zip vals
  let varStore := result.varStore.insertMany indexed
  {result with varStore := varStore, numAlloc := result.numAlloc + k}

@[simp, grind =]
lemma alloc_mk
  (vals : Vector (ZMod p) k)
  (numAlloc : ℕ)
  (varStore : VarStore p)
  (constraints : Prop)
:
  (Edsl.CircuitResult.mk numAlloc varStore constraints).alloc vals =
  Edsl.CircuitResult.mk
    (numAlloc + k)
    (varStore.insertMany ((Vector.range k).map (·+numAlloc) |>.zip vals))
    constraints
:= rfl

@[simp, grind =]
lemma numAlloc_alloc {vars : Vector (ZMod p) k} :
  (result.alloc vars).numAlloc = result.numAlloc + k := rfl

@[simp, grind =]
lemma varStore_alloc {vars : Vector (ZMod p) k} :
  (result.alloc vars).varStore =
  result.varStore.insertMany ((Vector.range k).map (·+result.numAlloc) |>.zip vars) := rfl

@[simp, grind =]
lemma constraints_alloc {vars : Vector (ZMod p) k} :
  (result.alloc vars).constraints = result.constraints := rfl

def step (result : CircuitResult p) (next : CircuitusPlanus p) (σ : HashConsSt p) :CircuitResult p :=
  -- dbg_trace s!"running: {repr next}"
  match next with
  | .eq0 e =>
    let x := result.get? e σ
    result.addConstraint (x = .some 0)
  | .lam => result.allocAnonymous
  | .share e =>
    (result.assertAllocated e σ).alloc #v[result.getD e σ]
  | .isZero e =>
    (result.assertAllocated e σ).alloc #v[if (result.get? e σ) = .some 0 then 1 else 0]
  | .num2bits width e =>
    (result.assertAllocated e σ).alloc (num2bitsLsbPureV width (result.getD e σ))

-- notation "[" σ "|" cmd "]ₛ" => step σ cmd

-- -- TODO do we want to make individual functions for these parts and prove properties about them
-- @[simp, grind =]
-- lemma step_mk
--   (numAlloc : ℕ)
--   (varStore : VarStore p)
--   (constraints : Prop)
--   (next : CircuitusPlanus p)
-- : (Edsl.CircuitResult.mk numAlloc varStore constraints).step next =
--   Edsl.CircuitResult.mk
--     (match next with
--       | .eq0 _ => numAlloc
--       | .lam => numAlloc + 1
--       | .share e => numAlloc + 1
--       | .isZero e => numAlloc + 1
--       | .num2bits width _ => numAlloc + width
--     )
--     (match next with
--       | .eq0 _ => varStore
--       | .lam => varStore
--       | .share e => varStore.insert numAlloc ((e.eval varStore).getD 0)
--       | .isZero e => varStore.insert numAlloc (if (e.eval varStore) = .some 0 then 1 else 0)
--       | .num2bits width e => varStore.insertMany
--         ((Vector.map (fun x => x + numAlloc) (Vector.range width)).zip
--           (num2bitsLsbPureV width ((FixedExp.eval varStore e).getD 0)))
--     )
--     (match next with
--       | .eq0 e => constraints ∧ (e.eval varStore) = .some 0
--       | .lam => constraints
--       | .share e => constraints ∧ (e.eval varStore).isSome
--       | .isZero e => constraints ∧ (e.eval varStore).isSome
--       | .num2bits width e => constraints ∧ (e.eval varStore).isSome
--     )
-- := by
--   sorry
--   -- cases next <;> simp [CircuitResult.step, Membership.mem]
--   -- rfl

-- -- @[simp, grind =]
-- lemma step_unconstrained {command : CircuitusPlanus p} :
--   [unconstrained[numAlloc][varStore]|command]ₛ =
--   [⟨numAlloc, varStore, True⟩|command]ₛ := rfl

-- def split (result : CircuitResult p) : CircuitResult p :=
--   {result with constraints := True}

-- @[simp, grind =]
-- lemma numAlloc_split : result.split.numAlloc = result.numAlloc := rfl

-- @[simp, grind =]
-- lemma varStore_split : result.split.varStore = result.varStore := rfl

-- @[simp, grind =]
-- lemma constraints_split : result.split.constraints = True := rfl

-- section

-- variable {p width : ℕ} {result : CircuitResult p} {e : FixedExp p}

-- @[simp, grind =]
-- lemma step_eq0 :
--   [result|.eq0 e]ₛ = result.addConstraint (result[e]? = .some 0) := rfl

-- @[simp, grind =]
-- lemma step_lam :
--   [result|.lam]ₛ = result.allocAnonymous := rfl

-- @[simp, grind =]
-- lemma step_share :
--   [result|.share e]ₛ = (result.assertAllocated e |>.alloc #v[result.getD e]) := rfl

-- @[simp, grind =]
-- lemma step_isZero :
--   [result|.isZero e]ₛ = (result.assertAllocated e |>.alloc #v[if result[e]? = .some 0 then 1 else 0]) := rfl

-- @[simp, grind =]
-- lemma step_num2bits :
--   [result|.num2bits width e]ₛ = (result.assertAllocated e |>.alloc (num2bitsLsbPureV width result[e]!)) := rfl

-- lemma addConstraint_eq_mk :
--   result.addConstraint constraint =
--   ⟨result.numAlloc, result.varStore, result.constraints ∧ constraint⟩ := rfl

-- lemma allocAnonymous_eq_mk :
--   result.allocAnonymous =
--   ⟨result.numAlloc + 1, result.varStore, result.constraints⟩ := rfl

-- lemma alloc_eq_mk {k} {vals : Vector _ k} :
--   result.alloc vals =
--   ⟨result.numAlloc + k,
--    result.varStore.insertMany (((Vector.range k).map (· + result.numAlloc)).zip vals),
--    result.constraints⟩ := by rfl

-- lemma assertAllocated_eq_addConstraint :
--   result.assertAllocated e = result.addConstraint (e ∈ result) := rfl

-- end

end

end CircuitResult

abbrev CircuitState.evalInOrder {p : ℕ} (circuit : CircuitState p) (σ : HashConsSt p) := circuit.foldl (CircuitResult.step (σ := σ))

def CircuitState.eval {p : ℕ} (circuit : CircuitState p) (varStore : VarStore p) (numAlloc : ℕ) (σ : HashConsSt p) : CircuitResult p :=
  CircuitState.evalInOrder circuit σ ⟨numAlloc, varStore, True⟩

-- notation "[" varStore ", " numAlloc "|" circuit "]ₑ" => CircuitState.eval circuit varStore numAlloc

namespace CircuitResult

variable {p : ℕ} {σ : HashConsSt p}

@[ext, grind ext]
lemma ext {p : ℕ} {r1 r2 : CircuitResult p}
  (h_numAlloc : r1.numAlloc = r2.numAlloc)
  (h_varStore : r1.varStore = r2.varStore)
  (h_constraints : r1.constraints = r2.constraints)
:
  r1 = r2
:= by
  obtain ⟨a1, b1, c1⟩ := r1
  obtain ⟨a2, b2, c2⟩ := r2
  simp_all

lemma foldl_step_numAlloc_independent_of_constraints
  {numAlloc : ℕ}
  {varStore : VarStore p}
  {constraints1 constraints2 : Prop}
  {circuit : CircuitState p}
:
  (CircuitState.evalInOrder circuit σ ⟨numAlloc, varStore, constraints1⟩).numAlloc =
  (CircuitState.evalInOrder circuit σ ⟨numAlloc, varStore, constraints2⟩).numAlloc
:= by
  rcases circuit with ⟨circuit⟩
  simp only [List.size_toArray, List.foldl_toArray']
  rewrite [←List.reverse_reverse circuit]
  induction circuit.reverse <;> grind

@[grind =>]
lemma foldr_step_numAlloc_independent_of_constraints
  {numAlloc : ℕ}
  {varStore : VarStore p}
  {constraints1 constraints2 : Prop}
  {circuit : CircuitState p}
:
  (Array.foldr (λ x y => step y x σ) ⟨numAlloc, varStore, constraints1⟩ circuit).numAlloc =
  (Array.foldr (λ x y => step y x σ) ⟨numAlloc, varStore, constraints2⟩ circuit).numAlloc
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  rw [show Array.mk circuit.reverse.reverse = Array.reverse ⟨circuit.reverse⟩ by simp]
  simp only [Array.foldr_reverse]
  exact foldl_step_numAlloc_independent_of_constraints

lemma foldl_step_varStore_independent_of_constraints
  {numAlloc : ℕ}
  {varStore : VarStore p}
  {constraints1 constraints2 : Prop}
  {circuit : CircuitState p}
:
  (CircuitState.evalInOrder circuit σ ⟨numAlloc, varStore, constraints1⟩).varStore =
  (CircuitState.evalInOrder circuit σ ⟨numAlloc, varStore, constraints2⟩).varStore
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  induction circuit.reverse
  -- TODO This used to be just `induction <;> grind`, now we need lemmas in terms of `GetElem?`
  -- to push through
  grind [=GetElem?.getElem?]
  simp
  next hd tl ih =>
    simp at *
    rcases hd with _ | _ | _ | _ | _
    · grind
    · grind
    · rw [Array.foldr_toList, Array.foldr_toList]
      grind
    · rw [Array.foldr_toList, Array.foldr_toList]
      simp only [step_isZero]
      unfold GetElem?.getElem?
      unfold instGetElem?FixedExpZModMem
      grind [GetElem?.getElem?, instGetElem?FixedExpZModMem]
    ·
      simp
      unfold GetElem?.getElem!
      unfold instGetElem?FixedExpZModMem
      simp
      rw [Array.foldr_toList, Array.foldr_toList]
      grind

@[grind .]
lemma foldr_step_varStore_independent_of_constraints
  {numAlloc : ℕ}
  {varStore : VarStore p}
  {constraints1 constraints2 : Prop}
  {circuit : CircuitState p}
:
  (Array.foldr (λ x y => step y x σ) ⟨numAlloc, varStore, constraints1⟩ circuit).varStore =
  (Array.foldr (λ x y => step y x σ) ⟨numAlloc, varStore, constraints2⟩ circuit).varStore
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  rw [show Array.mk circuit.reverse.reverse = Array.reverse ⟨circuit.reverse⟩ by simp]
  simp only [Array.foldr_reverse]
  exact foldl_step_varStore_independent_of_constraints

-- /--
-- This exists to appease `grind`.
-- -/
-- @[grind! .]
-- lemma foldr_step_varStore_independent_of_constraints'
--   {circuit : CircuitState p}
--   {σ₁ σ₂ : CircuitResult p}
--   (h₁ : σ₁.numAlloc = σ₂.numAlloc)
--   (h₂ : σ₁.varStore = σ₂.varStore)
-- :
--   (Array.foldr (λ x y => step y x) σ₁ circuit).varStore =
--   (Array.foldr (λ x y => step y x) σ₂ circuit).varStore
-- := by
--   rewrite [←Array.reverse_reverse circuit]
--   simp only [Array.foldr_reverse]
--   grind [cases CircuitResult]

-- lemma foldl_step_constraints_and
--   {result : CircuitResult p}
--   {circuit : CircuitState p}
-- :
--   (CircuitState.evalInOrder circuit result).constraints = (
--     result.constraints ∧
--     (CircuitState.evalInOrder circuit result.split).constraints
--   )
-- := by
--   rcases circuit with ⟨circuit⟩
--   rewrite [←List.reverse_reverse circuit]
--   induction circuit.reverse
--   -- TODO This used to be just `induction <;> grind`, now we need lemmas in terms of `GetElem?`
--   -- to push through
--   grind
--   simp
--   next hd tl ih =>
--     simp at *
--     rcases hd with _ | _ | _ | _ | _
--     ·
--       simp
--       unfold GetElem?.getElem?
--       unfold instGetElem?FixedExpZModMem
--       rw [Array.foldr_toList, Array.foldr_toList]
--       grind [GetElem?.getElem?, instGetElem?FixedExpZModMem]
--     · grind
--     · rw [Array.foldr_toList, Array.foldr_toList]
--       grind
--     · simp only [step_isZero]
--       unfold GetElem?.getElem?
--       unfold instGetElem?FixedExpZModMem
--       rw [Array.foldr_toList, Array.foldr_toList]
--       grind [GetElem?.getElem?, instGetElem?FixedExpZModMem]
--     · simp
--       unfold get?
--       rw [Array.foldr_toList, Array.foldr_toList]
--       grind

end CircuitResult

namespace CircuitState

variable {p : ℕ}

def seq (circuit₁ circuit₂ : CircuitState p)
        (varStore : VarStore p)
        (numAlloc : ℕ)
        (σ : HashConsSt p)
: CircuitResult p :=
  let ⟨numAllocMid, varStoreMid, constraintsMid⟩ := eval circuit₁ varStore numAlloc σ
  let ⟨numAllocPost, varStorePost, constraintsPost⟩ := eval circuit₂ varStoreMid numAllocMid σ
  ⟨numAllocPost, varStorePost, constraintsMid ∧ constraintsPost⟩

-- @[simp, grind=]
-- lemma numAlloc_seq (circuit1 circuit2 : CircuitState p) (varStore : VarStore p) (numAlloc : ℕ):
--   (CircuitState.seq circuit1 circuit2 varStore numAlloc).numAlloc =
--   let mid := [varStore, numAlloc|circuit1]ₑ
--   [mid.varStore, mid.numAlloc|circuit2]ₑ.numAlloc
-- := rfl

-- @[simp, grind=]
-- lemma varStore_seq (circuit1 circuit2 : CircuitState p) (varStore : VarStore p) (numAlloc : ℕ):
--   (CircuitState.seq circuit1 circuit2 varStore numAlloc).varStore =
--   let mid := [varStore, numAlloc|circuit1]ₑ
--   [mid.varStore, mid.numAlloc|circuit2]ₑ.varStore
-- := rfl

-- @[simp, grind=]
-- lemma constraints_seq (circuit1 circuit2 : CircuitState p) (varStore : VarStore p) (numAlloc : ℕ):
--   (CircuitState.seq circuit1 circuit2 varStore numAlloc).constraints =
--   let mid := [varStore, numAlloc|circuit1]ₑ
--   mid.constraints ∧ [mid.varStore, mid.numAlloc|circuit2]ₑ.constraints
-- := rfl

-- @[simp, grind =]
-- lemma eval_append
--   {numAlloc}
--   {circuit1 circuit2 : CircuitState p}
--   {varStore}
-- :
--   [varStore, numAlloc | circuit1 ++ circuit2]ₑ = seq circuit1 circuit2 varStore numAlloc
-- := by
--   simp [eval]
--   ext1
--   all_goals dsimp [seq]
--   . exact CircuitResult.foldl_step_numAlloc_independent_of_constraints
--   . exact CircuitResult.foldl_step_varStore_independent_of_constraints
--   . exact CircuitResult.foldl_step_constraints_and

-- @[simp high, grind =]
-- lemma eval_singleton
--   {numAlloc}
--   {command : CircuitusPlanus p}
--   {varStore}
-- :
--   [varStore, numAlloc | #[command]]ₑ =
--   [unconstrained[numAlloc][varStore] | command]ₛ := by
--   simp [eval, CircuitResult.step_unconstrained]

-- @[simp, grind =]
-- lemma eval_cons
--   {numAlloc}
--   {command : CircuitusPlanus p}
--   {circuit : CircuitState p}
--   {varStore}
-- :
--   [varStore, numAlloc | ⟨command :: circuit.toList⟩]ₑ =
--   seq #[command] circuit varStore numAlloc := by
--   rw [show ⟨command :: circuit.toList⟩ = #[command] ++ circuit by simp]
--   exact eval_append

-- section

-- variable {numAlloc : ℕ} {varStore : VarStore p} {e: FixedExp p}

-- @[simp, grind =]
-- lemma eval_empty :
--   [varStore, numAlloc | #[]]ₑ = unconstrained[numAlloc][varStore]
-- := by rfl

-- @[simp, grind =]
-- lemma eval_empty_collection :
--   [varStore, numAlloc | ∅]ₑ =
--   unconstrained[numAlloc][varStore]
-- := by rfl

-- @[simp, grind =]
-- lemma eval_eq0 :
--   [varStore, numAlloc | #[.eq0 e]]ₑ =
--   unconstrained[numAlloc][varStore].step (.eq0 e)
-- := by simp [eval, CircuitResult.addConstraint_unconstrained, GetElem?.getElem?]

-- @[simp, grind =]
-- lemma eval_lam :
--   [varStore, numAlloc | #[.lam]]ₑ =
--   unconstrained[numAlloc][varStore].step (.lam)
-- := by
--   simp [eval]

-- @[simp, grind =]
-- lemma eval_share :
--   [varStore, numAlloc | #[.share e]]ₑ =
--   unconstrained[numAlloc][varStore].step (.share e)
-- := by
--   simp [eval, CircuitResult.addConstraint_unconstrained, Membership.mem]

-- @[simp, grind =]
-- lemma eval_isZero :
--   [varStore, numAlloc | #[.isZero e]]ₑ =
--   unconstrained[numAlloc][varStore].step (.isZero e)
-- := by
--   simp [eval, CircuitResult.addConstraint_unconstrained, Membership.mem]
--   rfl

-- @[simp, grind =]
-- lemma eval_num2bits {width : ℕ} :
--   [varStore, numAlloc | #[.num2bits width e]]ₑ =
--   unconstrained[numAlloc][varStore].step (.num2bits width e)
-- := by
--   simp [eval, CircuitResult.addConstraint_unconstrained, Membership.mem, GetElem?.getElem!]

-- @[simp, grind =]
-- lemma seq_cons_nil {cmd : CircuitusPlanus p} {circuit : CircuitState p} {varStore} {numAlloc} :
--   seq (⟨cmd :: circuit.toList⟩) #[] varStore numAlloc =
--   seq #[cmd] circuit varStore numAlloc := by
--   aesop (add simp seq)

-- @[simp high, grind =]
-- lemma seq_singleton_nil {cmd : CircuitusPlanus p} {varStore} {numAlloc} :
--   seq #[cmd] #[] varStore numAlloc =
--   [varStore, numAlloc| #[cmd]]ₑ := by
--   simp [seq]

-- end

end CircuitState

-- end Edsl

-- end Clap
