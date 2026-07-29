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
         {constraint : Prop} {vars : Vector (ZMod p) k} {e : HashConsM p ExprRef} {e! : ExprRef}
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

@[simp, grind =]
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

@[simp, grind =]
lemma allocAnonymous_mk
  {numAlloc : ℕ}
  {varStore : VarStore p}
  {constraints : Prop}
:
  (Edsl.CircuitResult.mk numAlloc varStore constraints).allocAnonymous =
  Edsl.CircuitResult.mk (numAlloc + 1) varStore constraints
:= rfl

@[simp, grind =]
lemma allocAnonymous_unconstrained :
  unconstrained[numAlloc][varStore].allocAnonymous =
  ⟨numAlloc + 1, varStore, True⟩ := by rfl

@[simp, grind =]
lemma numAlloc_allocAnonymous : result.allocAnonymous.numAlloc = result.numAlloc + 1 := rfl

@[simp, grind =]
lemma varStore_allocAnonymous : result.allocAnonymous.varStore = result.varStore := rfl

@[simp, grind =]
lemma constraints_allocAnonymous : result.allocAnonymous.constraints = result.constraints := rfl

@[grind =]
def get? (result : CircuitResult p) (e : ExprRef) (σ : HashConsSt p) : (Option (ZMod p)) := do
  HashConsM.eval result.varStore e σ

@[grind =]
def getM? (result : CircuitResult p) (e : HashConsM p ExprRef) : HashConsM p (Option (ZMod p)) := do
  HashConsM.evalM result.varStore e

instance : Membership (ExprRef × HashConsSt p) (CircuitResult p) :=
  ⟨fun Γ (x, σ) ↦ (get? Γ x σ).isSome⟩

instance : GetElem (CircuitResult p) (ExprRef × HashConsSt p) (ZMod p) (fun Γ x ↦ x ∈ Γ) :=
  ⟨fun Γ (x, σ) h ↦ Γ.get? x σ |>.get h⟩

def getD (result : CircuitResult p) (e : ExprRef) (σ : HashConsSt p) : ZMod p :=
  (result.get? e σ).getD (dflt := 0)

instance {p} : GetElem? (CircuitResult p) (ExprRef × HashConsSt p) (ZMod p) (fun Γ x ↦ x ∈ Γ) :=
  ⟨Function.uncurry ∘ get?, Function.uncurry ∘ getD⟩

def getDM (result : CircuitResult p) (e : HashConsM p ExprRef) : HashConsM p (ZMod p) := do
  result.getM? e <&> Option.getD (dflt := 0)

@[simp, grind =]
lemma getD_eq_getM?_getD {e : ExprRef} : result.getD e σ = (result[(e, σ )]?).getD (dflt := 0) := rfl

@[simp, grind =]
lemma getElem!_eq_getElem?_getD {e : ExprRef} : result[(e, σ)]! = (result[(e, σ)]?).getD (dflt := 0) := rfl

@[simp, grind =]
lemma getDM_eq_getM?_getD : result.getDM e = result.getM? e <&> Option.getD (dflt := 0) := rfl

@[simp, grind =]
lemma get?_mk
  {varStore : VarStore p}
  {e : ExprRef}
  {numAlloc : ℕ}
  {constraints : Prop}
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

@[simp, grind =]
lemma getElem?_mk
  {varStore : VarStore p}
  {e : ExprRef}
  {numAlloc : ℕ}
  {constraints : Prop}
:
  (Edsl.CircuitResult.mk numAlloc varStore constraints)[(e, σ)]? =
  [varStore,σ|e]
:= rfl

@[simp, grind =]
lemma membership_unconstrained
  {e :ExprRef}
:
  ((e, σ) ∈ unconstrained[numAlloc][varStore]) =
  ([varStore,σ|e].isSome = true)
:= rfl

@[simp, grind =]
lemma getElem?_unconstrained
  {e : ExprRef}
:
  unconstrained[numAlloc][varStore][(e, σ)]? = [varStore,σ|e]
:= rfl

@[simp, grind =]
lemma getM?_unconstrained:
  (unconstrained[numAlloc][varStore].getM? e).run σ =
  [varStore,σ|←e] := by simp [unconstrained]

@[grind =>]
lemma getElem?_of_varStore_eq_varStore {e : ExprRef} (h : result.varStore = result'.varStore)
:
  result[(e, σ)]? = result'[(e, σ)]?
:= by
  simp_all [GetElem?.getElem?, CircuitResult.get?]

@[grind =>]
lemma getM?_of_varStore_eq_varStore (h : result.varStore = result'.varStore) : result.getM? e = result'.getM? e := by
  simp_all [CircuitResult.getM?]

-- Asserts that the expression that e points to does not use any variables that aren't in the varStore
-- Panics if e is outside of σ
def assertAllocated (result : CircuitResult p) (e : ExprRef) (σ : HashConsSt p) : CircuitResult p :=
  let val := result[(e, σ)]?
  result.addConstraint val.isSome

def assertAllocatedM (result : CircuitResult p) (e : HashConsM p ExprRef) : HashConsM p (CircuitResult p) := do
  let val ← result.getM? e
  return result.addConstraint val.isSome

@[simp, grind =]
lemma assertAllocated_mk
  {e : ExprRef}
  {numAlloc : ℕ}
  {varStore : VarStore p}
  {constraints : Prop}
:
  (Edsl.CircuitResult.mk numAlloc varStore constraints).assertAllocated e σ =
  Edsl.CircuitResult.mk
    numAlloc
    varStore
    (constraints ∧ [varStore,σ|e].isSome)
:= rfl

@[simp, grind =]
lemma assertAllocatedM_mk
  {e : HashConsM p ExprRef}
  {numAlloc : ℕ}
  {varStore : VarStore p}
  {constraints : Prop}
:
  ((Edsl.CircuitResult.mk numAlloc varStore constraints).assertAllocatedM e).run σ =
  (
    Edsl.CircuitResult.mk
      numAlloc
      varStore
      (constraints ∧ [varStore,σ|←e].1.isSome)
    ,
    [varStore,σ|←e].2
  )
:= rfl

@[simp, grind =]
lemma numAlloc_assertAllocated :
  (result.assertAllocated e! σ).numAlloc = result.numAlloc := rfl

@[simp, grind =]
lemma varStore_assertAllocated :
  (result.assertAllocated e! σ).varStore = result.varStore := rfl

@[simp, grind =]
lemma constraints_assertAllocated :
  (result.assertAllocated e! σ).constraints = (result.constraints ∧ result[(e!, σ)]?.isSome) := rfl

@[simp, grind =]
lemma assertAllocated_unconstrained :
  unconstrained[numAlloc][varStore].assertAllocated e! σ =
  letI α := unconstrained[numAlloc][varStore]
  α.addConstraint ((e!, σ) ∈ α) := rfl

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

def step (result : CircuitResult p) (next : CircuitusPlanus p) (σ : HashConsSt p) : CircuitResult p :=
  match next with
  | .eq0 e => result.addConstraint (result[(e, σ)]? = .some 0)
  | .lam => result.allocAnonymous
  | .share e => (result.assertAllocated e σ).alloc #v[result[(e, σ)]!]
  | .isZero e => (result.assertAllocated e σ).alloc #v[if result[(e, σ)]? = .some 0 then 1 else 0]
  | .num2bits width e => (result.assertAllocated e σ).alloc (num2bitsLsbPureV width (result[(e, σ)]!))

notation "[" res ", " σ "|" cmd "]ₛ" => step res cmd σ

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

-- @[simp, grind =]
lemma step_unconstrained {command : CircuitusPlanus p} {σ} :
  [unconstrained[numAlloc][varStore], σ|command]ₛ =
  [⟨numAlloc, varStore, True⟩, σ|command]ₛ := rfl

def split (result : CircuitResult p) : CircuitResult p :=
  {result with constraints := True}

@[simp, grind =]
lemma numAlloc_split : result.split.numAlloc = result.numAlloc := rfl

@[simp, grind =]
lemma varStore_split : result.split.varStore = result.varStore := rfl

@[simp, grind =]
lemma constraints_split : result.split.constraints = True := rfl

-- section

-- variable {p width : ℕ} {result : CircuitResult p} {e : FixedExp p}

@[simp, grind =]
lemma step_eq0 :
  [result,σ|.eq0 e!]ₛ = result.addConstraint (result[(e!, σ)]? = .some 0) := rfl

@[simp, grind =]
lemma step_lam :
  [result,σ|.lam]ₛ = result.allocAnonymous := rfl

@[simp, grind =]
lemma step_share :
  [result, σ|.share e!]ₛ =
  (result.assertAllocated e! σ |>.alloc #v[result.getD e! σ]) := rfl

@[simp, grind =]
lemma step_isZero :
  [result, σ|.isZero e!]ₛ =
  (result.assertAllocated e! σ |>.alloc #v[if result[(e!, σ)]? = .some 0 then 1 else 0]) := rfl

@[simp, grind =]
lemma step_num2bits {width} :
  [result, σ|.num2bits width e!]ₛ =
  (result.assertAllocated e! σ |>.alloc (num2bitsLsbPureV width result[(e!, σ)]!)) := rfl

@[aesop unsafe, grind =]
lemma addConstraint_eq_mk :
  result.addConstraint constraint =
  ⟨result.numAlloc, result.varStore, result.constraints ∧ constraint⟩ := rfl

@[aesop unsafe, grind =]
lemma allocAnonymous_eq_mk :
  result.allocAnonymous =
  ⟨result.numAlloc + 1, result.varStore, result.constraints⟩ := rfl

lemma alloc_eq_mk {k} {vals : Vector _ k} :
  result.alloc vals =
  ⟨result.numAlloc + k,
   result.varStore.insertMany (((Vector.range k).map (· + result.numAlloc)).zip vals),
   result.constraints⟩ := by rfl

lemma assertAllocated_eq_addConstraint :
  result.assertAllocated e! σ = result.addConstraint ((e!, σ) ∈ result) := rfl

end

end CircuitResult

abbrev CircuitState.evalInOrder {p : ℕ} (circuit : CircuitState p) (σ : HashConsSt p) :=
  circuit.foldl (CircuitResult.step (σ := σ))

def CircuitState.eval {p : ℕ} (circuit : CircuitState p) (varStore : VarStore p) (numAlloc : ℕ) (σ : HashConsSt p) : CircuitResult p :=
  CircuitState.evalInOrder circuit σ ⟨numAlloc, varStore, True⟩

notation "[" varStore ", " σ ", " numAlloc "|" circuit "]ₑ" => CircuitState.eval circuit varStore numAlloc σ

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

lemma foldr_step_numAlloc_independent_of_constraints
  {numAlloc : ℕ}
  {varStore : VarStore p}
  {constraints1 constraints2 : Prop}
  {circuit : CircuitState p}
:
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints1⟩ circuit).numAlloc =
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints2⟩ circuit).numAlloc
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  rw [show Array.mk circuit.reverse.reverse = Array.reverse ⟨circuit.reverse⟩ by simp]
  simp only [Array.foldr_reverse]
  exact foldl_step_numAlloc_independent_of_constraints

lemma foldr_step_numAlloc_independent_of_constraints'
  {numAlloc : ℕ}
  {varStore : VarStore p}
  {constraints1 constraints2 : Prop}
  {circuit : CircuitState p}
:
  (List.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints1⟩ circuit.toList).numAlloc =
  (List.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints2⟩ circuit.toList).numAlloc
:= by
  simp only [Array.foldr_toList]
  exact foldr_step_numAlloc_independent_of_constraints

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
  -- TODO you know what, whatever works at this point...
  grind [=GetElem?.getElem?]
  simp
  next hd tl ih =>
    simp at *
    rcases hd with _ | _ | _ | _ | _
    · grind
    · grind
    · rw [Array.foldr_toList, Array.foldr_toList]
      simp [ih]
      rw [foldr_step_numAlloc_independent_of_constraints']
      congr 1
      grind
    · rw [Array.foldr_toList, Array.foldr_toList]
      simp only [step_isZero]
      unfold GetElem?.getElem?
      unfold instGetElem?ProdExprRefHashConsStZModMem
      simp
      rw [foldr_step_numAlloc_independent_of_constraints' (constraints2 := constraints2)]
      grind [GetElem?.getElem?, instGetElemProdExprRefHashConsStZModMem]
    · simp
      rw [Array.foldr_toList, Array.foldr_toList]
      simp [foldr_step_numAlloc_independent_of_constraints' (constraints2 := constraints2)]
      simp
      rw [ih]
      congr 3
      simp [GetElem?.getElem?, get?]
      rw [ih]

lemma foldr_step_varStore_independent_of_constraints
  {numAlloc : ℕ}
  {varStore : VarStore p}
  {constraints1 constraints2 : Prop}
  {circuit : CircuitState p}
:
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints1⟩ circuit).varStore =
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints2⟩ circuit).varStore
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  rw [show Array.mk circuit.reverse.reverse = Array.reverse ⟨circuit.reverse⟩ by simp]
  simp only [Array.foldr_reverse]
  exact foldl_step_varStore_independent_of_constraints

lemma foldr_step_varStore_independent_of_constraints'
  {numAlloc : ℕ}
  {varStore : VarStore p}
  {constraints1 constraints2 : Prop}
  {circuit : CircuitState p}
  (σ : HashConsSt p)
:
  (List.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints1⟩ circuit.toList).varStore =
  (List.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints2⟩ circuit.toList).varStore
:= by
  simp only [Array.foldr_toList]
  exact foldr_step_varStore_independent_of_constraints

@[grind .]
lemma getElem_foldr_independent_of_constraints
  {numAlloc : ℕ}
  {varStore : VarStore p}
  {constraints1 constraints2 : Prop}
  {circuit : CircuitState p}
  {e : ExprRef}
:
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints1⟩ circuit)[(e, σ)]? =
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints2⟩ circuit)[(e, σ)]?
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  rw [show Array.mk circuit.reverse.reverse = Array.reverse ⟨circuit.reverse⟩ by simp]
  simp only [Array.foldr_reverse]
  simp [GetElem?.getElem?, get?]
  rw [foldr_step_varStore_independent_of_constraints']

/--
This exists to appease `grind`.

NB this is useless now.
-/
-- @[grind! .] -- I don't think there's an easy way to teach grind about the `σ` under the lambda
lemma foldr_step_varStore_independent_of_constraints''
  {circuit : CircuitState p}
  {σ₁ σ₂ : CircuitResult p}
  (h₁ : σ₁.numAlloc = σ₂.numAlloc)
  (h₂ : σ₁.varStore = σ₂.varStore)
:
  (Array.foldr (λ x y => [y, σ|x]ₛ) σ₁ circuit).varStore =
  (Array.foldr (λ x y => [y, σ|x]ₛ) σ₂ circuit).varStore
:= by
  convert foldr_step_varStore_independent_of_constraints using 4 <;> grind

lemma foldr_step_varStore_independent_of_constraints'''
  {circuit : CircuitState p}
  {σ₁ σ₂ : CircuitResult p}
  (h₁ : σ₁.numAlloc = σ₂.numAlloc)
  (h₂ : σ₁.varStore = σ₂.varStore) :
  (List.foldr (λ x y => [y, σ|x]ₛ) σ₁ circuit.toList).varStore =
  (List.foldr (λ x y => [y, σ|x]ₛ) σ₂ circuit.toList).varStore := by
  simp [Array.foldr_toList]
  apply foldr_step_varStore_independent_of_constraints'' <;> grind

@[simp, grind .]
lemma isSome_foldr_split {result : CircuitResult p} {circuit : CircuitState p} {e : ExprRef} :
  (List.foldr (fun x y => [y, σ|x]ₛ) result.split circuit.toList)[(e, σ)]?.isSome ↔
  (List.foldr (fun x y => [y, σ|x]ₛ) result circuit.toList)[(e, σ)]?.isSome := by
  rcases result
  simp [split]
  grind

@[simp, grind .]
lemma isSome_foldr_split' {result : CircuitResult p} {circuit : CircuitState p} {e : ExprRef} :
  (Array.foldr (fun x y => [y, σ|x]ₛ) result.split circuit)[(e, σ)]?.isSome ↔
  (Array.foldr (fun x y => [y, σ|x]ₛ) result circuit)[(e, σ)]?.isSome := by
  rcases result
  simp [split]
  grind

lemma foldl_step_constraints_and
  {result : CircuitResult p}
  {circuit : CircuitState p}
:
  (CircuitState.evalInOrder circuit σ result).constraints = (
    result.constraints ∧
    (CircuitState.evalInOrder circuit σ result.split).constraints
  )
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  induction circuit.reverse
  -- TODO This used to be just `induction <;> grind`, now we need lemmas in terms of `GetElem?`
  -- to push through
  grind
  simp
  next hd tl ih =>
    simp at *
    rcases hd with _ | _ | _ | _ | _
    · simp
      unfold GetElem?.getElem?
      unfold instGetElem?ProdExprRefHashConsStZModMem
      rw [Array.foldr_toList, Array.foldr_toList]
      simp [get?]
      rw [ih]
      rw [foldr_step_varStore_independent_of_constraints''' (σ₂ := result.split)] <;>
      aesop
    · grind
    · rw [Array.foldr_toList, Array.foldr_toList]
      simp [ih]
      expose_names
      rw [isSome_foldr_split]
      aesop
    · simp only [step_isZero]
      unfold GetElem?.getElem?
      unfold instGetElem?ProdExprRefHashConsStZModMem
      rw [Array.foldr_toList, Array.foldr_toList]
      grind [GetElem?.getElem?, instGetElemProdExprRefHashConsStZModMem]
    · simp
      unfold GetElem?.getElem?
      rw [Array.foldr_toList, Array.foldr_toList]
      grind

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

syntax "[" term ", " term ", " term "|" term "; " term "]" : term
macro_rules
  | `(term| [$Γ, $σ, $numAlloc | $c₁; $c₂]) => `(seq $c₁ $c₂ $Γ $numAlloc $σ)

@[app_unexpander seq]
def unexpandSeq : Lean.PrettyPrinter.Unexpander
  | `($_ $c₁ $c₂ $Γ $numAlloc $σ) =>
    `([$Γ, $numAlloc, $σ | $c₁; $c₂])
  | _ => throw ()

@[simp, grind=]
lemma numAlloc_seq {circuit1 circuit2 : CircuitState p} {varStore : VarStore p} {numAlloc : ℕ} {σ}:
  [varStore, σ, numAlloc | circuit1; circuit2].numAlloc =
  let mid := [varStore, σ, numAlloc|circuit1]ₑ
  [mid.varStore, σ, mid.numAlloc|circuit2]ₑ.numAlloc
:= rfl

@[simp]
lemma varStore_seq (circuit1 circuit2 : CircuitState p) (varStore : VarStore p) (numAlloc : ℕ) {σ}:
  (CircuitState.seq circuit1 circuit2 varStore numAlloc σ).varStore =
  let mid := [varStore, σ, numAlloc|circuit1]ₑ
  [mid.varStore, σ, mid.numAlloc|circuit2]ₑ.varStore
:= rfl

@[simp, grind=]
lemma constraints_seq (circuit1 circuit2 : CircuitState p) (varStore : VarStore p) (numAlloc : ℕ) {σ}:
  (CircuitState.seq circuit1 circuit2 varStore numAlloc σ).constraints =
  let mid := [varStore, σ, numAlloc|circuit1]ₑ
  mid.constraints ∧ [mid.varStore, σ, mid.numAlloc|circuit2]ₑ.constraints
:= rfl

@[simp, grind =]
lemma eval_append
  {numAlloc}
  {circuit1 circuit2 : CircuitState p}
  {varStore}
  {σ}
:
  [varStore, σ, numAlloc | circuit1 ++ circuit2]ₑ = seq circuit1 circuit2 varStore numAlloc σ
:= by
  simp [eval]
  ext1
  all_goals dsimp [seq]
  . exact CircuitResult.foldl_step_numAlloc_independent_of_constraints
  . exact CircuitResult.foldl_step_varStore_independent_of_constraints
  . exact CircuitResult.foldl_step_constraints_and

@[simp high, grind =]
lemma eval_singleton
  {numAlloc}
  {command : CircuitusPlanus p}
  {varStore}
  {σ}
:
  [varStore, σ, numAlloc | #[command]]ₑ =
  [unconstrained[numAlloc][varStore], σ | command]ₛ := by
  simp [eval, CircuitResult.step_unconstrained]

@[simp, grind =]
lemma eval_cons
  {numAlloc}
  {command : CircuitusPlanus p}
  {circuit : CircuitState p}
  {varStore}
  {σ}
:
  [varStore, σ, numAlloc | ⟨command :: circuit.toList⟩]ₑ =
  seq #[command] circuit varStore numAlloc σ:= by
  rw [show ⟨command :: circuit.toList⟩ = #[command] ++ circuit by simp]
  exact eval_append

section

variable {numAlloc : ℕ} {varStore : VarStore p} {e: ExprRef} {σ}

@[simp, grind =]
lemma eval_empty :
  [varStore, σ, numAlloc | #[]]ₑ = unconstrained[numAlloc][varStore]
:= by rfl

@[simp, grind =]
lemma eval_empty_collection :
  [varStore, σ, numAlloc | ∅]ₑ =
  unconstrained[numAlloc][varStore]
:= by rfl

@[simp, grind =]
lemma eval_eq0 :
  [varStore, σ, numAlloc | #[.eq0 e]]ₑ =
  unconstrained[numAlloc][varStore].step (.eq0 e) σ
:= by simp [eval, CircuitResult.addConstraint_unconstrained]

@[simp, grind =]
lemma eval_lam :
  [varStore, σ, numAlloc | #[.lam]]ₑ =
  unconstrained[numAlloc][varStore].step (.lam) σ
:= by
  simp [eval]

@[simp, grind =]
lemma eval_share :
  [varStore, σ, numAlloc | #[.share e]]ₑ =
  unconstrained[numAlloc][varStore].step (.share e) σ
:= by
  simp [eval]

@[simp, grind =]
lemma eval_isZero :
  [varStore, σ, numAlloc | #[.isZero e]]ₑ =
  unconstrained[numAlloc][varStore].step (.isZero e) σ
:= by
  simp [eval]
  rfl

@[simp, grind =]
lemma eval_num2bits {width : ℕ} :
  [varStore, σ, numAlloc | #[.num2bits width e]]ₑ =
  unconstrained[numAlloc][varStore].step (.num2bits width e) σ
:= by
  simp [eval]

@[simp, grind =]
lemma seq_cons_nil {cmd : CircuitusPlanus p} {circuit : CircuitState p} {varStore} {numAlloc} :
  seq (⟨cmd :: circuit.toList⟩) #[] varStore numAlloc σ =
  seq #[cmd] circuit varStore numAlloc σ := by
  aesop (add simp seq)

@[simp high, grind =]
lemma seq_singleton_nil {cmd : CircuitusPlanus p} {varStore} {numAlloc} :
  seq #[cmd] #[] varStore numAlloc σ =
  [varStore, σ, numAlloc| #[cmd]]ₑ := by
  simp [seq]

end

end Clap.Edsl.CircuitState
