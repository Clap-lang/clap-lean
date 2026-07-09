import Mathlib.Control.Monad.Writer

import Clap.eDSLState.Exp

namespace Clap

@[grind cases]
inductive CircuitusPlanus (p : ℕ) where
  | eq0 (e : FixedExp p)
  | lam
  | share (e : FixedExp p)
  | isZero (e : FixedExp p)
  | num2bits (w : ℕ) (e : FixedExp p)
  deriving Repr

abbrev CircuitState (p : ℕ) := List (CircuitusPlanus p)

namespace Edsl

structure CircuitResult (p : ℕ) where
  numAlloc : ℕ
  varStore : Std.ExtTreeMap ℕ (ZMod p)
  constraints : Prop

namespace CircuitResult

section

-- TODO do we need all of these?
variable {p k numAlloc : ℕ} {result result' : CircuitResult p}
         {constraint : Prop} {vars : Vector (ZMod p) k} {e : FixedExp p}
         {varStore : Std.ExtTreeMap ℕ (ZMod p)}

def init (p : ℕ) : CircuitResult p := ⟨0, ∅, True⟩

def withNoConstraints (numAlloc : ℕ) (varStore : Std.ExtTreeMap ℕ (ZMod p)) : CircuitResult p :=
  ⟨numAlloc, varStore, True⟩

@[simp, grind =]
lemma numAlloc_withNoConstraints : (withNoConstraints numAlloc varStore).numAlloc = numAlloc := rfl

@[simp, grind =]
lemma varStore_withNoConstraints : (withNoConstraints numAlloc varStore).varStore = varStore := rfl

@[simp, grind =]
lemma constraints_withNoConstraints : (withNoConstraints numAlloc varStore).constraints = True := rfl

def addConstraint (result : CircuitResult p) (constraint : Prop) : CircuitResult p :=
  {result with constraints := result.constraints ∧ constraint}

@[simp, grind =]
lemma addConstraint_mk
  (numAlloc : ℕ)
  (varStore : Std.ExtTreeMap ℕ (ZMod p))
  (constraints constraint : Prop)
:
  (Edsl.CircuitResult.mk numAlloc varStore constraints).addConstraint constraint =
  Edsl.CircuitResult.mk numAlloc varStore (constraints ∧ constraint)
:= rfl

@[simp, grind =]
lemma addConstraint_withNoConstraints {constraint : Prop} :
  (withNoConstraints numAlloc varStore).addConstraint constraint =
  ⟨numAlloc, varStore, constraint⟩ := by simp [withNoConstraints]

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
  (numAlloc : ℕ)
  (varStore : Std.ExtTreeMap ℕ (ZMod p))
  (constraints : Prop)
:
  (Edsl.CircuitResult.mk numAlloc varStore constraints).allocAnonymous =
  Edsl.CircuitResult.mk (numAlloc + 1) varStore constraints
:= rfl

@[simp, grind =]
lemma allocAnonymous_withNoConstraints :
  (CircuitResult.withNoConstraints numAlloc varStore).allocAnonymous =
  ⟨numAlloc + 1, varStore, True⟩ := by rfl

@[simp, grind =]
lemma numAlloc_allocAnonymous : result.allocAnonymous.numAlloc = result.numAlloc + 1 := rfl

@[simp, grind =]
lemma varStore_allocAnonymous : result.allocAnonymous.varStore = result.varStore := rfl

@[simp, grind =]
lemma constraints_allocAnonymous : result.allocAnonymous.constraints = result.constraints := rfl

def get? (result : CircuitResult p) (e : FixedExp p) : Option (ZMod p) :=
  e.eval result.varStore.get?

@[simp, grind =]
lemma get?_mk
  (e : FixedExp p)
  (numAlloc : ℕ)
  (varStore : Std.ExtTreeMap ℕ (ZMod p))
  (constraints : Prop)
:
  (Edsl.CircuitResult.mk numAlloc varStore constraints).get? e =
  FixedExp.eval varStore.get? e
:= rfl

@[grind =>]
lemma get?_of_varStore_eq_varStore (h : result.varStore = result'.varStore) : result.get? e = result'.get? e := by
  simp_all [CircuitResult.get?]

def getD (result : CircuitResult p) (e : FixedExp p) :=
  result.get? e |>.getD 0

@[simp, grind =]
lemma getD_eq_get?_getD : result.getD e = (result.get? e |>.getD 0) := rfl

@[simp, grind =]
lemma get?_withNoConstraints :
  (withNoConstraints numAlloc varStore).get? e =
  e.eval varStore.get? := by simp [withNoConstraints]

def assertAllocated (result : CircuitResult p) (e : FixedExp p) : CircuitResult p :=
  result.addConstraint (result.get? e).isSome

@[simp, grind =]
lemma assertAllocated_mk
  (e : FixedExp p)
  (numAlloc : ℕ)
  (varStore : Std.ExtTreeMap ℕ (ZMod p))
  (constraints : Prop)
:
  (Edsl.CircuitResult.mk numAlloc varStore constraints).assertAllocated e =
  Edsl.CircuitResult.mk numAlloc varStore (constraints ∧ (e.eval varStore.get?).isSome)
:= rfl

@[simp, grind =]
lemma numAlloc_assertAllocated :
  (result.assertAllocated e).numAlloc = result.numAlloc := rfl

@[simp, grind =]
lemma varStore_assertAllocated :
  (result.assertAllocated e).varStore = result.varStore := rfl

@[simp, grind =]
lemma constraints_assertAllocated :
  (result.assertAllocated e).constraints = (result.constraints ∧ (result.get? e).isSome = true) := rfl

@[simp, grind =]
lemma assertAllocated_withNoConstraints :
  (withNoConstraints numAlloc varStore).assertAllocated e =
  (withNoConstraints numAlloc varStore).addConstraint
  ((withNoConstraints numAlloc varStore).get? e).isSome := rfl

def alloc {k p : ℕ} (result : CircuitResult p) (vals : Vector (ZMod p) k) : CircuitResult p :=
  let indexed := (Vector.range k).map (·+result.numAlloc) |>.zip vals
  let varStore := result.varStore.insertMany indexed
  {result with varStore := varStore, numAlloc := result.numAlloc + k}

@[simp, grind =]
lemma alloc_mk
  (vals : Vector (ZMod p) k)
  (numAlloc : ℕ)
  (varStore : Std.ExtTreeMap ℕ (ZMod p))
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

def step (result : CircuitResult p) (next : CircuitusPlanus p) : CircuitResult p :=
  match next with
  | .eq0 e => result.addConstraint (result.get? e = .some 0)
  | .lam => result.allocAnonymous
  | .share e => result.assertAllocated e |>.alloc #v[result.getD e]
  | .isZero e => result.assertAllocated e |>.alloc #v[if result.get? e = .some 0 then 1 else 0]
  | .num2bits width e => result.assertAllocated e |>.alloc (num2bitsLsbPureV width (result.getD e))

-- TODO do we want to make individual functions for these parts and prove properties about them
@[simp, grind =]
lemma step_mk
  (numAlloc : ℕ)
  (varStore : Std.ExtTreeMap ℕ (ZMod p))
  (constraints : Prop)
  (next : CircuitusPlanus p)
: (Edsl.CircuitResult.mk numAlloc varStore constraints).step next =
  Edsl.CircuitResult.mk
    (match next with
      | .eq0 _ => numAlloc
      | .lam => numAlloc + 1
      | .share e => numAlloc + 1
      | .isZero e => numAlloc + 1
      | .num2bits width _ => numAlloc + width
    )
    (match next with
      | .eq0 _ => varStore
      | .lam => varStore
      | .share e => varStore.insert numAlloc ((e.eval varStore.get?).getD 0)
      | .isZero e => varStore.insert numAlloc (if (e.eval varStore.get?) = .some 0 then 1 else 0)
      | .num2bits width e => varStore.insertMany
        ((Vector.map (fun x => x + numAlloc) (Vector.range width)).zip
          (num2bitsLsbPureV width ((FixedExp.eval varStore.get? e).getD 0)))
    )
    (match next with
      | .eq0 e => constraints ∧ (e.eval varStore.get?) = .some 0
      | .lam => constraints
      | .share e => constraints ∧ (e.eval varStore.get?).isSome
      | .isZero e => constraints ∧ (e.eval varStore.get?).isSome
      | .num2bits width e => constraints ∧ (e.eval varStore.get?).isSome
    )
:= by
  cases next <;> simp [CircuitResult.step]
  rfl

def split (result : CircuitResult p) : CircuitResult p :=
  {result with constraints := True}

@[simp, grind =]
lemma numAlloc_split : result.split.numAlloc = result.numAlloc := rfl

@[simp, grind =]
lemma varStore_split : result.split.varStore = result.varStore := rfl

@[simp, grind =]
lemma constraints_split : result.split.constraints = True := rfl

section

variable {p width : ℕ} {result : CircuitResult p} {e : FixedExp p}

@[simp, grind =]
lemma step_eq0 :
  result.step (.eq0 e) = result.addConstraint (result.get? e = .some 0) := rfl

@[simp, grind =]
lemma step_lam :
  result.step .lam = result.allocAnonymous := rfl

@[simp, grind =]
lemma step_share :
  result.step (.share e) = (result.assertAllocated e |>.alloc #v[result.getD e]) := rfl

@[simp, grind =]
lemma step_isZero :
  result.step (.isZero e) = (result.assertAllocated e |>.alloc #v[if result.get? e = .some 0 then 1 else 0]) := rfl

@[simp, grind =]
lemma step_num2bits :
  result.step (.num2bits width e) = (result.assertAllocated e |>.alloc (num2bitsLsbPureV width (result.getD e))) := rfl

end

end

end CircuitResult

abbrev CircuitState.evalInOrder {p : ℕ} (circuit : CircuitState p) := circuit.foldl CircuitResult.step

def CircuitState.eval {p : ℕ} (circuit : CircuitState p) (varStore : Std.ExtTreeMap ℕ (ZMod p)) (numAlloc : ℕ) : CircuitResult p :=
  CircuitState.evalInOrder circuit ⟨numAlloc, varStore, True⟩

namespace CircuitResult

variable {p : ℕ}

@[ext]
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
  {varStore : Std.ExtTreeMap ℕ (ZMod p)}
  {constraints1 constraints2 : Prop}
  {circuit : CircuitState p}
:
  (CircuitState.evalInOrder circuit ⟨numAlloc, varStore, constraints1⟩).numAlloc =
  (CircuitState.evalInOrder circuit ⟨numAlloc, varStore, constraints2⟩).numAlloc
:= by
  rewrite [←List.reverse_reverse circuit]
  induction circuit.reverse <;> grind

@[grind =>]
lemma foldr_step_numAlloc_independent_of_constraints
  {numAlloc : ℕ}
  {varStore : Std.ExtTreeMap ℕ (ZMod p)}
  {constraints1 constraints2 : Prop}
  {circuit : List (CircuitusPlanus p)}
:
  (List.foldr (λ x y => step y x) ⟨numAlloc, varStore, constraints1⟩ circuit).numAlloc =
  (List.foldr (λ x y => step y x) ⟨numAlloc, varStore, constraints2⟩ circuit).numAlloc
:= by
  rewrite [←List.reverse_reverse circuit]
  simp only [List.foldr_reverse]
  exact foldl_step_numAlloc_independent_of_constraints

lemma foldl_step_varStore_independent_of_constraints
  {numAlloc : ℕ}
  {varStore : Std.ExtTreeMap ℕ (ZMod p)}
  {constraints1 constraints2 : Prop}
  {circuit : CircuitState p}
:
  (circuit.foldl step ⟨numAlloc, varStore, constraints1⟩).varStore =
  (circuit.foldl step ⟨numAlloc, varStore, constraints2⟩).varStore
:= by
  rewrite [←List.reverse_reverse circuit]
  induction circuit.reverse <;> grind

@[grind .]
lemma foldr_step_varStore_independent_of_constraints
  {numAlloc : ℕ}
  {varStore : Std.ExtTreeMap ℕ (ZMod p)}
  {constraints1 constraints2 : Prop}
  {circuit : List (CircuitusPlanus p)}
:
  (List.foldr (λ x y => step y x) ⟨numAlloc, varStore, constraints1⟩ circuit).varStore =
  (List.foldr (λ x y => step y x) ⟨numAlloc, varStore, constraints2⟩ circuit).varStore
:= by
  rewrite [←List.reverse_reverse circuit]
  simp only [List.foldr_reverse]
  exact foldl_step_varStore_independent_of_constraints

/--
This exists to appease `grind`.
-/
@[grind! .]
lemma foldr_step_varStore_independent_of_constraints'
  {circuit : List (CircuitusPlanus p)}
  {σ₁ σ₂ : CircuitResult p}
  (h₁ : σ₁.numAlloc = σ₂.numAlloc)
  (h₂ : σ₁.varStore = σ₂.varStore)
:
  (List.foldr (λ x y => step y x) σ₁ circuit).varStore =
  (List.foldr (λ x y => step y x) σ₂ circuit).varStore
:= by
  rewrite [←List.reverse_reverse circuit]
  simp only [List.foldr_reverse, ←List.foldl_toArray]
  grind [cases CircuitResult]

lemma foldl_step_constraints_and
  {result : CircuitResult p}
  {circuit : CircuitState p}
:
  (CircuitState.evalInOrder circuit result).constraints = (
    result.constraints ∧
    (CircuitState.evalInOrder circuit result.split).constraints
  )
:= by
  rewrite [←List.reverse_reverse circuit]
  induction circuit.reverse <;> grind

end CircuitResult

namespace CircuitState

variable {p : ℕ}

@[simp, grind =]
lemma eval_append
  {numAlloc}
  {circuit1 circuit2 : CircuitState p}
  {varStore}
:
  eval (circuit1 ++ circuit2) varStore numAlloc = (
    let ⟨numAllocMid, varStoreMid, constraintsMid⟩ := eval circuit1 varStore numAlloc
    let ⟨numAllocPost, varStorePost, constraintsPost⟩ := eval circuit2 varStoreMid numAllocMid
    ⟨numAllocPost, varStorePost, constraintsMid ∧ constraintsPost⟩
  )
:= by
  simp [eval]
  ext1
  all_goals dsimp
  . exact CircuitResult.foldl_step_numAlloc_independent_of_constraints
  . exact CircuitResult.foldl_step_varStore_independent_of_constraints
  . exact CircuitResult.foldl_step_constraints_and

@[simp, grind =]
lemma eval_cons
  {numAlloc}
  {command : CircuitusPlanus p}
  {circuit : CircuitState p}
  {varStore}
:
  eval (command :: circuit) varStore numAlloc = (
    let ⟨numAllocMid, varStoreMid, constraintsMid⟩ := eval command varStore numAlloc
    let ⟨numAllocPost, varStorePost, constraintsPost⟩ := eval circuit2 varStoreMid numAllocMid
    ⟨numAllocPost, varStorePost, constraintsMid ∧ constraintsPost⟩
  ) := sorry

section

variable {numAlloc : ℕ} {varStore : Std.ExtTreeMap ℕ (ZMod p)} {e: FixedExp p}

@[simp, grind =]
lemma eval_empty :
  Edsl.CircuitState.eval #[] varStore numAlloc =
  ⟨numAlloc, varStore, True⟩
:= by rfl

@[simp, grind =]
lemma eval_empty_collection :
  Edsl.CircuitState.eval ∅ varStore numAlloc =
  ⟨numAlloc, varStore, True⟩
:= by rfl

@[simp, grind =]
lemma eval_eq0 :
  Edsl.CircuitState.eval #[.eq0 e] varStore numAlloc =  
  (CircuitResult.withNoConstraints numAlloc varStore).step (.eq0 e)
:= by simp [eval]

@[simp, grind =]
lemma eval_lam :
  Edsl.CircuitState.eval #[.lam] varStore numAlloc =
  (CircuitResult.withNoConstraints numAlloc varStore).step (.lam)
:= by
  simp [eval]

@[simp, grind =]
lemma eval_share :
  Edsl.CircuitState.eval #[.share e] varStore numAlloc =
  (CircuitResult.withNoConstraints numAlloc varStore).step (.share e)
:= by
  simp [eval]

@[simp, grind =]
lemma eval_isZero :
  Edsl.CircuitState.eval #[.isZero e] varStore numAlloc =
  (CircuitResult.withNoConstraints numAlloc varStore).step (.isZero e)
:= by
  simp [eval]
  rfl

@[simp, grind =]
lemma eval_num2bits {width : ℕ} :
  Edsl.CircuitState.eval #[.num2bits width e] varStore numAlloc =
  (CircuitResult.withNoConstraints numAlloc varStore).step (.num2bits width e)
:= by
  simp [eval]

end

end CircuitState

end Edsl

end Clap
