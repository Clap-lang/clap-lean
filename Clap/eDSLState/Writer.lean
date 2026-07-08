import Mathlib.Control.Monad.Writer

import Clap.Circuit

import Clap.eDSLState.Wheels

namespace Clap

namespace Circuit

section

def p : ℕ := 57

variable {var : Type}


def pretty [Repr var] [Index var] (c : Circuit p var) := repr 0 c

end

end Circuit

abbrev FixedExp (p : ℕ) := Clap.Exp p ℕ
abbrev FixedCircuit (p : ℕ) := Clap.Circuit p ℕ

def FixedExp.eval {p : ℕ} (varStore : ℕ → Option (ZMod p)) (x : FixedExp p) : Option (ZMod p) :=
  match x with
  | .c x => .some x
  | .v x => varStore x
  | .add l r => do (←eval varStore l) + (←eval varStore r)
  | .sub l r => do (←eval varStore l) - (←eval varStore r)
  | .mul l r => do (←eval varStore l) * (←eval varStore r)

@[grind cases]
inductive CircuitusPlanus (p : ℕ) where
  | eq0 (e : FixedExp p)
  | lam
  | share (e : FixedExp p)
  | isZero (e : FixedExp p)
  | num2bits (w : ℕ) (e : FixedExp p)
  deriving Repr

abbrev CircuitState (p : ℕ) := Array (CircuitusPlanus p)

namespace Edsl

section

variable {p : ℕ}

abbrev CircuitStateM (p : ℕ) (α : Type) : Type := WriterT (CircuitState p) (ReaderM ℕ) α

def CircuitStateM.run {p : ℕ} {α : Type} (cmd : CircuitStateM p α) (numAlloc : ℕ): (α × CircuitState p) :=
  ReaderT.run WriterT.run cmd numAlloc

structure CircuitResult (p : ℕ) where
  numAlloc : ℕ
  varStore : Std.ExtTreeMap ℕ (ZMod p)
  constraints : Prop

namespace CircuitResult

section

variable {k : ℕ} {result result' : CircuitResult p}
         {constraint : Prop} {vars : Vector (ZMod p) k} {e : FixedExp p}

def addConstraint (result : CircuitResult p) (constraint : Prop) :=
  {result with constraints := result.constraints ∧ constraint}

@[simp, grind =]
lemma numAlloc_addConstraint : (result.addConstraint constraint).numAlloc = result.numAlloc := rfl

@[simp, grind =]
lemma varStore_addConstraint : (result.addConstraint constraint).varStore = result.varStore := rfl

@[simp, grind =]
lemma constraints_addConstraint : (result.addConstraint constraint).constraints =
                                  (result.constraints ∧ constraint) := rfl

def allocAnonymous (result : CircuitResult p) :=
  {result with numAlloc := result.numAlloc + 1}

@[simp, grind =]
lemma numAlloc_allocAnonymous : result.allocAnonymous.numAlloc = result.numAlloc + 1 := rfl

@[simp, grind =]
lemma varStore_allocAnonymous : result.allocAnonymous.varStore = result.varStore := rfl

def get? (result : CircuitResult p) (e : FixedExp p) :=
  e.eval result.varStore.get?

@[grind =>]
lemma get?_of_varStore_eq_varStore (h : result.varStore = result'.varStore) : result.get? e = result'.get? e := by
  simp_all [CircuitResult.get?]

def getD (result : CircuitResult p) (e : FixedExp p) :=
  result.get? e |>.getD 0

@[simp, grind =]
lemma getD_eq_get?_getD : result.getD e = (result.get? e |>.getD 0) := rfl

@[simp, grind =]
lemma constraints_allocAnonymous : result.allocAnonymous.constraints = result.constraints := rfl

def init (result : CircuitResult p) (e : FixedExp p) :=
  result.addConstraint (result.get? e).isSome

@[simp, grind =]
lemma numAlloc_init :
  (result.init e).numAlloc = result.numAlloc := rfl

@[simp, grind =]
lemma varStore_init :
  (result.init e).varStore = result.varStore := rfl

@[simp, grind =]
lemma constraints_init :
  (result.init e).constraints = (result.constraints ∧ (result.get? e).isSome = true) := rfl

def alloc {k p : ℕ} (result : CircuitResult p) (vars : Vector (ZMod p) k) :=
  let indexed := (Vector.range k).map (·+result.numAlloc) |>.zip vars
  let varStore := result.varStore.insertMany indexed
  {result with varStore := varStore, numAlloc := result.numAlloc + k}

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

def step {p : ℕ} (result : CircuitResult p) (next : CircuitusPlanus p) : CircuitResult p :=
  match next with
  | .eq0 e => result.addConstraint (result.get? e = .some 0)
  | .lam => result.allocAnonymous
  | .share e => result.init e |>.alloc #v[result.getD e]
  | .isZero e => result.init e |>.alloc #v[if result.get? e = .some 0 then 1 else 0]
  | .num2bits width e => result.init e |>.alloc (num2bitsLsbPureV width (result.getD e))
  -- num2bits width e => ⟨
  --   numAlloc + width,
  --   varStore.insertMany ((Vector.range width).zip (num2bitsLsbPureV width ((e.eval varStore.get?).getD 0))),
  --   TODO(check):         ^^^^^^^^^^^^^^^^^^^ I think we want `Vector.range width |>.map (·+numAlloc)` here,
  --                                            and in general, in the impl. of `alloc`
  --   constraints ∧ (e.eval varStore.get?).isSome
  -- ⟩

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
  result.step (.share e) = (result.init e |>.alloc #v[result.getD e]) := rfl

@[simp, grind =]
lemma step_isZero :
  result.step (.isZero e) = (result.init e |>.alloc #v[if result.get? e = .some 0 then 1 else 0]) := rfl

@[simp, grind =]
lemma step_num2bits :
  result.step (.num2bits width e) = (result.init e |>.alloc (num2bitsLsbPureV width (result.getD e))) := rfl

end

end

end CircuitResult

abbrev CircuitState.evalInOrder {p : ℕ} (circuit : CircuitState p) := circuit.foldl CircuitResult.step

def CircuitState.eval {p : ℕ} (circuit : CircuitState p) (varStore : Std.ExtTreeMap ℕ (ZMod p)) (numAlloc : ℕ) : CircuitResult p :=
  CircuitState.evalInOrder circuit ⟨numAlloc, varStore, True⟩

namespace CircuitResult

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
  obtain ⟨list⟩ := circuit
  rewrite [←List.reverse_reverse list]
  induction list.reverse <;> grind

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
  simp only [List.foldr_reverse, ←List.foldl_toArray]
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
  obtain ⟨list⟩ := circuit
  rewrite [←List.reverse_reverse list]
  induction list.reverse <;> grind

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
  simp only [List.foldr_reverse, ←List.foldl_toArray]
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
  grind [cases CircuitResult, foldl_step_varStore_independent_of_constraints]

lemma foldl_step_constraints_and
  {result : CircuitResult p}
  {circuit : CircuitState p}
:
  (CircuitState.evalInOrder circuit result).constraints = (
    result.constraints ∧
    (CircuitState.evalInOrder circuit result.split).constraints
  )
:= by
  obtain ⟨list⟩ := circuit
  rewrite [←List.reverse_reverse list]
  induction list.reverse <;> grind

end CircuitResult

namespace CircuitState

@[simp, grind =]
lemma eval_append
  {p : ℕ}
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
lemma eval_bind
  {α β : Type}
  {varStore : Std.ExtTreeMap ℕ (ZMod p)}
  {numAlloc : ℕ}
  {action : CircuitStateM p α}
  {function : α → CircuitStateM p β}
:
  eval (CircuitStateM.run (action >>= function) numAlloc).2 varStore numAlloc =
  let (result, action_circuit) := action.run numAlloc
  let (_, function_circuit) := (function result).run numAlloc
  let first_eval := eval action_circuit varStore numAlloc
  let second_eval := eval function_circuit first_eval.varStore first_eval.numAlloc
  {
    numAlloc := second_eval.numAlloc
    varStore := second_eval.varStore
    constraints := first_eval.constraints ∧ second_eval.constraints
  }
:= by
  simp only [CircuitStateM.run, ReaderT.run, WriterT.run, bind, WriterT.mk, ReaderT.bind, Functor.map]
  grind

end CircuitState

section

variable {var : Type}

@[irreducible]
def eq0 (e : FixedExp p) : CircuitStateM p Unit := do
  tell #[.eq0 e]

@[irreducible]
def lam {α : Type} (action: (FixedExp p) → CircuitStateM p α) : CircuitStateM p α := do
  tell #[.lam]
  let numAlloc ← read
  withReader (· + 1) (action (.v numAlloc))

@[irreducible]
def share (e : FixedExp p) : CircuitStateM p (FixedExp p) := do
  CircuitStateM.push (.share e)
  let varIdx ← CircuitStateM.alloc
  return .v varIdx

@[irreducible]
def isZero (e : FixedExp p) : CircuitStateM p (FixedExp p) := do
  CircuitStateM.push (.isZero e)
  let varIdx ← CircuitStateM.alloc
  return .v varIdx

@[irreducible]
def num2bits (width : ℕ) (e : FixedExp p) : CircuitStateM p (Vector (FixedExp p) width) := do
  CircuitStateM.push (.isZero e)
  Vector.ofFnM fun _ ↦ do
    let varIdx ← CircuitStateM.alloc
    return .v varIdx

def testWithInput (x : ZMod 57) : CircuitStateM 57 Unit := do
  eq0 (.c x)
  let y ← share (.add 1 1)
  discard <| [1, 2, y].mapM eq0
  eq0 4

def test : CircuitStateM p Unit := do
  let x ← lam
  eq0 x
  let y ← share (.add 1 1)
  discard <| [1, 2, y].mapM eq0
  eq0 4

#eval test.run (p := 57)

-- Something like this?
-- Aaanyway... now I need to make sure to produce `.lam`s from initial arguments

end

end

end Edsl

end Clap
