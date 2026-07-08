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
  varStore : Std.TreeMap ℕ (ZMod p)
  constraints : Prop

def CircuitResult.step {p : ℕ} (result : CircuitResult p) (next : CircuitusPlanus p) : CircuitResult p :=
  let ⟨numAlloc, varStore, constraints⟩ := result
  match next with
    | .eq0 e => ⟨
      numAlloc,
      varStore,
      constraints ∧ (e.eval varStore.get?) = .some 0
    ⟩
    | .lam => ⟨
      numAlloc + 1,
      varStore,
      constraints
    ⟩
    | .share e => ⟨
      numAlloc + 1,
      varStore.insert numAlloc ((e.eval varStore.get?).getD 0),
      constraints ∧ (e.eval varStore.get?).isSome
    ⟩
    | .isZero e => ⟨
      numAlloc + 1,
      varStore.insert numAlloc (if (e.eval varStore.get?) = .some 0 then 1 else 0),
      constraints ∧ (e.eval varStore.get?).isSome
    ⟩
    | .num2bits width e => ⟨
      numAlloc + width,
      varStore.insertMany ((Vector.range width).zip (num2bitsLsbPureV width ((e.eval varStore.get?).getD 0))),
      constraints ∧ (e.eval varStore.get?).isSome
    ⟩

def CircuitState.eval {p : ℕ} (circuit : CircuitState p) (varStore : Std.TreeMap ℕ (ZMod p)) (numAlloc : ℕ) : CircuitResult p :=
  circuit.foldl CircuitResult.step ⟨numAlloc, varStore, True⟩

lemma CircuitResult.ext {p : ℕ} {r1 r2 : CircuitResult p}
  (h_numAlloc : r1.numAlloc = r2.numAlloc)
  (h_varStore : r1.varStore = r2.varStore)
  (h_constraints : r1.constraints = r2.constraints)
:
  r1 = r2
:= by
  obtain ⟨a1, b1, c1⟩ := r1
  obtain ⟨a2, b2, c2⟩ := r2
  simp_all

lemma CircuitResult.foldl_step_numAlloc_independent_of_constraints
  {numAlloc : ℕ}
  {varStore : Std.TreeMap ℕ (ZMod p)}
  {constraints1 constraints2 : Prop}
  {circuit : CircuitState p}
:
  (circuit.foldl CircuitResult.step ⟨numAlloc, varStore, constraints1⟩).numAlloc =
  (circuit.foldl CircuitResult.step ⟨numAlloc, varStore, constraints2⟩).numAlloc
:= by
  obtain ⟨list⟩ := circuit
  rewrite [←List.reverse_reverse list]
  induction list.reverse with
    | nil =>
      simp
    | cons head tail h_tail =>
      simp at h_tail
      simp
      set x := List.foldr _ _ _
      set y := List.foldr _ _ _
      cases head
      all_goals simp [CircuitResult.step, h_tail]

lemma CircuitResult.foldr_step_numAlloc_independent_of_constraints
  {numAlloc : ℕ}
  {varStore : Std.TreeMap ℕ (ZMod p)}
  {constraints1 constraints2 : Prop}
  {circuit : List (CircuitusPlanus p)}
:
  (List.foldr (λ x y => CircuitResult.step y x) ⟨numAlloc, varStore, constraints1⟩ circuit).numAlloc =
  (List.foldr (λ x y => CircuitResult.step y x) ⟨numAlloc, varStore, constraints2⟩ circuit).numAlloc
:= by
  rewrite [←List.reverse_reverse circuit]
  simp only [List.foldr_reverse, ←List.foldl_toArray]
  exact CircuitResult.foldl_step_numAlloc_independent_of_constraints

lemma CircuitResult.foldl_step_varStore_independent_of_constraints
  {numAlloc : ℕ}
  {varStore : Std.TreeMap ℕ (ZMod p)}
  {constraints1 constraints2 : Prop}
  {circuit : CircuitState p}
:
  (circuit.foldl CircuitResult.step ⟨numAlloc, varStore, constraints1⟩).varStore =
  (circuit.foldl CircuitResult.step ⟨numAlloc, varStore, constraints2⟩).varStore
:= by
  obtain ⟨list⟩ := circuit
  rewrite [←List.reverse_reverse list]
  induction list.reverse with
    | nil =>
      simp
    | cons head tail h_tail =>
      simp at h_tail
      simp
      set x := List.foldr _ _ _
      set y := List.foldr _ _ _
      have h_numAlloc : x.numAlloc = y.numAlloc := CircuitResult.foldr_step_numAlloc_independent_of_constraints
      cases head
      all_goals simp [CircuitResult.step, h_tail, h_numAlloc]

lemma CircuitResult.foldr_step_varStore_independent_of_constraints
  {numAlloc : ℕ}
  {varStore : Std.TreeMap ℕ (ZMod p)}
  {constraints1 constraints2 : Prop}
  {circuit : List (CircuitusPlanus p)}
:
  (List.foldr (λ x y => CircuitResult.step y x) ⟨numAlloc, varStore, constraints1⟩ circuit).varStore =
  (List.foldr (λ x y => CircuitResult.step y x) ⟨numAlloc, varStore, constraints2⟩ circuit).varStore
:= by
  rewrite [←List.reverse_reverse circuit]
  simp only [List.foldr_reverse, ←List.foldl_toArray]
  exact CircuitResult.foldl_step_varStore_independent_of_constraints

lemma CircuitResult.foldl_step_constraints_and
  {result : CircuitResult p}
  {circuit : CircuitState p}
:
  (circuit.foldl CircuitResult.step result).constraints = (
    result.constraints ∧
    (circuit.foldl CircuitResult.step ⟨result.numAlloc, result.varStore, True⟩).constraints
  )
:= by
  obtain ⟨list⟩ := circuit
  rewrite [←List.reverse_reverse list]
  induction list.reverse with
    | nil =>
      simp
    | cons head tail h_tail =>
      simp at h_tail
      simp
      set x := List.foldr _ _ _
      set y := List.foldr _ _ _
      have h_varStore : x.varStore = y.varStore := CircuitResult.foldr_step_varStore_independent_of_constraints
      cases head
      all_goals simp [CircuitResult.step, h_tail, h_varStore, and_assoc]

lemma CircuitState.eval_append
  {p : ℕ}
  {numAlloc}
  {circuit1 circuit2 : CircuitState p}
  {varStore}
:
  CircuitState.eval (circuit1 ++ circuit2) varStore numAlloc = (
    let ⟨numAllocMid, varStoreMid, constraintsMid⟩ := CircuitState.eval circuit1 varStore numAlloc
    let ⟨numAllocPost, varStorePost, constraintsPost⟩ := CircuitState.eval circuit2 varStoreMid numAllocMid
    ⟨numAllocPost, varStorePost, constraintsMid ∧ constraintsPost⟩
  )
:= by
  simp [CircuitState.eval]
  set first := Array.foldl _ _ circuit1
  apply CircuitResult.ext
  all_goals dsimp
  . exact CircuitResult.foldl_step_numAlloc_independent_of_constraints
  . exact CircuitResult.foldl_step_varStore_independent_of_constraints
  . exact CircuitResult.foldl_step_constraints_and

lemma CircuitState.eval_bind
  (α β: Type)
  (varStore : Std.TreeMap ℕ (ZMod p))
  (numAlloc : ℕ)
  (action : CircuitStateM p α)
  (function : α → CircuitStateM p β)
:
  CircuitState.eval (CircuitStateM.run (bind action function) numAlloc).2 varStore numAlloc =
  let (result, action_circuit) := action.run numAlloc
  let (_, function_circuit) := (function result).run numAlloc
  let first_eval := CircuitState.eval action_circuit varStore numAlloc
  let second_eval := CircuitState.eval function_circuit first_eval.varStore first_eval.numAlloc
  {
    numAlloc := second_eval.numAlloc
    varStore := second_eval.varStore
    constraints := first_eval.constraints ∧ second_eval.constraints
  }
:= by
  simp [CircuitStateM.run, bind, Functor.map, ReaderT.run, WriterT.run, WriterT.mk, ReaderT.bind]
  obtain ⟨data, state_post_action⟩ := action numAlloc
  dsimp
  obtain ⟨_, final_state⟩ := (function data) numAlloc
  dsimp
  simp [CircuitState.eval_append]

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
