import Mathlib.Control.Monad.Writer

import Clap.eDSLState.Circuit

namespace Clap

namespace Edsl

variable {p : ℕ}

abbrev CircuitStateM (p : ℕ) (α : Type) : Type := WriterT (CircuitState p) (StateM ℕ) α

section Monoid

-- TODO do we really want this instance, or do we create it locally in order to create LawfulMonad manually?
instance (p : ℕ) : Monoid (CircuitState p) where
  mul := List.append
  mul_assoc := List.append_assoc
  one := []
  one_mul := List.nil_append
  mul_one := List.append_nil

@[simp, grind =]
lemma CircuitState.mul_eq_append {a b: CircuitState p} :
  a * b = a ++ b
:= rfl

@[simp, grind =]
lemma CircuitState.one_eq_nil :
  (1 : CircuitState p) = []
:= rfl

end Monoid

namespace CircuitStateM

def run {p : ℕ} {α : Type} (cmd : CircuitStateM p α) (numAlloc : ℕ) :=
  StateT.run (WriterT.run cmd) numAlloc

def runAndEval
  {p : ℕ} {α : Type} (cmd : CircuitStateM p α) (numAlloc : ℕ) (varStore : Std.ExtTreeMap ℕ (ZMod p))
:
  α × CircuitResult p
:=
  let ⟨⟨result, circuit⟩, _numAlloc⟩ := (cmd.run numAlloc)
  ⟨result, Edsl.CircuitState.eval circuit varStore numAlloc⟩

@[simp]
abbrev getResult
  {p : ℕ} {α : Type} (cmd : CircuitStateM p α) (numAlloc : ℕ)
: α :=
  (cmd.run numAlloc).1.1

@[simp]
abbrev getState
  {p : ℕ} {α : Type} (cmd : CircuitStateM p α) (numAlloc : ℕ)
: CircuitState p :=
  (cmd.run numAlloc).1.2

@[simp]
abbrev getNumAlloc
  {p : ℕ} {α : Type} (cmd : CircuitStateM p α) (numAlloc : ℕ)
: ℕ :=
  (cmd.run numAlloc).2

def alloc {p : ℕ} : CircuitStateM p ℕ:=
  getModify (· + 1)

def wellFormed
  {α : Type}
  (action : CircuitStateM p α)
:
  Prop
:=
  ∀ numAlloc varStore,
    (action.getNumAlloc numAlloc) =
    (CircuitState.eval (action.getState numAlloc) varStore numAlloc).numAlloc

end CircuitStateM

attribute [Clap.monads, grind =]
  bind
  pure

  CircuitStateM.run

  WriterT.run
  WriterT.mk
  tell

  StateT.run
  StateT.bind
  StateT.pure
  StateT.map

  Functor.map


namespace CircuitState

@[simp, grind =]
lemma eval_bind
  {α β : Type}
  {varStore : Std.ExtTreeMap ℕ (ZMod p)}
  {numAlloc : ℕ}
  {action : CircuitStateM p α}
  {function : α → CircuitStateM p β}
:
  eval (CircuitStateM.run (action >>= function) numAlloc).1.2 varStore numAlloc =
  let ((result, action_circuit), numAlloc') := action.run numAlloc
  let ((_, function_circuit), _) := (function result).run numAlloc'
  let first_eval := eval action_circuit varStore numAlloc
  let second_eval := eval function_circuit first_eval.varStore first_eval.numAlloc
  {
    numAlloc := second_eval.numAlloc
    varStore := second_eval.varStore
    constraints := first_eval.constraints ∧ second_eval.constraints
  }
:= by
  simp only [Clap.monads]
  grind

lemma runAndEval_bind
  {α β : Type}
  {varStore : Std.ExtTreeMap ℕ (ZMod p)}
  {numAlloc : ℕ}
  {action : CircuitStateM p α}
  {function : α → CircuitStateM p β}
  (h_wf : action.wellFormed)
:
  (action >>= function).runAndEval numAlloc varStore =
  let ⟨actionData, actionCircuitResult⟩ := action.runAndEval numAlloc varStore
  let ⟨functionData, functionCircuitResult⟩ := ((function actionData).runAndEval actionCircuitResult.numAlloc actionCircuitResult.varStore)
  ⟨functionData, functionCircuitResult.addConstraint actionCircuitResult.constraints⟩
:= by
  simp [CircuitStateM.runAndEval, Clap.monads]
  have : (eval (action numAlloc).1.2 varStore numAlloc).numAlloc = (action numAlloc).2 := by
    simp [CircuitStateM.wellFormed, Clap.monads] at h_wf
    exact (h_wf numAlloc varStore).symm
  set x := action numAlloc
  obtain ⟨a, b⟩ := x
  simp [this]
  obtain ⟨c, d⟩ := function a.1 b
  simp [this]
  ext <;> grind

end CircuitState

namespace CircuitStateM

section

variable {numAlloc : ℕ}

@[Clap.monads]
lemma getModify_eq
  (f : ℕ → ℕ)
:
  @getModify
    ℕ
    (CircuitStateM p)
    (instMonadStateOfMonadStateOf ℕ (CircuitStateM p))
    f
    numAlloc = ((numAlloc, []), f numAlloc)
:= rfl

@[simp, grind =]
lemma alloc_eq :
  CircuitStateM.alloc (p := p) numAlloc =
  ((numAlloc, []), numAlloc + 1)
:= by
  simp [CircuitStateM.alloc, Clap.monads]

@[Clap.monads]
lemma Vector_ofFnM_empty_state
  {α}
  {n}
  {a : Fin n → ℕ → α}
  {c : Fin n → ℕ → ℕ}
:
  (@Vector.ofFnM (CircuitStateM p) _ n _ (λ x s => ⟨⟨a x s, []⟩, c x s⟩) numAlloc).1.2 =
  []
:= by
  induction n with
  | zero =>
    simp [Vector.ofFnM_zero, Clap.monads]
  | succ n h =>
    rewrite [Vector.ofFnM_succ]
    simp_all [Clap.monads]
    set x := @Vector.ofFnM (CircuitStateM p) _ _ _ _ _
    have : x = ⟨x.1, x.2⟩ := rfl
    rewrite [this]; clear this
    simp [x, h]

end

end CircuitStateM

end Edsl

end Clap
