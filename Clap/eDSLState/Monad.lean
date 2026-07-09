import Mathlib.Control.Monad.Writer

import Clap.eDSLState.Circuit

namespace Clap

namespace Edsl

variable {p : ℕ}

abbrev CircuitStateM (p : ℕ) (α : Type) : Type := WriterT (CircuitState p) (StateM ℕ) α

-- TODO do we really want this instance, or do we create it locally in order to create LawfulMonad manually?
instance (p : ℕ) : Monoid (CircuitState p) where
  mul := Array.append
  mul_assoc := by apply Array.append_assoc
  one := #[]
  one_mul := by apply Array.empty_append
  mul_one := by apply Array.append_empty

@[simp, grind =]
lemma CircuitState.mul_eq_append (a b: CircuitState p) :
  a * b = a ++ b
:= rfl

@[simp, grind =]
lemma CircuitState.one_eq_empty :
  (1: CircuitState p) = #[]
:= rfl

#synth LawfulMonad (CircuitStateM 57)

def CircuitStateM.run {p : ℕ} {α : Type} (cmd : CircuitStateM p α) (numAlloc : ℕ) :=
  StateT.run (WriterT.run cmd) numAlloc

attribute [Clap.monads]
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

attribute [local implicit_reducible]
  StateT
  WriterT
  Id

def CircuitStateM.alloc {p : ℕ} : CircuitStateM p ℕ:=
  getModify (· + 1)

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

end CircuitState

namespace CircuitStateM

@[Clap.monads]
lemma getModify_eq
  (numAlloc : ℕ) (f : ℕ → ℕ)
:
  @getModify
    ℕ
    (CircuitStateM p)
    (instMonadStateOfMonadStateOf ℕ (CircuitStateM p))
    f
    numAlloc =
    ((numAlloc, #[]), f numAlloc)
:= rfl

@[simp, grind =]
lemma alloc_eq
  (numAlloc : ℕ)
:
  CircuitStateM.alloc (p := p) numAlloc =
  ((numAlloc, #[]), numAlloc + 1)
:= by
  simp [CircuitStateM.alloc, Clap.monads]

-- TODO should this be in just simp, and/or grind?
@[Clap.monads]
lemma Vector_ofFnM_empty_state
  (α)
  (n)
  (a : Fin n → ℕ → α)
  (c : Fin n → ℕ → ℕ)
  (numAlloc: ℕ)
:
  (@Vector.ofFnM (CircuitStateM p) _ n _ (λ x s => ⟨⟨a x s, #[]⟩, c x s⟩) numAlloc).1.2 =
  #[]
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

end CircuitStateM

end Edsl

end Clap
