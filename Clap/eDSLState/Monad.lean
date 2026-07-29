import Mathlib.Control.Monad.Writer

import Clap.eDSLState.Circuit

namespace Clap

namespace Edsl

variable {p : ℕ}

--StateT numAlloc
--WriterT array of circuit constructors
abbrev CircuitStateT (p : ℕ) (m : Type → Type) (α : Type) : Type := WriterT (CircuitState p) (StateT ℕ m) α

abbrev CircuitStateM (p : ℕ) (α : Type) : Type := CircuitStateT p Id α

abbrev ClapM (p : ℕ) (α : Type) : Type := CircuitStateT p (HashConsM p) α

namespace ClapM

def run {α}
  (cmd : ClapM p α) (numAlloc : ℕ) (hashConsState : HashConsSt p)
: ((α × CircuitState p) × ℕ) × (HashConsSt p) :=
  (HashConsM.run (StateT.run (WriterT.run cmd) numAlloc) hashConsState)

-- This is what ClapM actually is
-- Given an initial numAlloc and expression cache, produce:
--   a pure result
--   an updated expression cache
--   a new numAlloc
--   an array of circuit constructors (referencing the updated cache)
example {resultT}:
  ClapM p resultT =
  (ℕ → (HashConsSt p) → ((resultT × CircuitState p) × ℕ) × (HashConsSt p))
 := rfl

-- Pure takes numAlloc, hashConsState, and a value, and returns them all with no circuit constructors
example {resultT} {val : resultT}:
  @pure (ClapM p) _ resultT val =
  λ numAlloc hashConsState => (((val, #[]), numAlloc), hashConsState)
:= rfl

-- Bind evaluates action with a numAlloc and hashConsState
-- passes the result, new numAlloc, and new hashConsState to function,
-- then appends the action's circuit to the function's
example {midT resultT} {action : ClapM p midT} {function : midT → ClapM p resultT}:
  @bind (ClapM p) _ midT resultT action function =
  λ numAlloc hashConsState =>
    let (((resultMid, circuitStateMid), numAllocMid), hashConsStateMid) := action.run numAlloc hashConsState
    let (((resultPost, circuitStatePost), numAllocPost), hashConsStatePost) := (function resultMid).run numAllocMid hashConsStateMid
    (((resultPost, circuitStateMid ++ circuitStatePost), numAllocPost), hashConsStatePost)
:= rfl

section Monoid

-- TODO do we really want this instance, or do we create it locally in order to create LawfulMonad manually?
instance (p : ℕ) : Monoid (CircuitState p) where
  mul := Array.append
  mul_assoc a b c := by exact Array.append_assoc
  one := #[]
  one_mul := by unfold_projs; simp
  mul_one := by unfold_projs; simp

@[simp, grind =]
lemma CircuitState.mul_eq_append {a b: CircuitState p} :
  a * b = a ++ b
:= rfl

@[simp, grind =]
lemma CircuitState.one_eq_nil :
  (1 : CircuitState p) = #[]
:= rfl

end Monoid


-- @[simp, grind =]
-- TODO do we really want this is simp, perhaps run_mk?
lemma run_def {α} {cmd : ClapM p α} {numAlloc} :
  ClapM.run cmd numAlloc = cmd numAlloc := rfl

def runAndEval
  {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ) (varStore : VarStore p) (σ : HashConsSt p)
:
  α × CircuitResult p
:=
  let ⟨⟨⟨result, circuit⟩, _numAlloc⟩, σ⟩ := cmd.run numAlloc σ
  ⟨result, CircuitState.eval circuit varStore numAlloc σ⟩

def alloc {p : ℕ} : ClapM p ℕ :=
  getModify (· + 1)

section Getters

abbrev getResult
  {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ) (σ : HashConsSt p)
: α :=
  (cmd.run numAlloc σ).1.1.1

abbrev getCircuit
  {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ) (σ : HashConsSt p)
: CircuitState p :=
  (cmd.run numAlloc σ).1.1.2

abbrev getNumAlloc
  {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ) (σ : HashConsSt p)
: ℕ :=
  (cmd.run numAlloc σ).1.2

abbrev getHashConsState
  {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ) (σ : HashConsSt p)
: HashConsSt p :=
  (cmd.run numAlloc σ).2

@[simp, grind=]
lemma getResult_alloc (numAlloc : ℕ) (σ : HashConsSt p):
  (ClapM.alloc (p := p)).getResult numAlloc σ =
  numAlloc
:= rfl

@[simp, grind=]
lemma getCircuit_alloc (numAlloc : ℕ) (σ : HashConsSt p):
  (ClapM.alloc (p := p)).getCircuit numAlloc σ =
  #[]
:= rfl

@[simp, grind=]
lemma getNumAlloc_alloc (numAlloc : ℕ) (σ : HashConsSt p):
  (ClapM.alloc (p := p)).getNumAlloc numAlloc σ = numAlloc + 1
:= rfl

@[simp, grind=]
lemma getHashConsState_alloc (numAlloc : ℕ) (σ : HashConsSt p):
  (ClapM.alloc (p := p)).getHashConsState numAlloc σ = σ
:= rfl

@[simp, grind =]
lemma getResult_bind
  {α β}
  {action : ClapM p α}
  {function : α → ClapM p β}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
:
  (action >>= function).getResult numAlloc σ =
  ((function (action.getResult numAlloc σ)).getResult (action.getNumAlloc numAlloc σ)) (action.getHashConsState numAlloc σ)
:= rfl

@[simp, grind =]
lemma getCircuit_bind
  {α β}
  {action : ClapM p α}
  {function : α → ClapM p β}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
:
  (action >>= function).getCircuit numAlloc σ =
  (action.getCircuit numAlloc σ) ++
  ((function (action.getResult numAlloc σ)).getCircuit (action.getNumAlloc numAlloc σ) (action.getHashConsState numAlloc σ))
:= rfl

@[simp, grind =]
lemma getNumAlloc_bind
  {α β}
  {action : ClapM p α}
  {function : α → ClapM p β}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
:
  (action >>= function).getNumAlloc numAlloc σ =
  ((function (action.getResult numAlloc σ)).getNumAlloc (action.getNumAlloc numAlloc σ) (action.getHashConsState numAlloc σ))
:= rfl

@[simp, grind =]
lemma getHashConsState_bind
  {α β}
  {action : ClapM p α}
  {function : α → ClapM p β}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
:
  (action >>= function).getHashConsState numAlloc σ =
  ((function (action.getResult numAlloc σ)).getHashConsState (action.getNumAlloc numAlloc σ) (action.getHashConsState numAlloc σ))
:= rfl

@[simp, grind =]
lemma getResult_tell (numAlloc : ℕ) (xs : CircuitState p) (σ : HashConsSt p):
  ClapM.getResult (tell xs) numAlloc σ = ()
:= rfl

@[simp, grind =]
lemma getCircuit_tell (numAlloc : ℕ) (xs : CircuitState p) (σ : HashConsSt p):
  ClapM.getCircuit (tell xs) numAlloc σ =
  xs
:= rfl

@[simp, grind =]
lemma getNumAlloc_tell (numAlloc : ℕ) (xs : CircuitState p) (σ : HashConsSt p):
  ClapM.getNumAlloc (tell xs) numAlloc σ =
  numAlloc
:= rfl

@[simp, grind =]
lemma getHashConsState_tell (numAlloc : ℕ) (xs : CircuitState p) (σ : HashConsSt p):
  ClapM.getHashConsState (tell xs) numAlloc σ =
  σ
:= rfl

@[simp, grind=]
lemma getResult_pure {α} (numAlloc : ℕ) (x : α) (σ : HashConsSt p):
  ClapM.getResult (p := p) (pure x) numAlloc σ =
  x
:= rfl

@[simp, grind=]
lemma getCircuit_pure {α} (numAlloc : ℕ) (x : α) (σ : HashConsSt p):
  ClapM.getCircuit (p := p) (pure x) numAlloc σ =
  #[]
:= rfl

@[simp, grind=]
lemma getNumAlloc_pure {α} (numAlloc : ℕ) (x : α) (σ : HashConsSt p) :
  ClapM.getNumAlloc (p := p) (pure x) numAlloc σ =
  numAlloc
:= rfl

@[simp, grind=]
lemma getHashConsState_pure {α} (numAlloc : ℕ) (x : α) (σ : HashConsSt p) :
  ClapM.getHashConsState (p := p) (pure x) numAlloc σ =
  σ
:= rfl

@[simp, grind=]
lemma getResult_map {α β} (f : α → β) (numAlloc : ℕ) (cmd : ClapM p α) (σ : HashConsSt p):
  (f <$> cmd).getResult numAlloc σ =
  f (cmd.getResult numAlloc σ)
:= rfl

@[simp, grind=]
lemma getNumAlloc_map {α β} (f : α → β) (numAlloc : ℕ) (cmd : ClapM p α) (σ : HashConsSt p):
  (f <$> cmd).getNumAlloc numAlloc σ =
  cmd.getNumAlloc numAlloc σ
:= rfl

@[simp, grind=]
lemma getCircuit_map {α β} (f : α → β) (numAlloc : ℕ) (cmd : ClapM p α) (σ : HashConsSt p):
  (f <$> cmd).getCircuit numAlloc σ =
  cmd.getCircuit numAlloc σ
:= rfl

@[simp, grind=]
lemma getHashConsState_map {α β} (f : α → β) (numAlloc : ℕ) (cmd : ClapM p α) (σ : HashConsSt p):
  (f <$> cmd).getHashConsState numAlloc σ =
  cmd.getHashConsState numAlloc σ
:= rfl

end Getters

-- StateT is more powerful than we technically need, so we can restrict here
-- numAlloc must not decrease
-- hashConsState must only be appended to
-- TODO? circuit exprRefs are less than the state length
-- TODO? circuit varIdxs are less than numAlloc
-- TODO? pure, and bind lemmas
def LawfulClapM {p} {α} (cmd : ClapM p α) : Prop :=
  ∀ numAlloc hashConsState,
    let (((_result, _circuit), numAllocPost), hashConsStatePost) := cmd.run numAlloc hashConsState
    numAllocPost ≥ numAlloc ∧
    ∃ newExprs, hashConsStatePost.exprs = hashConsState.exprs ++ newExprs

def circuitState_wellFormed
  {α : Type}
  (action : ClapM p α)
  (numAlloc : ℕ)
  (varStore : VarStore p)
  (σ : HashConsSt p)
: Prop
:=
  (action.getCircuit numAlloc σ).refsValid (action.getHashConsState numAlloc σ).exprs.size ∧
  (action.getCircuit numAlloc σ).varsAllocated varStore (action.getHashConsState numAlloc σ)

def numAlloc_wellFormed
  {α : Type}
  (action : ClapM p α)
  (numAlloc : ℕ)
  (varStore : VarStore p)
  (σ : HashConsSt p)
:
  Prop
:=
  (action.getNumAlloc numAlloc σ) =
  (CircuitState.eval (action.getCircuit numAlloc σ) varStore numAlloc σ).numAlloc

def hashConsState_wellFormed
  {α : Type}
  (action : ClapM p α)
  (numAlloc : ℕ)
  (σ : HashConsSt p)
:
  Prop
:=
  ∃ newExprs, (action.getHashConsState numAlloc σ).exprs = σ.exprs ++ newExprs

def wellFormed
  {α : Type}
  (action : ClapM p α)
  (numAlloc : ℕ)
  (varStore : VarStore p)
  (σ : HashConsSt p)
:
  Prop
:=
  circuitState_wellFormed action numAlloc varStore σ ∧
  numAlloc_wellFormed action numAlloc varStore σ ∧
  hashConsState_wellFormed action numAlloc σ

end ClapM

attribute [Clap.monads, grind =]
  bind
  pure

  ClapM.run

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
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {action : ClapM p α}
  {function : α → ClapM p β}
  {σ : HashConsSt p}
:
  eval ((action >>= function).getCircuit numAlloc σ) varStore numAlloc σ =
  let (((result, action_circuit), numAlloc'), σ') := action.run numAlloc σ
  let (((_, function_circuit), _), _) := (function result).run numAlloc' σ'
  seq action_circuit function_circuit varStore numAlloc σ
:= by
  simp [seq, eval, evalInOrder, ←ClapM.getCircuit.eq_def]
  set x := (Array.foldl (λ result next => result.step next σ) { numAlloc := numAlloc, varStore := varStore, constraints := True : CircuitResult p} (action.getCircuit numAlloc σ))
  simp [←ClapM.getCircuit.eq_def, ←ClapM.getResult.eq_def, ←ClapM.getNumAlloc.eq_def, ←ClapM.getHashConsState.eq_def]
  ext <;> simp
  grind

lemma runAndEval_bind
  {α β : Type}
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {action : ClapM p α}
  {function : α → ClapM p β}
  (h_wf : action.wellFormed)
:
  (action >>= function).runAndEval numAlloc varStore =
  let ⟨actionData, actionCircuitResult⟩ := action.runAndEval numAlloc varStore
  let ⟨functionData, functionCircuitResult⟩ := ((function actionData).runAndEval actionCircuitResult.numAlloc actionCircuitResult.varStore)
  ⟨functionData, functionCircuitResult.addConstraint actionCircuitResult.constraints⟩
:= by
  sorry
  -- simp [ClapM.runAndEval, Clap.monads]
  -- have : (eval (action numAlloc).1.2 varStore numAlloc).numAlloc = (action numAlloc).2 := by
  --   simp [ClapM.wellFormed, Clap.monads] at h_wf
  --   exact (h_wf numAlloc varStore).symm
  -- set x := action numAlloc
  -- obtain ⟨a, b⟩ := x
  -- simp [this]
  -- obtain ⟨c, d⟩ := function a.1 b
  -- simp [seq, this]
  -- ext <;> grind

end CircuitState

namespace ClapM

section

variable {numAlloc : ℕ}

@[Clap.monads]
lemma getModify_eq
  (f : ℕ → ℕ)
:
  @getModify
    ℕ
    (ClapM p)
    (instMonadStateOfMonadStateOf ℕ (ClapM p))
    f
    numAlloc = ((numAlloc, #[]), f numAlloc)
:= rfl

@[simp, grind =]
lemma alloc_eq :
  ClapM.alloc (p := p) numAlloc =
  ((numAlloc, #[]), numAlloc + 1)
:= by
  simp [ClapM.alloc, Clap.monads]

@[Clap.monads]
lemma Vector_ofFnM_empty_state
  {α}
  {n}
  {a : Fin n → ℕ → α}
  {c : Fin n → ℕ → ℕ}
:
  (@Vector.ofFnM (ClapM p) _ n _ (λ x s => ⟨⟨a x s, #[]⟩, c x s⟩) numAlloc).1.2 =
  #[]
:= by
  induction n with
  | zero =>
    simp [Vector.ofFnM_zero, Clap.monads]
  | succ n h =>
    rewrite [Vector.ofFnM_succ]
    simp_all [Clap.monads]
    set x := @Vector.ofFnM (ClapM p) _ _ _ _ _
    have : x = ⟨x.1, x.2⟩ := rfl
    rewrite [this]; clear this
    simp [x, h]

@[aesop safe forward, grind _=_]
lemma mem_iff_isSome {p} {varStore : VarStore p} {x : FixedExp p} :
  x ∈ varStore ↔ [varStore|x].isSome := by rfl

lemma bind_eval {α} {a} {varStore : VarStore p} {f : ZMod p → Option α} (h : a ∈ varStore) :
  [varStore|a] >>= f = f ([varStore|a].get h) := by aesop (add simp Option.bind)

@[grind <=]
lemma bind_eval' {α} {a} {varStore : VarStore p} {f : ZMod p → Option α} (h : a ∈ varStore) :
  [varStore|a].bind f = f ([varStore|a].get h) := by aesop (add simp Option.bind)

end

end ClapM

end Edsl

end Clap
