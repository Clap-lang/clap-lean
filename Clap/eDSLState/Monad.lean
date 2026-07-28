import Mathlib.Control.Monad.Writer

import Clap.eDSLState.Circuit

namespace Clap

namespace Edsl

variable {p : ℕ}

--StateT numAlloc
abbrev CircuitStateT (p : ℕ) (m : Type → Type) (α : Type) : Type := WriterT (CircuitState p) (StateT ℕ m) α

abbrev CircuitStateM (p : ℕ) (α : Type) : Type := CircuitStateT p Id α

abbrev ClapM (p : ℕ) (α : Type) : Type := CircuitStateT p (HashConsM p) α

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

def CircuitStateM.run {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ) :=
  StateT.run (WriterT.run cmd) numAlloc

namespace ClapM

def run {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ) (σ : HashConsSt p) :
  ((α × CircuitState p) × ℕ) × HashConsSt p :=
  (StateT.run (WriterT.run cmd) numAlloc).run σ

@[simp, grind =]
lemma run_def {α} {cmd : ClapM p α} {numAlloc} :
  ClapM.run cmd numAlloc = cmd numAlloc := rfl

def runAndEval
  {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ) (varStore : VarStore p) (σ : HashConsSt p)
:
  α × CircuitResult p
:=
  let ⟨⟨⟨result, circuit⟩, _numAlloc⟩, _σ⟩ := cmd.run numAlloc σ
  ⟨result, Edsl.CircuitState.eval circuit varStore numAlloc⟩

def alloc {p : ℕ} : ClapM p ℕ :=
  getModify (· + 1)

section Getters

abbrev getResult
  {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ)
: α :=
  (cmd.run numAlloc).1.1

abbrev getCircuit
  {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ)
: CircuitState p :=
  (cmd.run numAlloc).1.2

abbrev getNumAlloc
  {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ)
: ℕ :=
  (cmd.run numAlloc).2

@[simp, grind=]
lemma getResult_alloc (numAlloc : ℕ):
  (ClapM.alloc (p := p)).getResult numAlloc =
  numAlloc
:= rfl

@[simp, grind=]
lemma getCircuit_alloc (numAlloc : ℕ):
  (ClapM.alloc (p := p)).getCircuit numAlloc =
  #[]
:= rfl

@[simp, grind=]
lemma getNumAlloc_alloc (numAlloc : ℕ):
  (ClapM.alloc (p := p)).getNumAlloc numAlloc = numAlloc + 1
:= rfl

@[simp, grind =]
lemma getResult_bind
  {α β}
  {action : ClapM p α}
  {function : α → ClapM p β}
  {numAlloc : ℕ}
:
  (action >>= function).getResult numAlloc =
  ((function (action.getResult numAlloc)).getResult (action.getNumAlloc numAlloc))
:= rfl

@[simp, grind =]
lemma getCircuit_bind
  {α β}
  {action : ClapM p α}
  {function : α → ClapM p β}
  {numAlloc : ℕ}
:
  (action >>= function).getCircuit numAlloc =
  (action.getCircuit numAlloc) ++
  ((function (action.getResult numAlloc)).getCircuit (action.getNumAlloc numAlloc))
:= rfl

@[simp, grind =]
lemma getNumAlloc_bind
  {α β}
  {action : ClapM p α}
  {function : α → ClapM p β}
  {numAlloc : ℕ}
:
  (action >>= function).getNumAlloc numAlloc =
  ((function (action.getResult numAlloc)).getNumAlloc (action.getNumAlloc numAlloc))
:= rfl

@[simp, grind =]
lemma getResult_tell (numAlloc : ℕ) (xs : CircuitState p):
  ClapM.getResult (tell xs) numAlloc = ()
:= rfl

@[simp, grind =]
lemma getCircuit_tell (numAlloc : ℕ) (xs : CircuitState p):
  ClapM.getCircuit (tell xs) numAlloc =
  xs
:= rfl

@[simp, grind =]
lemma getNumAlloc_tell (numAlloc : ℕ) (xs : CircuitState p):
  ClapM.getNumAlloc (tell xs) numAlloc =
  numAlloc
:= rfl

@[simp, grind=]
lemma getResult_pure {α} (numAlloc : ℕ) (x : α):
  ClapM.getResult (p := p) (pure x) numAlloc =
  x
:= rfl

@[simp, grind=]
lemma getCircuit_pure {α} (numAlloc : ℕ) (x : α):
  ClapM.getCircuit (p := p) (pure x) numAlloc =
  #[]
:= rfl

@[simp, grind=]
lemma getNumAlloc_pure {α} (numAlloc : ℕ) (x : α) :
  ClapM.getNumAlloc (p := p) (pure x) numAlloc =
  numAlloc
:= rfl

@[simp, grind=]
lemma getResult_map {α β} (f : α → β) (numAlloc : ℕ) (cmd : ClapM p α):
  (f <$> cmd).getResult numAlloc =
  f (cmd.getResult numAlloc)
:= rfl

@[simp, grind=]
lemma getNumAlloc_map {α β} (f : α → β) (numAlloc : ℕ) (cmd : ClapM p α):
  (f <$> cmd).getNumAlloc numAlloc =
  (cmd.getNumAlloc) numAlloc
:= rfl

@[simp, grind=]
lemma getCircuit_map {α β} (f : α → β) (numAlloc : ℕ) (cmd : ClapM p α):
  (f <$> cmd).getCircuit numAlloc =
  (cmd.getCircuit) numAlloc
:= rfl

end Getters

def wellFormed
  {α : Type}
  (action : ClapM p α)
:
  Prop
:=
  ∀ numAlloc varStore,
    (action.getNumAlloc numAlloc) =
    (CircuitState.eval (action.getCircuit numAlloc) varStore numAlloc).numAlloc

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
:
  eval ((action >>= function).getCircuit numAlloc) varStore numAlloc =
  let ((result, action_circuit), numAlloc') := action.run numAlloc
  let ((_, function_circuit), _) := (function result).run numAlloc'
  seq action_circuit function_circuit varStore numAlloc
:= by
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
