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

-- Allocates new variable and returns reference to it
def alloc {p : ℕ} : ClapM p ExprRef := do
  let varIdx ← getModify (· + 1)
  HashConsM.mkVar (p := p) varIdx

section Getters

variable {numAlloc : ℕ} {σ : HashConsSt p}

def getResult
  {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ) (σ : HashConsSt p)
: α :=
  (cmd.run numAlloc σ).1.1.1

def getCircuit
  {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ) (σ : HashConsSt p)
: CircuitState p :=
  (cmd.run numAlloc σ).1.1.2

def getNumAlloc
  {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ) (σ : HashConsSt p)
: ℕ :=
  (cmd.run numAlloc σ).1.2

def getHashConsState
  {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ) (σ : HashConsSt p)
: HashConsSt p :=
  (cmd.run numAlloc σ).2

@[simp, grind=]
lemma getResult_alloc :
  ClapM.alloc.getResult numAlloc σ =
  (HashConsM.mkVar numAlloc σ).1
:= rfl

@[simp, grind=]
lemma getCircuit_alloc :
  ClapM.alloc.getCircuit numAlloc σ =
  #[]
:= rfl

@[simp, grind=]
lemma getNumAlloc_alloc :
  ClapM.alloc.getNumAlloc numAlloc σ = numAlloc + 1
:= rfl

@[simp, grind=]
lemma getHashConsState_alloc:
  ClapM.alloc.getHashConsState numAlloc σ =
  (HashConsM.mkVar numAlloc σ).2
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
lemma getResult_tell {numAlloc : ℕ} {xs : CircuitState p} {σ : HashConsSt p} :
  ClapM.getResult (tell xs) numAlloc σ = ()
:= rfl

@[simp, grind =]
lemma getCircuit_tell {numAlloc : ℕ} {xs : CircuitState p} {σ : HashConsSt p} :
  ClapM.getCircuit (tell xs) numAlloc σ =
  xs
:= rfl

@[simp, grind =]
lemma getNumAlloc_tell {numAlloc : ℕ} {xs : CircuitState p} {σ : HashConsSt p}:
  ClapM.getNumAlloc (tell xs) numAlloc σ =
  numAlloc
:= rfl

@[simp, grind =]
lemma getHashConsState_tell {numAlloc : ℕ} {xs : CircuitState p} {σ : HashConsSt p}:
  ClapM.getHashConsState (tell xs) numAlloc σ =
  σ
:= rfl

@[simp, grind=]
lemma getResult_pure {α} {numAlloc : ℕ} {x : α} {σ : HashConsSt p}:
  ClapM.getResult (p := p) (pure x) numAlloc σ =
  x
:= rfl

@[simp, grind=]
lemma getCircuit_pure {α} {numAlloc : ℕ} {x : α} {σ : HashConsSt p}:
  ClapM.getCircuit (p := p) (pure x) numAlloc σ =
  #[]
:= rfl

@[simp, grind=]
lemma getNumAlloc_pure {α} {numAlloc : ℕ} {x : α} {σ : HashConsSt p}:
  ClapM.getNumAlloc (p := p) (pure x) numAlloc σ =
  numAlloc
:= rfl

@[simp, grind=]
lemma getHashConsState_pure {α} {numAlloc : ℕ} {x : α} {σ : HashConsSt p}:
  ClapM.getHashConsState (p := p) (pure x) numAlloc σ =
  σ
:= rfl

@[simp, grind=]
lemma getResult_map {α β} (f : α → β) {numAlloc : ℕ} {cmd : ClapM p α} {σ : HashConsSt p}:
  (f <$> cmd).getResult numAlloc σ =
  f (cmd.getResult numAlloc σ)
:= rfl

@[simp, grind=]
lemma getNumAlloc_map {α β} (f : α → β) {numAlloc : ℕ} {cmd : ClapM p α} {σ : HashConsSt p}:
  (f <$> cmd).getNumAlloc numAlloc σ =
  cmd.getNumAlloc numAlloc σ
:= rfl

@[simp, grind=]
lemma getCircuit_map {α β} (f : α → β) {numAlloc : ℕ} {cmd : ClapM p α} {σ : HashConsSt p}:
  (f <$> cmd).getCircuit numAlloc σ =
  cmd.getCircuit numAlloc σ
:= rfl

@[simp, grind=]
lemma getHashConsState_map {α β} (f : α → β) {numAlloc : ℕ} {cmd : ClapM p α} {σ : HashConsSt p}:
  (f <$> cmd).getHashConsState numAlloc σ =
  cmd.getHashConsState numAlloc σ
:= rfl

end Getters

def runAndEval
  {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ) (varStore : VarStore p) (σ : HashConsSt p)
:
  α × CircuitResult p
:=
  ⟨
    cmd.getResult numAlloc σ,
    [varStore,(cmd.getHashConsState numAlloc σ),numAlloc|(cmd.getCircuit numAlloc σ)]ₑ
  ⟩

@[grind =]
def circuitState_wellFormed
  {α : Type}
  (action : ClapM p α)
  (numAlloc : ℕ)
  (σ : HashConsSt p)
: Prop
:=
  (action.getCircuit numAlloc σ).refsValid (action.getHashConsState numAlloc σ).exprs.size

@[grind =]
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
  (CircuitState.eval (action.getCircuit numAlloc σ) varStore numAlloc (action.getHashConsState numAlloc σ)).numAlloc

@[grind =]
def hashConsState_wellFormed
  {α : Type}
  (action : ClapM p α)
  (numAlloc : ℕ)
  (σ : HashConsSt p)
:
  Prop
:=
  σ.exprs.isPrefixOf (action.getHashConsState numAlloc σ).exprs

@[grind =]
def wellFormed
  {α : Type}
  (action : ClapM p α)
  (numAlloc : ℕ)
  (varStore : VarStore p)
  (σ : HashConsSt p)
:
  Prop
:=
  circuitState_wellFormed action numAlloc σ ∧
  numAlloc_wellFormed action numAlloc varStore σ ∧
  hashConsState_wellFormed action numAlloc σ

section Bind_WellFormed

variable
  {α β}
  {numAlloc : ℕ}
  {varStore : VarStore p}
  {σ : HashConsSt p}
  {a : ClapM p α}
  {f : α → ClapM p β}

@[simp, grind =]
lemma bind_refsValid :
  letI a_result := a.getResult numAlloc σ
  letI a_numAlloc := a.getNumAlloc numAlloc σ
  letI a_σ := a.getHashConsState numAlloc σ
  ((a >>= f).getCircuit numAlloc σ).refsValid ((a >>= f).getHashConsState numAlloc σ).exprs.size ↔
  (
    a.getCircuit numAlloc σ ++
    (f a_result).getCircuit a_numAlloc a_σ
  ).refsValid
    ((f a_result).getHashConsState a_numAlloc a_σ).exprs.size
:= by
  grind

-- TODO grind?
lemma refsValid_of_refsValid_of_le
  {circuit : CircuitState p}
  {low_bound high_bound : ℕ}
  (h_valid : circuit.refsValid low_bound)
  (h_le : low_bound ≤ high_bound)
:
  circuit.refsValid high_bound
:= by
  aesop (add simp [CircuitState.refsValid, CircuitusPlanus.refsValid]) (add safe (by grind))

example
  (h_a : a.wellFormed numAlloc varStore σ)
  (h_f : (
      f (a.getResult numAlloc σ)
    ).wellFormed
      (a.getNumAlloc numAlloc σ)
      [varStore,(a.getHashConsState numAlloc σ),numAlloc|a.getCircuit numAlloc σ]ₑ.varStore
      (a.getHashConsState numAlloc σ)
  )
:
  (a.getHashConsState numAlloc σ).exprs.size ≤
  ((a >>= f).getHashConsState numAlloc σ).exprs.size
:= by
  done

lemma bind_circuitState_wellFormed
  (h_a : a.wellFormed numAlloc varStore σ)
  (h_f : (
      f (a.getResult numAlloc σ)
    ).wellFormed
      (a.getNumAlloc numAlloc σ)
      [varStore,(a.getHashConsState numAlloc σ),numAlloc|a.getCircuit numAlloc σ]ₑ.varStore
      (a.getHashConsState numAlloc σ)
  )
:
  (a >>= f).circuitState_wellFormed numAlloc σ
:= by
  unfold circuitState_wellFormed
  rewrite [bind_refsValid, CircuitState.refsValid_append_iff]
  split_ands
  . obtain h_a_refs := h_a.1
    unfold circuitState_wellFormed at h_a_refs
    apply refsValid_of_refsValid_of_le h_a_refs


  done

lemma bind_wellFormed
  (h_a : a.wellFormed numAlloc varStore σ)
  (h_f : (
      f (a.getResult numAlloc σ)
    ).wellFormed
      (a.getNumAlloc numAlloc σ)
      [varStore,(a.getHashConsState numAlloc σ),numAlloc|a.getCircuit numAlloc σ]ₑ.varStore
      (a.getHashConsState numAlloc σ)
  )
:
  (a >>= f).wellFormed numAlloc varStore σ
:= by
  done

end Bind_WellFormed

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
  [varStore, σ, numAlloc|((action >>= function).getCircuit numAlloc σ)]ₑ =
  letI numAlloc' := (action.getNumAlloc numAlloc σ)
  letI σ' := (action.getHashConsState numAlloc σ)
  letI result := (action.getResult numAlloc σ)
  seq (action.getCircuit numAlloc σ) ((function result).getCircuit numAlloc' σ') varStore numAlloc σ
:= by
  simp [seq, eval, evalInOrder]
  ext <;> simp
  . exact CircuitResult.foldl_step_numAlloc_independent_of_constraints
  . exact CircuitResult.foldl_step_varStore_independent_of_constraints
  . rewrite [iff_eq_eq]
    exact CircuitResult.foldl_step_constraints_and

lemma getHashConsState_apply {α β} {result : α} {numAlloc} {σ} {f : α → ClapM p β} :
  (f result).getHashConsState numAlloc σ = ((f result).run numAlloc σ).2 := rfl

lemma runAndEval_bind
  {α β : Type}
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {action : ClapM p α}
  {function : α → ClapM p β}
  {σ : HashConsSt p}
  (h_wf_action : action.wellFormed numAlloc varStore σ)
  (
    h_wf_function :
      (function (action.getResult numAlloc σ)).wellFormed
        (action.getNumAlloc numAlloc σ)
        (action.runAndEval numAlloc varStore σ).2.varStore
        (action.getHashConsState numAlloc σ)
  )
:
  (action >>= function).runAndEval numAlloc varStore σ =
  let ⟨actionData, actionCircuitResult⟩ := action.runAndEval numAlloc varStore σ
  let ⟨functionData, functionCircuitResult⟩ := ((function actionData).runAndEval actionCircuitResult.numAlloc actionCircuitResult.varStore) (action.getHashConsState numAlloc σ)
  ⟨functionData, functionCircuitResult.addConstraint actionCircuitResult.constraints⟩
:= by
  simp [ClapM.runAndEval]
  split_ands
  . grind
  . simp [seq]
    set result := (action.getResult numAlloc σ)
    set numAlloc' := (action.getNumAlloc numAlloc σ)
    set σ' := (action.getHashConsState numAlloc σ)
    set circuit := (action.getCircuit numAlloc σ)
    set varStore' := [varStore, σ', numAlloc|circuit]ₑ.varStore
    ext
    . simp
      have : [varStore, σ', numAlloc|circuit]ₑ.numAlloc = numAlloc' := by
        grind
      rewrite [this]; clear this
      congr 3
      sorry
      sorry
    . sorry
    . sorry


end CircuitState

namespace ClapM

section

variable {numAlloc : ℕ}

@[Clap.monads]
lemma getModify_eq
  {f : ℕ → ℕ}
:
  @getModify
    ℕ
    (ClapM p)
    (instMonadStateOfMonadStateOf ℕ (ClapM p))
    f
    numAlloc = pure ((numAlloc, #[]), f numAlloc)
:= rfl

@[Clap.monads]
lemma Vector_ofFnM_empty_state
  {α}
  {n}
  {a : Fin n → ℕ → α}
  {c : Fin n → ℕ → ℕ}
  {σ}
:
  (@Vector.ofFnM (ClapM p) _ n _ (λ x s σ => ⟨⟨⟨a x s, #[]⟩, c x s⟩, σ⟩) numAlloc σ).1.1.2 =
  #[]
:= by
  induction n with
  | zero =>
    simp [Vector.ofFnM_zero, Clap.monads]
  | succ n h =>
    rewrite [Vector.ofFnM_succ]
    simp_all [Clap.monads]
    set x := @Vector.ofFnM (ClapM p) _ _ _ _ _ σ
    have : x = ⟨x.1, x.2⟩ := rfl
    rewrite [this]; clear this
    simp [x, h]

lemma bind_eval {α} {e!} {varStore : VarStore p} {f : ZMod p → Option α}
                {σ} (h : [varStore,σ|e!].isSome) :
  [varStore, σ|e!] >>= f = f ([varStore, σ|e!].get h) := by
  unfold HashConsM.eval
  unfold HashConsM.evalWithCache
  simp
  unfold Option.bind
  grind

@[grind <=]
lemma bind_eval' {α : Type} {e!} {varStore : VarStore p} {f : ZMod p → Option α}
                 {σ} (h : [varStore,σ|e!].isSome) :
  [varStore, σ|e!].bind f = f ([varStore, σ|e!].get h) := bind_eval h

end

end ClapM

end Edsl

end Clap
