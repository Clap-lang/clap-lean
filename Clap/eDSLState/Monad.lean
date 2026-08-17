import Mathlib.Control.Monad.Writer

import Clap.eDSLState.Circuit

namespace Clap

variable {p : ℕ}

--StateT numAlloc
--WriterT array of circuit constructors
abbrev CircuitT (p : ℕ) (m : Type → Type) (α : Type) : Type := WriterT (Circuit p) (StateT ℕ m) α

abbrev CircuitM (p : ℕ) (α : Type) : Type := CircuitT p Id α

abbrev ClapM (p : ℕ) (α : Type) : Type := CircuitT p (HashConsM p) α

namespace ClapM

def run {α}
  (cmd : ClapM p α) (numAlloc : ℕ) (hashConsState : HashConsSt p)
: ((α × Circuit p) × ℕ) × (HashConsSt p) :=
  (HashConsM.run (StateT.run (WriterT.run cmd) numAlloc) hashConsState)

-- This is what ClapM actually is
-- Given an initial ℕ and expression cache, produce:
--   a pure result
--   an updated expression cache
--   a new ℕ
--   an array of circuit constructors (referencing the updated cache)
example {resultT}:
  ClapM p resultT =
  (ℕ → (HashConsSt p) → ((resultT × Circuit p) × ℕ) × (HashConsSt p))
 := rfl

-- Pure takes numAlloc, hashConsState, and a value, and returns them all with no circuit constructors
example {resultT} {val : resultT}:
  @pure (ClapM p) _ resultT val =
  λ numAlloc hashConsState => (((val, #[]), numAlloc), hashConsState)
:= rfl

-- Bind evaluates action with a ℕ and hashConsState
-- passes the result, new ℕ, and new hashConsState to function,
-- then appends the action's circuit to the function's
example {midT resultT} {action : ClapM p midT} {function : midT → ClapM p resultT}:
  @bind (ClapM p) _ midT resultT action function =
  λ state hashConsState =>
    let (((resultMid, CircuitMid), stateMid), hashConsStateMid) := action.run state hashConsState
    let (((resultPost, CircuitPost), numAllocPost), hashConsStatePost) := (function resultMid).run stateMid hashConsStateMid
    (((resultPost, CircuitMid ++ CircuitPost), numAllocPost), hashConsStatePost)
:= rfl

section Monoid

-- TODO do we really want this instance, or do we create it locally in order to create LawfulMonad manually?
instance (p : ℕ) : Monoid (Circuit p) where
  mul := Array.append
  mul_assoc a b c := by exact Array.append_assoc
  one := #[]
  one_mul := by unfold_projs; simp
  mul_one := by unfold_projs; simp

@[simp, grind =]
lemma Circuit.mul_eq_append {a b: Circuit p} :
  a * b = a ++ b
:= rfl

@[simp, grind =]
lemma Circuit.one_eq_nil :
  (1 : Circuit p) = #[]
:= rfl

end Monoid


-- @[simp, grind =]
-- TODO do we really want this is simp, perhaps run_mk?
lemma run_def {α} {cmd : ClapM p α} {numAlloc} :
  ClapM.run cmd numAlloc = cmd numAlloc := rfl

-- Allocates new variable and returns reference to it
def alloc {p : ℕ} : ClapM p ExprRef := do
  let varIdx ← getModify (·+1)
  HashConsM.mkVar (p := p) varIdx

section Getters

variable {numAlloc : ℕ} {σ : HashConsSt p}

def getResult
  {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ) (σ : HashConsSt p)
: α :=
  (cmd.run numAlloc σ).1.1.1

def getCircuit
  {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ) (σ : HashConsSt p)
: Circuit p :=
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
lemma getHashConsState_alloc :
  ClapM.alloc.getHashConsState numAlloc σ =
  (HashConsM.mkVar numAlloc σ).2
:= rfl

section NamedThisForDom

variable {α β} {action : ClapM p α} {function : α → ClapM p β}
         {numAlloc : ℕ} {σ : HashConsSt p} {xs : Circuit p}
         {cmd : ClapM p α} {f : α → β} {x : α}

@[simp, grind =]
lemma getResult_bind
:
  (action >>= function).getResult numAlloc σ =
  ((function (action.getResult numAlloc σ)).getResult (action.getNumAlloc numAlloc σ)) (action.getHashConsState numAlloc σ)
:= rfl

@[simp, grind =]
lemma getCircuit_bind :
  (action >>= function).getCircuit numAlloc σ =
  (action.getCircuit numAlloc σ) ++
  ((function (action.getResult numAlloc σ)).getCircuit (action.getNumAlloc numAlloc σ) (action.getHashConsState numAlloc σ))
:= rfl

@[simp, grind =]
lemma getState_bind
:
  (action >>= function).getNumAlloc numAlloc σ =
  ((function (action.getResult numAlloc σ)).getNumAlloc (action.getNumAlloc numAlloc σ) (action.getHashConsState numAlloc σ))
:= rfl

@[simp, grind =]
lemma getHashConsState_bind
:
  (action >>= function).getHashConsState numAlloc σ =
  ((function (action.getResult numAlloc σ)).getHashConsState (action.getNumAlloc numAlloc σ) (action.getHashConsState numAlloc σ))
:= rfl

@[simp, grind =]
lemma getResult_tell :
  ClapM.getResult (tell xs) numAlloc σ = ()
:= rfl

@[simp, grind =]
lemma getCircuit_tell :
  ClapM.getCircuit (tell xs) numAlloc σ =
  xs
:= rfl

@[simp, grind =]
lemma getNumAlloc_tell :
  ClapM.getNumAlloc (tell xs) numAlloc σ =
  numAlloc
:= rfl

@[simp, grind =]
lemma getHashConsState_tell :
  ClapM.getHashConsState (tell xs) numAlloc σ =
  σ
:= rfl

@[simp, grind=]
lemma getResult_pure :
  ClapM.getResult (p := p) (pure x) numAlloc σ =
  x
:= rfl

@[simp, grind=]
lemma getCircuit_pure :
  ClapM.getCircuit (p := p) (pure x) numAlloc σ =
  #[]
:= rfl

@[simp, grind=]
lemma getState_pure :
  ClapM.getNumAlloc (p := p) (pure x) numAlloc σ =
  numAlloc
:= rfl

@[simp, grind=]
lemma getHashConsState_pure :
  ClapM.getHashConsState (p := p) (pure x) numAlloc σ =
  σ
:= rfl

@[simp, grind=]
lemma getResult_map :
  (f <$> cmd).getResult numAlloc σ =
  f (cmd.getResult numAlloc σ)
:= rfl

@[simp, grind=]
lemma getState_map :
  (f <$> cmd).getNumAlloc numAlloc σ =
  cmd.getNumAlloc numAlloc σ
:= rfl

@[simp, grind=]
lemma getCircuit_map :
  (f <$> cmd).getCircuit numAlloc σ =
  cmd.getCircuit numAlloc σ
:= rfl

@[simp, grind=]
lemma getHashConsState_map :
  (f <$> cmd).getHashConsState numAlloc σ =
  cmd.getHashConsState numAlloc σ
:= rfl

end NamedThisForDom

end Getters

def runAndEval
  {p : ℕ} {α : Type} (cmd : ClapM p α) (numAlloc : ℕ) (varStore : VarStore p) (σ : HashConsSt p)
:
  α × EvalSt p
:=
  ⟨
    cmd.getResult numAlloc σ,
    [varStore,(cmd.getHashConsState numAlloc σ),numAlloc|(cmd.getCircuit numAlloc σ)]ₑ
  ⟩

/--
Well formed up to `numAlloc.pc`.
-/
@[grind =]
abbrev circuit_wellFormed
  {α : Type}
  (action : ClapM p α)
  (numAlloc : ℕ)
  (Γ : VarStore p)
  (σ : HashConsSt p)
: Prop
:=
  (action.getCircuit numAlloc σ).wellFormed Γ (action.getHashConsState numAlloc σ) numAlloc

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
  action.getNumAlloc numAlloc σ =
  [varStore, action.getHashConsState numAlloc σ, numAlloc|action.getCircuit numAlloc σ]ₑ.numAlloc

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
  circuit_wellFormed action numAlloc varStore σ ∧
  numAlloc_wellFormed action numAlloc varStore σ ∧
  hashConsState_wellFormed action numAlloc σ

section Bind_WellFormed

variable
  {α β}
  {numAlloc : ℕ}
  {numAlloc : ℕ}
  {varStore : VarStore p}
  {σ : HashConsSt p}
  {a : ClapM p α}
  {f : α → ClapM p β}

@[simp, grind =]
lemma refsValid_bind_iff :
  letI a_result := a.getResult numAlloc σ
  letI a_st := a.getNumAlloc numAlloc σ
  letI a_σ := a.getHashConsState numAlloc σ
  ((a >>= f).getCircuit numAlloc σ).refsValid ((a >>= f).getHashConsState numAlloc σ).size ↔
  (
    a.getCircuit numAlloc σ ++
    (f a_result).getCircuit a_st a_σ
  ).refsValid
    ((f a_result).getHashConsState a_st a_σ).size
:= by
  grind

lemma size_le_size_bind
  (h_f : (
      f (a.getResult numAlloc σ)
    ).wellFormed
      (a.getNumAlloc numAlloc σ)
      [varStore,(a.getHashConsState numAlloc σ),numAlloc|a.getCircuit numAlloc σ]ₑ.varStore
      (a.getHashConsState numAlloc σ)
  )
:
  (a.getHashConsState numAlloc σ).size ≤
  ((a >>= f).getHashConsState numAlloc σ).size
:= by
  simp
  unfold wellFormed hashConsState_wellFormed at h_f
  replace h_f := h_f.2.2
  rewrite [←Array.isPrefixOf_toList, List.isPrefixOf_iff_prefix] at h_f
  simp [Array.size_eq_length_toList, -Array.length_toList]
  grind

lemma bind_Circuit_wellFormed
  (h_a : a.wellFormed numAlloc varStore σ)
  (h_f : (
      f (a.getResult numAlloc σ)
    ).wellFormed
      (a.getNumAlloc numAlloc σ)
      [varStore,(a.getHashConsState numAlloc σ),numAlloc|a.getCircuit numAlloc σ]ₑ.varStore
      (a.getHashConsState numAlloc σ)
  )
:
  (a >>= f).circuit_wellFormed numAlloc varStore σ
:= by
  unfold circuit_wellFormed
  rewrite [Circuit.wellFormed_iff, refsValid_bind_iff, Circuit.refsValid_append_iff]
  split_ands
  . exact Circuit.refsValid_of_refsValid_of_le h_a.1.1 (size_le_size_bind h_f)
  . exact h_f.1.1
  . simp only [getCircuit_bind, getHashConsState_bind]
    unfold Circuit.varsAllocated
    intros i hi
    rcases h_a with ⟨⟨ha_refsValid, ha_varsAllocated⟩, ha_numAlloc, ha_hashConsSt⟩
    rcases h_f with ⟨⟨hf_refsValid, hf_varsAllocated⟩, hf_numAlloc, hf_hashConsSt⟩
    set result := a.getResult numAlloc σ with eq₁
    set numAlloc' := a.getNumAlloc numAlloc σ with eq₂
    set σ' := a.getHashConsState numAlloc σ with eq₃
    set circuit := a.getCircuit numAlloc σ with eq₄
    set varStore' := [varStore, σ', numAlloc|circuit]ₑ.varStore with eq₅
    set f_circuit := (f result).getCircuit numAlloc' σ' with eq₆
    set f_sigma := (f result).getHashConsState numAlloc' σ' with eq₇
    rw! [←eq₁, ←eq₂, ←eq₃, ←eq₄, ←eq₆]
    split_ands
    · by_cases h : i < circuit.size
      · rewrite [show (circuit ++ f_circuit).take i = circuit.take i by aesop (add safe (by grind))]
        simp only [h, Array.getElem_append_left]
        specialize ha_varsAllocated i h
        rw [Circuit.eval_of_refsValid_prefix (σ := σ') (by grind) (by grind)]
        grind
      · specialize hf_varsAllocated (i - circuit.size) (by grind)
        simp
        convert hf_varsAllocated.1 using 1
        · grind
        · unfold numAlloc_wellFormed at ha_numAlloc
          rw! [←eq₂, ←eq₃, ←eq₄] at ha_numAlloc
          have this : circuit.extract 0 i = circuit := by
            rw [Array.extract_eq_self_of_le]
            grind
          have that : numAlloc + Circuit.numAllocStep (Array.extract circuit 0 i) =
                 numAlloc' := by
            grind
          rw [that]
          simp [this]
          rw [Circuit.eval_of_refsValid_prefix (Γ := varStore) (σ' := f_sigma)]
          grind
          grind
    · intros i' hi'
      rw [Circuit.eval_numAlloc]
      by_cases h : i < circuit.size
      · simp [h] at hi' ⊢
        rw [←varSet.varSet_eq_of_prefix
              (e₂ := ⟨circuit[i].expr, f_sigma⟩)
              (e₁ := ⟨circuit[i].expr, σ'⟩) (by grind)] at hi'
        · unfold Circuit.varsAllocated at ha_varsAllocated
          specialize ha_varsAllocated i h
          simp [Circuit.eval_numAlloc] at ha_varsAllocated
          rcases ha_varsAllocated with ⟨eq₁, eq₂⟩
          specialize eq₂ i' hi'
          grind
        · grind
        · grind
      · specialize hf_varsAllocated (i - circuit.size) (by grind)
        rcases hf_varsAllocated with ⟨eq₁, newName⟩
        specialize newName i' (by grind)
        simp [Circuit.eval_numAlloc] at newName
        unfold numAlloc_wellFormed at ha_numAlloc
        rw! [←eq₂, ←eq₃, ←eq₄] at ha_numAlloc
        have this : circuit.extract 0 i = circuit := by
          rw [Array.extract_eq_self_of_le]
          grind
        grind

@[aesop safe, grind .]
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
  unfold wellFormed
  split_ands
  · exact bind_Circuit_wellFormed h_a h_f
  · grind
  · unfold hashConsState_wellFormed
    apply Array.isPrefixOf_trans (b := (a.getHashConsState numAlloc σ).exprs) <;> grind

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


namespace Circuit

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
  [varStore, σ, numAlloc|action.getCircuit numAlloc σ; (function result).getCircuit numAlloc' σ']ₑ
:= by
  simp [seq, eval, evalInOrder]
  ext1 <;> simp
  . exact EvalSt.evalInOrder_numAlloc_independent_of_constraints
  . exact EvalSt.evalInOrder_varStore_independent_of_constraints
  . rewrite [iff_eq_eq]
    exact EvalSt.evalInOrder_constraints_and

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
  grind [seq]

end Circuit

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
  unfold eval
  unfold Expr.evalWithCache
  simp
  unfold Option.bind
  grind

@[grind <=]
lemma bind_eval' {α : Type} {e!} {varStore : VarStore p} {f : ZMod p → Option α}
                 {σ} (h : [varStore,σ|e!].isSome) :
  [varStore, σ|e!].bind f = f ([varStore, σ|e!].get h) := bind_eval h

end

end ClapM

end Clap
