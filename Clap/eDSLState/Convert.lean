import Clap.eDSLState.eDSL

import Clap.Lang.Wheels

namespace Clap

structure ClapMState (p : ℕ) where
  varStore : VarStore p
  σ : HashConsSt p
  numAlloc : ℕ

def ClapM.getState {p} {α} (cmd : ClapM p α) (state : ClapMState p) : ClapMState p where
  varStore := cmd.getVarStore state.varStore state.numAlloc state.σ
  σ := cmd.getHashConsState state.numAlloc state.σ
  numAlloc := cmd.getNumAlloc state.numAlloc state.σ

structure Converts {p : ℕ} {α : Type}
  (conversion : α → List (ZMod p))
  (state : ClapMState p)
  (exprs : List ExprRef)
  (val : α)
: Prop where
  h_conversion : (conversion val).length = exprs.length
  varSet_wf : ∀ (i : Fin exprs.length), ⦃exprs[i], state.σ⦄.varSet_wellFormed state.numAlloc
  expr_wf   : ∀ (i : Fin exprs.length), ⦃exprs[i], state.σ⦄.wellFormed
  value_eq  : ∀ (i : Fin exprs.length), [state.varStore|⦃exprs[i], state.σ⦄] = .some ((conversion val)[i])

-- structure HasSpec {p} {idealT} {representsT} (action : ClapM p representsT) where
--   spec : idealT
--   converts : Converts k conversion varStore σ numAlloc exprs spec

/-
isZero.hasSpec a := {
  spec := a == 0
  converts : FB.ConvertsM (isZero a) spec
}

(a >>= f).spec = something

-/

section Lemmas

variable
  {p k : ℕ}
  {α : Type}
  {conversion : α → List (ZMod p)}
  {state : ClapMState p}
  {exprs : List ExprRef}
  {val : α}
  {x : ZMod p}
  {action : ClapM p α}
  {circuit : Circuit}

@[simp, grind =]
lemma getState_map
  {β}
  {f : α → β}
:
  (f <$> action).getState state =
  action.getState state
:= by
  grind [ClapM.getState]

@[grind =]
lemma getState_bind
  {β}
  {function : α → ClapM p β}
  (h_action : action.wellFormed state.numAlloc state.varStore state.σ)
  (h_function : (function (action.getResult state.numAlloc state.σ)).wellFormed
    (action.getState state).numAlloc
    (action.getState state).varStore
    (action.getState state).σ
  )
:
  (action >>= function).getState state =
  (function (action.getResult state.numAlloc state.σ)).getState (action.getState state)
:= by
  grind [ClapM.getState]


lemma eval_varStore_eval_eq_some
  {β}
  {action : ClapM p β}
  (h₁ : Converts conversion state exprs val)
  (h₂ : action.hashConsState_wellFormed state.numAlloc state.σ)
:
  letI varStore' := [state.varStore, action.getHashConsState state.numAlloc state.σ, state.numAlloc|circuit]ₑ.varStore
  ∀ i : Fin exprs.length,
    [varStore'|⦃exprs[i], action.getHashConsState state.numAlloc state.σ⦄] =
    some ((conversion val)[i]'(by grind [cases Converts]))
:= by
  intros i
  rcases circuit with ⟨l⟩
  induction' eq : l.length with len ih generalizing l
  · rcases l <;> grind [Converts]
  · rcases l with _ | ⟨hd, tl⟩
    · simp at eq
    · simp [-Fin.getElem_fin]
      specialize ih tl (by grind)
      rewrite [←ih]; clear ih
      apply eval_eq_of_varStore_eq_at_varSet
      . grind [Converts]
      . intro v h_v
        set vashtorr := [unconstrained[state.numAlloc][state.varStore], action.getHashConsState state.numAlloc state.σ|hd]ₛ.varStore
        rewrite [Circuit.getElem?_eval_eq_getElem?_of_lt (by grind [Converts])]
        rewrite [Circuit.getElem?_eval_eq_getElem?_of_lt (by grind [Converts])]
        choose k vec h_vec using @EvalSt.exists_varStore_step_eq_insertMany
        simp [vashtorr, h_vec.1]
        rw [Std.ExtTreeMap.getElem?_insertMany_eq_getElem?_of_neq]
        grind [Converts]

lemma toIdeal_run_of_toIdeal
  {β}
  (action : ClapM p β)
  (h_a_wf : action.wellFormed state.numAlloc state.varStore state.σ)
  (h : Converts conversion state exprs val) :
  Converts
           conversion
           (action.getState state)
           exprs
           val := by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  constructor
  · grind [=Expr.varSet_wellFormed, ClapM.getState]
  · grind [ClapM.getState]
  · intro i
    unfold ClapM.getState ClapM.getVarStore
    rw [eval_varStore_eval_eq_some (conversion := conversion) (val := val)]
    . constructor
      . assumption
      . assumption
      . assumption
      . assumption
    . grind
  . assumption

@[grind .]
lemma isSome_eval_of_mem
  {expr}
  (h : Converts conversion state exprs val)
  (h_mem : expr ∈ exprs)
:
  [state.varStore, state.σ|expr].isSome = true
:= by
  obtain ⟨_, _, _, h_value⟩ := h
  obtain ⟨i, h_i, h_expr⟩ := List.getElem_of_mem h_mem
  apply Option.isSome_of_eq_some
  rewrite [←h_value ⟨i, by grind⟩]
  grind

@[grind .]
lemma expr_wellFormed_of_mem
  {expr}
  (h : Converts conversion state exprs val)
  (h_mem : expr ∈ exprs)
:
  ⦃expr, state.σ⦄.wellFormed
:= by
  obtain ⟨_, _, h_wf, _⟩ := h
  obtain ⟨i, h_i, h_expr⟩ := List.getElem_of_mem h_mem
  grind [h_wf ⟨i, by grind⟩]

@[grind .]
lemma isSome_eval_singleton
  {state : ClapMState p}
  {expr : ExprRef}
  (h : Converts conversion state [expr] val)
:
  [state.varStore, state.σ|expr].isSome = true
:= by
  grind

@[grind .]
lemma expr_wellFormed_of_mem_singleton
  {expr}
  (h : Converts conversion state [expr] val)
:
  ⦃expr, state.σ⦄.wellFormed
:= by
  grind


end Lemmas

structure ConvertsM
  {p IdealT}
  (conversion : IdealT → List (ZMod p))
  (action : ClapM p (List ExprRef))
  (state : ClapMState p)
  (val : IdealT)
: Prop where
  result : Converts
    conversion
    (action.getState state)
    (action.getResult state.numAlloc state.σ)
    val
  wellFormed : action.wellFormed state.numAlloc state.varStore state.σ
  constraints : (action.runAndEval state.numAlloc state.varStore state.σ).2.constraints

lemma converts_skip
  {p IdealT1 IdealT2}
  {conversion1 conversion2}
  {action : ClapM p (List ExprRef)}
  {state}
  {val1 : IdealT1}
  {val2 : IdealT2}
  {exprs}
  (h_action : ConvertsM conversion1 action state val1)
  (h : Converts conversion2 state exprs val2)
:
  Converts conversion2 (action.getState state) exprs val2
:= toIdeal_run_of_toIdeal _ h_action.wellFormed h

end Clap
