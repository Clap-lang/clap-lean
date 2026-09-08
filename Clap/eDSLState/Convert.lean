import Clap.eDSLState.eDSL

import Clap.Lang.Wheels

namespace Clap

structure Conversion (p : ℕ) (α : Type) where
  IdealT : Type
  conversion : IdealT → List (ZMod p)
  toExprs : α → List ExprRef

-- class HasConversion (p : ℕ) (α : Type) where
--   conversion : α → List (ZMod p)

-- class HasToExprs (α : Type) where
--   toExprs : α → List ExprRef

export Conversion (conversion)

structure ClapMState (p : ℕ) where
  varStore : VarStore p
  σ : HashConsSt p
  numAlloc : ℕ

def ClapM.getState {p} {α} (cmd : ClapM p α) (state : ClapMState p) : ClapMState p where
  varStore := cmd.getVarStore state.varStore state.numAlloc state.σ
  σ := cmd.getHashConsState state.numAlloc state.σ
  numAlloc := cmd.getNumAlloc state.numAlloc state.σ

structure Converts {p : ℕ} {α : Type}
  (conversion : Conversion p α)
  (state : ClapMState p)
  (exprs : α)
  (val : conversion.IdealT)
: Prop where
  h_conversion : (conversion.conversion val).length = (conversion.toExprs exprs).length
  varSet_wf : ∀ (i : Fin (conversion.toExprs exprs).length), ⦃(conversion.toExprs exprs)[i], state.σ⦄.varSet_wellFormed state.numAlloc
  expr_wf   : ∀ (i : Fin (conversion.toExprs exprs).length), ⦃(conversion.toExprs exprs)[i], state.σ⦄.wellFormed
  value_eq  : ∀ (i : Fin (conversion.toExprs exprs).length), [state.varStore|⦃(conversion.toExprs exprs)[i], state.σ⦄] = .some ((conversion.conversion val)[i])

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

section AnotherSection

variable
  {p k : ℕ}
  {α : Type}
  {state : ClapMState p}
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

end AnotherSection

section Lemmas

variable
  {p k : ℕ}
  {α : Type} (conversion : Conversion p α)
  {state : ClapMState p}
  -- {exprs : List ExprRef}
  {val : conversion.IdealT}
  {x : ZMod p}
  {action : ClapM p α}
  {circuit : Circuit}

lemma eval_varStore_eval_eq_some
  {β}
  {action : ClapM p β}
  {exprs : α}
  (h₁ : Converts conversion state exprs val)
  (h₂ : action.hashConsState_wellFormed state.numAlloc state.σ)
:
  letI varStore' := [state.varStore, action.getHashConsState state.numAlloc state.σ, state.numAlloc|circuit]ₑ.varStore
  ∀ i : Fin (conversion.toExprs exprs).length,
    [varStore'|⦃(conversion.toExprs exprs)[i], action.getHashConsState state.numAlloc state.σ⦄] =
    some ((conversion.conversion val)[i]'(by grind [cases Converts]))
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
  {exprs : α}
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
    rw [eval_varStore_eval_eq_some (val := val)]
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
  {exprs : α}
  (h : Converts conversion state exprs val)
  (h_mem : expr ∈ conversion.toExprs exprs)
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
  {exprs : α}
  (h : Converts conversion state exprs val)
  (h_mem : expr ∈ conversion.toExprs exprs)
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
  {exprs : α}
  (h₁ : conversion.toExprs exprs = [expr])
  (h₂ : Converts conversion state exprs val)
:
  [state.varStore, state.σ|expr].isSome = true
:= by
  grind

@[grind .]
lemma expr_wellFormed_of_mem_singleton
  {expr}
  {exprs : α}
  (h₁ : conversion.toExprs exprs = [expr])
  (h : Converts conversion state exprs val)
:
  ⦃expr, state.σ⦄.wellFormed
:= by
  grind

end Lemmas

structure ConvertsM
  {p α}
  (conversion : Conversion p α)
  (action : ClapM p α)
  (state : ClapMState p)
  (val : conversion.IdealT)
: Prop where
  result : Converts
    conversion
    (action.getState state)
    (action.getResult state.numAlloc state.σ)
    val
  wellFormed : action.wellFormed state.numAlloc state.varStore state.σ
  constraints : (action.runAndEval state.numAlloc state.varStore state.σ).2.constraints

lemma converts_skip
  {p α β}
  {conversion₂ : Conversion p β}
  {conversion₁ : Conversion p α}
  {action : ClapM p α}
  {state}
  {val1 : conversion₁.IdealT}
  {val2 : conversion₂.IdealT}
  {exprs : β}
  (h_action : ConvertsM conversion₁ action state val1)
  (h : Converts conversion₂ state exprs val2)
:
  Converts conversion₂ (action.getState state) exprs val2
:= toIdeal_run_of_toIdeal _ _ h_action.wellFormed h

@[aesop safe]
lemma convertsM_pure
  {p α}
  (conversion : Conversion p α)
  {state : ClapMState p}
  {x : α}
  {val : conversion.IdealT}
  (h : Converts conversion state x val)
:
  ConvertsM conversion (pure x) state val
:= by
  constructor
  · simpa
  · grind
  . simp [ClapM.runAndEval]

lemma converts_cast
  {p α β}
  {conversion1 : Conversion p α}
  {conversion2 : Conversion p β}
  {state : ClapMState p}
  {x : α}
  {y : β}
  {val1 : conversion1.IdealT}
  {val2 : conversion2.IdealT}
  (h : Converts conversion1 state x val1)
  (h_ptr : conversion1.toExprs x = conversion2.toExprs y)
  (h_val : conversion1.conversion val1 = conversion2.conversion val2)
:
  Converts conversion2 state y val2
:= by
  constructor
  . intro ⟨i, h_i⟩
    convert h.varSet_wf ⟨i, by grind⟩
    <;> exact h_ptr.symm
  . intro ⟨i, h_i⟩
    convert h.expr_wf ⟨i, by grind⟩
    <;> exact h_ptr.symm
  . intro ⟨i, h_i⟩
    convert h.value_eq ⟨i, by grind⟩
    <;> simp [*]
  . grind [Converts]

lemma convertsM_bind
  {p α β}
  {conversion1 : Conversion p α}
  {conversion2 : Conversion p β}
  {action : ClapM p α}
  {function : α → ClapM p β}
  {state}
  {action_val}
  {function_val}
  (h_action : ConvertsM conversion1 action state action_val)
  (h_function : ConvertsM
    conversion2
    (function (action.getResult state.numAlloc state.σ))
    (action.getState state)
    function_val
  )
:
  ConvertsM conversion2 (action >>= function) state function_val
:= by
  grind [ConvertsM, Converts, ClapM.getState]

lemma convertsM_map
  {p α β}
  {conversion1 : Conversion p α}
  {conversion2 : Conversion p β}
  {action : ClapM p α}
  {f : α → β}
  {state}
  {action_val}
  {function_val}
  (h_action : ConvertsM conversion1 action state action_val)
  (h_function : Converts conversion2 (action.getState state) (f (action.getResult state.numAlloc state.σ)) function_val)
:
  ConvertsM conversion2 (f <$> action) state function_val
:= by
  constructor
  . grind
  . grind [ConvertsM]
  . grind [ConvertsM]

-- It's back!
-- Useful specifically in case convert gets overeager
lemma converts_of_converts
  {p α}
  {conversion : Conversion p α}
  {state}
  {exprs}
  {val1 val2}
  (h: Converts conversion state exprs val1)
  (h_eq : val1 = val2)
:
  Converts conversion state exprs val2
:= by
  rewrite [h_eq] at h
  exact h

end Clap
