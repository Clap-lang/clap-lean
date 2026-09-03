import Clap.eDSLState.eDSL

import Clap.Lang.Wheels

/-!
# Converting circuits to their specifications

`Converts` relates a list of `ExprRef`s to the ideal value they denote at a given
`ClapMState`; `ConvertsM` is the Hoare triple that says running a `ClapM` action from a state
produces such references, well-formedly, with satisfied constraints.

The generic combinators at the bottom of this file (`ConvertsM.bind`, `.map`, `.pure`,
`.congr`, `Converts.skip`, `Stable`) are what circuit proofs are written against. They are
stated once, in a shape that unifies against every representation family, rather than copied
per family.

See `docs/CircuitProofs.md` for the rules on how to use them, and
`Clap/eDSLState/ConvertTactic.lean` for the `clap_step` / `clap_finish` tactics.
-/

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

/-!
## Generic combinators

Every representation family (`F`, `FB`, `FUnit`, `FArray k`, `FList`) defines its judgement as

```
X.ConvertsM a state v  ≡  Clap.ConvertsM X.serializeVal (X.toExprs <$> a) state v
```

so a lemma stated in `te <$> action` form unifies against *all* of them: `apply` unfolds the
family `def` at default transparency, and `?te <$> (?a >>= ?f)` is a first-order pattern.
That is why the lemmas below carry `te`/`c` as ordinary unification variables rather than
living behind a typeclass — and why `bind` takes the post-value `vb` free instead of a
`function_val : IA → IB`, which is the unification problem that made the per-family
`convertsM_bind_*` lemmas unusable.

Never copy these per family. Add `toExprs`, `serializeVal` and *structural* lemmas only.
-/

section Combinators

variable
  {p : ℕ}
  {A B IA IB : Type}
  {cA : IA → List (ZMod p)} {cB : IB → List (ZMod p)}
  {teA : A → List ExprRef} {teB : B → List ExprRef}
  {state : ClapMState p}
  {va : IA} {vb : IB}

@[simp, grind =]
lemma getState_pure {x : A} :
  (Pure.pure x : ClapM p A).getState state = state
:= by
  simp [ClapM.getState]

/--
`ClapM.bind_wellFormed` phrased against `ClapM.getState` rather than the three separate
getters, which is the shape every `ConvertsM` proof actually has to hand.
-/
@[grind .]
lemma ClapM.bind_wellFormed'
  {a : ClapM p A} {f : A → ClapM p B}
  (h_a : a.wellFormed state.numAlloc state.varStore state.σ)
  (h_f : (f (a.getResult state.numAlloc state.σ)).wellFormed
    (a.getState state).numAlloc
    (a.getState state).varStore
    (a.getState state).σ
  )
:
  (a >>= f).wellFormed state.numAlloc state.varStore state.σ
:= by
  apply ClapM.bind_wellFormed h_a
  grind [ClapM.getState]

/--
Congruence: `Converts` only ever looks at `conversion` applied to `val`, so it transports
along any equation between two such applications. Subsumes both "same conversion, different
value" and "different conversion, same value".
-/
lemma Converts.congr
  {c c' : IA → List (ZMod p)} {exprs : List ExprRef} {va va' : IA}
  (h : Converts c state exprs va)
  (h_c : c' va' = c va)
:
  Converts c' state exprs va'
where
  h_conversion := by rw [h_c]; exact h.h_conversion
  varSet_wf := h.varSet_wf
  expr_wf := h.expr_wf
  value_eq := fun i => by simp only [h_c]; exact h.value_eq i

/--
Frame rule. A `Converts` fact survives running any well-formed action, so everything you
still need after a monadic step must be phrased as one.
-/
lemma Converts.skip
  {β : Type} {exprs : List ExprRef} {b : ClapM p β}
  (h_wf : b.wellFormed state.numAlloc state.varStore state.σ)
  (h : Converts cA state exprs va)
:
  Converts cA (b.getState state) exprs va
:= toIdeal_run_of_toIdeal _ h_wf h

namespace ConvertsM

/-- `wellFormed` of the underlying action, with the `toExprs` map stripped. -/
lemma wellFormed'
  {a : ClapM p A}
  (h : ConvertsM cA (teA <$> a) state va)
:
  a.wellFormed state.numAlloc state.varStore state.σ
:= (ClapM.map_wellFormed a teA).mp h.wellFormed

/-- `constraints` of the underlying action, with the `toExprs` map stripped. -/
lemma constraints'
  {a : ClapM p A}
  (h : ConvertsM cA (teA <$> a) state va)
:
  (a.runAndEval state.numAlloc state.varStore state.σ).2.constraints
:= Circuit.runAndEval_map_constraints.mp h.constraints

/--
Project the post-state `Converts` fact out of a `ConvertsM`.
Replaces the four copies of `X.converts_of_convertsM`.
-/
lemma converts
  {a : ClapM p A}
  (h : ConvertsM cA (teA <$> a) state va)
:
  Converts cA (a.getState state) (teA (a.getResult state.numAlloc state.σ)) va
:= by
  have := h.result
  simpa using this

/-- Frame rule, taking the step as a `ConvertsM` rather than a bare `wellFormed`. -/
lemma skip
  {exprs : List ExprRef} {b : ClapM p B}
  (h_step : ConvertsM cB (teB <$> b) state vb)
  (h : Converts cA state exprs va)
:
  Converts cA (b.getState state) exprs va
:= Converts.skip h_step.wellFormed' h

/-- Generic `pure`. Replaces `{F,FArray,FList}.convertsM_pure`. -/
lemma pure
  {x : A}
  (h : Converts cA state (teA x) va)
:
  ConvertsM cA (teA <$> (Pure.pure x : ClapM p A)) state va
where
  result := by simpa using h
  wellFormed := by simp
  constraints := by simp [ClapM.runAndEval]

/--
Generic `bind`. Replaces `FB.convertsM_bind_F` and `FArray.convertsM_bind_{F,FB,FArray}`,
and scales to any pair of families instead of one lemma per pair.

Note `vb` is *free*: there is no `function_val : IA → IB` for unification to guess, which is
what makes this usable in a forwards proof.
-/
lemma bind
  {a : ClapM p A} {f : A → ClapM p B}
  (h_a : ConvertsM cA (teA <$> a) state va)
  (h_f : ConvertsM cB (teB <$> f (a.getResult state.numAlloc state.σ)) (a.getState state) vb)
:
  ConvertsM cB (teB <$> (a >>= f)) state vb
:= by
  have hwa := h_a.wellFormed'
  have hwf := h_f.wellFormed'
  constructor
  . simp only [getState_map, ClapM.getResult_map, ClapM.getResult_bind]
    rewrite [getState_bind hwa (by grind [ClapM.getState])]
    exact h_f.converts
  . rewrite [ClapM.map_wellFormed]
    exact ClapM.bind_wellFormed' hwa hwf
  . rewrite [Circuit.runAndEval_map_constraints,
             Circuit.runAndEval_bind_constraints hwa (by grind [ClapM.getState])]
    exact ⟨h_a.constraints', h_f.constraints'⟩

/--
Generic `map`. Replaces `FArray.convertsM_map_FB_FArray` and
`oneHotRaw.convertsM_map_FArray_FArray`.
-/
lemma map
  {a : ClapM p A} {g : A → B}
  (h_a : ConvertsM cA (teA <$> a) state va)
  (h_g : Converts cB (a.getState state) (teB (g (a.getResult state.numAlloc state.σ))) vb)
:
  ConvertsM cB (teB <$> (g <$> a)) state vb
where
  result := by simpa using h_g
  wellFormed := by simp only [ClapM.map_wellFormed]; exact h_a.wellFormed'
  constraints := by
    simp only [Circuit.runAndEval_map_constraints]; exact h_a.constraints'

/--
Congruence, for closing the gap between the spec a circuit naturally produces and the one you
want to state. Prove the mismatch as a separate pure lemma and feed it here.
-/
lemma congr
  {c c' : IA → List (ZMod p)} {te te' : A → List ExprRef}
  {a : ClapM p A} {va va' : IA}
  (h : ConvertsM c (te <$> a) state va)
  (h_te : ∀ x, te' x = te x)
  (h_c : c' va' = c va)
:
  ConvertsM c' (te' <$> a) state va'
:= by
  have : te' = te := funext h_te
  subst this
  exact ⟨h.result.congr h_c, h.wellFormed, h.constraints⟩

/-- The common special case of `ConvertsM.congr`: only the ideal value moves. -/
lemma congr_val
  {a : ClapM p A} {va' : IA}
  (h : ConvertsM cA (teA <$> a) state va)
  (h_c : cA va' = cA va)
:
  ConvertsM cA (teA <$> a) state va'
:= h.congr (fun _ => rfl) h_c

end ConvertsM

/--
A state predicate preserved by running any well-formed action.

This is the frame condition a loop rule needs: `Stable P` says `P` can be carried across
every iteration, so the per-element obligation may assume it. `Converts` facts are the
canonical instance (`Stable.converts`).
-/
def Stable {p : ℕ} (P : ClapMState p → Prop) : Prop :=
  ∀ {β : Type} (b : ClapM p β) (st : ClapMState p),
    b.wellFormed st.numAlloc st.varStore st.σ → P st → P (b.getState st)

namespace Stable

lemma converts {exprs : List ExprRef} :
  Stable (fun st => Converts cA st exprs va)
:= fun _ _ h_wf h => Converts.skip h_wf h

lemma triv : Stable (fun _ : ClapMState p => True) := fun _ _ _ _ => trivial

lemma and {P Q : ClapMState p → Prop} (hP : Stable P) (hQ : Stable Q) :
  Stable (fun st => P st ∧ Q st)
:= fun b st h_wf h => ⟨hP b st h_wf h.1, hQ b st h_wf h.2⟩

lemma all {ι : Type} {P : ι → ClapMState p → Prop} (hP : ∀ i, Stable (P i)) :
  Stable (fun st => ∀ i, P i st)
:= fun b st h_wf h i => hP i b st h_wf (h i)

end Stable

end Combinators

end Clap
