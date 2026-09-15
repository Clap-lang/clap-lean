import Clap.eDSLState.Convert.Specialised

namespace Clap.Lang

variable {p : ℕ}

def num2bits (w : ℕ) (e : F p) : ClapM p (FArray p w) :=
  Clap.num2bits w e

namespace num2bits

lemma wellFormed {e! : ExprRef} {state} {value : ZMod p} {w : ℕ}
  (h : Converts F.conversion state e! value)
:
  (num2bits w e!).wellFormed state.numAlloc state.varStore state.σ
:= by
  unfold num2bits
  obtain ⟨h_varSet, h_wellFormed, h_result⟩ := h
  simp at *
  apply Clap.wellFormed_num2bits
  . grind
  . have : [state.varStore|⦃e!, state.σ⦄].isSome = true := by grind
    grind
  . grind

/-- Dereferencing is stable along a heap prefix, for a ref that was already well-formed. -/
private lemma deref_frame {e e' : Expr p}
  (h₁ : e.wellFormed) (h₂ : e.σ.exprs.isPrefixOf e'.σ.exprs) (h₃ : e.ref = e'.ref) :
  *e' = *e
:= by
  have : e.σ.exprs.toList.isPrefixOf e'.σ.exprs.toList = true := by grind
  grind [List.prefix_iff_getElem?, =Expr.deref]

private lemma num2bitsLsbPureV_aux_mem {n : ℕ} :
  ∀ {f : ZMod p} {x}, x ∈ num2bitsLsbPureV.aux n f → x = 0 ∨ x = 1
:= by
  induction n with
  | zero => intro f x hx; simp [num2bitsLsbPureV.aux] at hx
  | succ n ih =>
    intro f x hx
    unfold num2bitsLsbPureV.aux at hx
    rw [Vector.mem_push] at hx
    rcases hx with hx | hx
    · exact ih hx
    · rcases Nat.mod_two_eq_zero_or_one f.val with h | h <;> simp [hx, h]

/-- Every entry of `num2bitsLsbPureV` is a bit. -/
private lemma num2bitsLsbPureV_mem {n : ℕ} {f : ZMod p} :
  ∀ x ∈ num2bitsLsbPureV n f, x = 0 ∨ x = 1
:= by
  intro x hx
  unfold num2bitsLsbPureV at hx
  rw [Vector.mem_reverse] at hx
  exact num2bitsLsbPureV_aux_mem hx

/--
The `i`-th of the `w` freshly-allocated variables produced by `Vector.ofFnM (fun _ => ClapM.alloc)`
dereferences (against the final heap) to exactly the fresh variable node `numAlloc + i`.
-/
lemma key_getElem_ofFnM_alloc {w : ℕ} :
  ∀ {numAlloc : ℕ} {σ : HashConsSt p} (i : Fin w),
  *(Expr.mk
    ((Vector.ofFnM (fun (_ : Fin w) => (ClapM.alloc : ClapM p ExprRef))).getResult numAlloc σ)[i.val]
    ((Vector.ofFnM (fun (_ : Fin w) => (ClapM.alloc : ClapM p ExprRef))).getHashConsState numAlloc σ)
  ) = some (CacheExpr.v (numAlloc + i.val))
:= by
  induction w with
  | zero => intro numAlloc σ i; exact i.elim0
  | succ w ih =>
    intro numAlloc σ i
    simp only [Vector.ofFnM_succ, ClapM.getResult_bind, ClapM.getHashConsState_bind,
      ClapM.getResult_pure, ClapM.getHashConsState_pure,
      Clap.getNumAlloc_Vector_ofFnM_alloc]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp only [Fin.val_castSucc, Vector.getElem_push_lt (show j.val < w by omega)]
      have h_deref := ih (numAlloc := numAlloc) (σ := σ) j
      have h_wf :
        (Expr.mk
          (((Vector.ofFnM (fun (_ : Fin w) => (ClapM.alloc : ClapM p ExprRef))).getResult numAlloc σ)[j.val])
          ((Vector.ofFnM (fun (_ : Fin w) => (ClapM.alloc : ClapM p ExprRef))).getHashConsState numAlloc σ)
        ).wellFormed
      := Expr.wellFormed_iff_isSome.mpr (by rw [h_deref]; rfl)
      have h_prefix :
        ((Vector.ofFnM (fun (_ : Fin w) => (ClapM.alloc : ClapM p ExprRef))).getHashConsState numAlloc σ).exprs.isPrefixOf
        ((ClapM.alloc : ClapM p ExprRef).getHashConsState (numAlloc + w)
          ((Vector.ofFnM (fun (_ : Fin w) => (ClapM.alloc : ClapM p ExprRef))).getHashConsState numAlloc σ)).exprs
      := Clap.isPrefixOf_mkVar
      have h_deref' :
        *(Expr.mk
            (((Vector.ofFnM (fun (_ : Fin w) => (ClapM.alloc : ClapM p ExprRef))).getResult numAlloc σ)[j.val])
            ((ClapM.alloc : ClapM p ExprRef).getHashConsState (numAlloc + w)
              ((Vector.ofFnM (fun (_ : Fin w) => (ClapM.alloc : ClapM p ExprRef))).getHashConsState numAlloc σ))
        ) = some (CacheExpr.v (numAlloc + j.val))
      := by
        rw [deref_frame (e' :=
          Expr.mk
            (((Vector.ofFnM (fun (_ : Fin w) => (ClapM.alloc : ClapM p ExprRef))).getResult numAlloc σ)[j.val])
            ((ClapM.alloc : ClapM p ExprRef).getHashConsState (numAlloc + w)
              ((Vector.ofFnM (fun (_ : Fin w) => (ClapM.alloc : ClapM p ExprRef))).getHashConsState numAlloc σ)))
          h_wf h_prefix rfl]
        exact h_deref
      exact h_deref'
    · simp only [Fin.val_last, Vector.getElem_push_eq]
      exact Expr.deref_mkVar_eq_some

lemma converts
  {state} {w : ℕ} {e : F p} {e_val : ZMod p}
  (h_e : Converts F.conversion state e e_val)
:
  Converts FArray.conversion
    ((num2bits w e).getState state)
    ((num2bits w e).getResult state.numAlloc state.σ)
    (num2bitsLsbPureV w e_val |>.map fun x ↦ x == 1)
:= by
  rw [FArray.converts_iff_FB_converts]
  intro i
  have h_result :
    (num2bits w e).getResult state.numAlloc state.σ =
    (Vector.ofFnM (fun (_ : Fin w) => (ClapM.alloc : ClapM p ExprRef))).getResult state.numAlloc state.σ
  := by unfold num2bits; exact Clap.getResult_num2bits
  have h_σ :
    ((num2bits w e).getState state).σ =
    (Vector.ofFnM (fun (_ : Fin w) => (ClapM.alloc : ClapM p ExprRef))).getHashConsState state.numAlloc state.σ
  := by unfold num2bits Clap.num2bits ClapM.getState; simp
  have h_numAlloc :
    ((num2bits w e).getState state).numAlloc = state.numAlloc + w
  := by unfold num2bits Clap.num2bits ClapM.getState; simp [Clap.getNumAlloc_Vector_ofFnM_alloc]
  have h_e_eq : [state.varStore|⦃e, state.σ⦄] = some e_val := by
    have := h_e.value_eq; simpa using this
  have h_e_wf : (Expr.mk e state.σ).wellFormed := by
    have := h_e.expr_wf; simpa using this
  have h_e_prefix :
    state.σ.exprs.isPrefixOf ((Clap.num2bits w e).getHashConsState state.numAlloc state.σ).exprs
  := by unfold Clap.num2bits; simp
  have h_e_eq' :
    [state.varStore|⦃e, (Clap.num2bits w e).getHashConsState state.numAlloc state.σ⦄] = some e_val
  := by
    rw [eval_eq_evalRec (Expr.wellFormed_frame
          (e' := Expr.mk e ((Clap.num2bits w e).getHashConsState state.numAlloc state.σ))
          h_e_wf h_e_prefix rfl),
        ←evalRec_of_wellFormed_of_prefix h_e_prefix h_e_wf, ←eval_eq_evalRec h_e_wf, h_e_eq]
  have h_varStore :
    ((num2bits w e).getState state).varStore[state.numAlloc + i.val]? =
    some ((num2bitsLsbPureV w e_val)[i])
  := by
    unfold num2bits ClapM.getState ClapM.getVarStore
    simp [Clap.getCircuit_num2bits, h_e_eq']
    rw [Std.ExtTreeMap.insertMany_vector_list]
    apply Std.ExtTreeMap.getElem?_insertMany_list_of_mem (k := state.numAlloc + i.val) (by simp)
    · rw [List.pairwise_iff_getElem]
      intro a b ha hb hab
      simp
      omega
    · rw [List.mem_iff_getElem]
      refine ⟨i.val, by simp, ?_⟩
      simp
      omega
  have h_deref := key_getElem_ofFnM_alloc (w := w) (numAlloc := state.numAlloc) (σ := state.σ) i
  have h_wf :
    (Expr.mk
      ((Vector.ofFnM (fun (_ : Fin w) => (ClapM.alloc : ClapM p ExprRef))).getResult state.numAlloc state.σ)[i.val]
      ((Vector.ofFnM (fun (_ : Fin w) => (ClapM.alloc : ClapM p ExprRef))).getHashConsState state.numAlloc state.σ)
    ).wellFormed
  := Expr.wellFormed_iff_isSome.mpr (by rw [h_deref]; rfl)
  have h_eval :
    [((num2bits w e).getState state).varStore|⟨
      ((Vector.ofFnM (fun (_ : Fin w) => (ClapM.alloc : ClapM p ExprRef))).getResult state.numAlloc state.σ)[i.val],
      (Vector.ofFnM (fun (_ : Fin w) => (ClapM.alloc : ClapM p ExprRef))).getHashConsState state.numAlloc state.σ⟩] =
    some ((num2bitsLsbPureV w e_val)[i])
  := by rw [eval_eq_evalRec h_wf, evalRec_eq_of_deref_eq_some_v h_deref]; exact h_varStore
  rw [h_result]
  refine ⟨by simp, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · simp only [FB.conversion, Fin.getElem_fin] at j ⊢
    rw [h_σ, h_numAlloc]
    grind [Expr.varSet, Expr.varSet_wellFormed]
  · simp only [FB.conversion] at j ⊢
    rw [h_σ]
    grind
  · have hj : j = 0 := Fin.eq_zero j
    subst hj
    simp only [FB.conversion, List.getElem_cons_zero, Fin.getElem_fin, Fin.val_zero]
    rw [h_σ, h_eval]
    have h_bit := num2bitsLsbPureV_mem (n := w) (f := e_val) ((num2bitsLsbPureV w e_val)[i.val])
      (Vector.getElem_mem (xs := num2bitsLsbPureV w e_val) (i := i.val) i.isLt)
    by_cases h : (num2bitsLsbPureV w e_val)[i] = 1 <;> simp_all

lemma constraints
  {state : ClapMState p} {w : ℕ} {e} {e_val}
  (h_e : Converts F.conversion state e e_val)
:
  ((num2bits w e).runAndEval state.numAlloc state.varStore state.σ).2.constraints
:= by
  unfold num2bits Clap.num2bits
  simp [ClapM.runAndEval]
  have : [state.varStore|⦃e, state.σ⦄].isSome := by grind
  exact isSome_eval_of_prefix (by grind [cases Converts]) this (by rfl) (by grind)

lemma convertsM
  {state}
  {w : ℕ}
  {e : F p}
  {e_val : ZMod p}
  (h_e : Converts F.conversion state e e_val)
  :
  ConvertsM FArray.conversion
    (num2bits w e)
    state
    (num2bitsLsbPureV w e_val |>.map fun x ↦ x == 1)
    True
where
  result := converts h_e
  wellFormed := wellFormed h_e
  constraints := iff_true_intro (constraints h_e)

end num2bits

end Clap.Lang
