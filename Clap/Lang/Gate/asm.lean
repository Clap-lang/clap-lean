import Clap.Lang.Gate.num2bits

namespace Clap.Lang

variable {p : ℕ}

def asm (spec : LawfulGateSpec p)
        (inputs : FVec p spec.numInputs) : ClapM p (FVec p spec.numPublic) :=
  Clap.asm spec inputs

namespace asm

variable {spec : LawfulGateSpec p} {state : ClapMState p}
         {inputs : FVec p spec.numInputs} {inputs' : Vector (ZMod p) spec.numInputs}

private lemma converts_of_mem (h : Converts FVec.conversion state inputs inputs') {e : F p}
  (he : e ∈ inputs) : ∃ v, Converts F.conversion state e v := by
  obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp he
  exact ⟨_, FVec.converts_iff_F_converts.mp h ⟨i, hi⟩⟩

lemma wellFormed (h : Converts FVec.conversion state inputs inputs') :
  (asm spec inputs).wellFormed state.numAlloc state.varStore state.σ := by
  unfold asm
  apply Clap.wellFormed_asm
  all_goals
    intro e he
    obtain ⟨v, ⟨h_varSet, h_wellFormed, h_result⟩⟩ := converts_of_mem h he
    simp at *
  · grind
  · have : [state.varStore|⦃e, state.σ⦄].isSome = true := by grind
    grind
  · grind

private lemma eval_frame {e : F p} {v : ZMod p} {σ' : HashConsSt p}
  (h : Converts F.conversion state e v) (h_prefix : state.σ.exprs.isPrefixOf σ'.exprs) :
  [state.varStore|⦃e, σ'⦄] = some v := by
  have h_eq : [state.varStore|⦃e, state.σ⦄] = some v := by
    have := h.value_eq; simpa using this
  have h_wf : (Expr.mk e state.σ).wellFormed := by
    have := h.expr_wf; simpa using this
  rw [eval_eq_evalRec (Expr.wellFormed_frame (e' := Expr.mk e σ') h_wf h_prefix rfl),
      ←evalRec_of_wellFormed_of_prefix h_prefix h_wf, ←eval_eq_evalRec h_wf, h_eq]

private lemma map_eval_eq (h : Converts FVec.conversion state inputs inputs') {σ' : HashConsSt p}
  (h_prefix : state.σ.exprs.isPrefixOf σ'.exprs) :
  inputs.map (fun e ↦ [state.varStore|⦃e, σ'⦄].getD 0) = inputs' := by
  ext i hi
  have hv := FVec.converts_iff_F_converts.mp h ⟨i, hi⟩
  simp only [Fin.getElem_fin] at hv
  rw [Vector.getElem_map, eval_frame hv h_prefix]
  rfl

lemma converts (h : Converts FVec.conversion state inputs inputs') :
  Converts FVec.conversion
    ((asm spec inputs).getState state)
    ((asm spec inputs).getResult state.numAlloc state.σ)
    (spec.outputs inputs') := by
  rw [FVec.converts_iff_F_converts]
  intro i
  have h_result :
    (asm spec inputs).getResult state.numAlloc state.σ =
    (Vector.ofFnM (fun (_ : Fin spec.numPublic) => (ClapM.alloc : ClapM p ExprRef))).getResult
      state.numAlloc state.σ
  := by unfold asm; exact Clap.getResult_asm
  have h_σ :
    ((asm spec inputs).getState state).σ =
    (Vector.ofFnM (fun (_ : Fin spec.numPublic) => (ClapM.alloc : ClapM p ExprRef))).getHashConsState
      state.numAlloc state.σ
  := by unfold asm Clap.asm ClapM.getState; simp
  have h_numAlloc :
    ((asm spec inputs).getState state).numAlloc = state.numAlloc + spec.numPublic
  := by unfold asm Clap.asm ClapM.getState; simp [Clap.getNumAlloc_Vector_ofFnM_alloc]
  have h_map := map_eval_eq h (σ' :=
    (Vector.ofFnM (fun (_ : Fin spec.numPublic) => (ClapM.alloc : ClapM p ExprRef))).getHashConsState
      state.numAlloc state.σ) isPrefixOf_getHashConsState_Vector_ofFnM_alloc
  have h_varStore :
    ((asm spec inputs).getState state).varStore[state.numAlloc + i.val]? =
    some ((spec.outputs inputs')[i])
  := by
    unfold asm ClapM.getState
    simp only [Clap.getVarStore_asm, h_map]
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
  have h_deref :=
    num2bits.key_getElem_ofFnM_alloc (w := spec.numPublic) (numAlloc := state.numAlloc)
      (σ := state.σ) i
  have h_wf :
    (Expr.mk
      ((Vector.ofFnM (fun (_ : Fin spec.numPublic) => (ClapM.alloc : ClapM p ExprRef))).getResult
        state.numAlloc state.σ)[i.val]
      ((Vector.ofFnM (fun (_ : Fin spec.numPublic) => (ClapM.alloc : ClapM p ExprRef))).getHashConsState
        state.numAlloc state.σ)
    ).wellFormed
  := Expr.wellFormed_iff_isSome.mpr (by rw [h_deref]; rfl)
  have h_eval :
    [((asm spec inputs).getState state).varStore|⟨
      ((Vector.ofFnM (fun (_ : Fin spec.numPublic) => (ClapM.alloc : ClapM p ExprRef))).getResult
        state.numAlloc state.σ)[i.val],
      (Vector.ofFnM (fun (_ : Fin spec.numPublic) => (ClapM.alloc : ClapM p ExprRef))).getHashConsState
        state.numAlloc state.σ⟩] =
    some ((spec.outputs inputs')[i])
  := by rw [eval_eq_evalRec h_wf, evalRec_eq_of_deref_eq_some_v h_deref]; exact h_varStore
  rw [h_result]
  refine ⟨by simp, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · simp only [F.conversion, Fin.getElem_fin] at j ⊢
    rw [h_σ, h_numAlloc]
    grind [Expr.varSet, Expr.varSet_wellFormed]
  · simp only [F.conversion] at j ⊢
    rw [h_σ]
    grind
  · have hj : j = 0 := Fin.eq_zero j
    subst hj
    simp only [F.conversion, List.getElem_cons_zero, Fin.getElem_fin, Fin.val_zero]
    rw [h_σ, h_eval]
    simp

lemma constraints (h : Converts FVec.conversion state inputs inputs') :
  ((asm spec inputs).runAndEval state.numAlloc state.varStore state.σ).2.constraints ↔
  spec.inputProp inputs' := by
  have h_prefix := isPrefixOf_getHashConsState_Vector_ofFnM_alloc (k := spec.numPublic)
    (numAlloc := state.numAlloc) (σ := state.σ)
  unfold asm
  rw [Clap.eval_edsl_asm, EvalSt.constraints_stepAsm]
  simp only [EvalSt.constraints_unconstrained, EvalSt.membership_unconstrained,
    EvalSt.getElem?_unconstrained, true_and, GateSpec.assertions, map_eval_eq h h_prefix]
  refine ⟨And.right, fun h_prop ↦ ⟨fun e he ↦ ?_, h_prop⟩⟩
  obtain ⟨v, hv⟩ := converts_of_mem h he
  rw [eval_frame hv h_prefix]
  rfl

lemma convertsM
  (h : Converts FVec.conversion state inputs inputs') :
  ConvertsM FVec.conversion
    (asm spec inputs)
    state
    (spec.outputs inputs')
    (spec.inputProp inputs')
where
  result := converts h
  wellFormed := wellFormed h
  constraints := constraints h

end asm

end Clap.Lang
