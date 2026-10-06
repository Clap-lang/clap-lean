import Clap.Lang.Gate.num2bits
import Clap.Util.Limbs

namespace Clap.Lang

variable {p : ℕ}

namespace Limbs

/-- `k` limbs of `w` bits, least significant first, read as the natural number they encode. -/
abbrev conversion (w k : ℕ) : Conversion p (FVec p k) where
  IdealT := ℕ
  toExprs x := x.toList
  conversion n := natToLimbs w k n

variable {w k : ℕ} {state : ClapMState p} {x : FVec p k}

lemma converts_FVec {n : ℕ} (h : Converts (conversion w k) state x n) :
  Converts FVec.conversion state x (natToLimbsV p w k n)
:= converts_cast h rfl rfl

lemma converts_of_FVec {n : ℕ} (h : Converts FVec.conversion state x (natToLimbsV p w k n)) :
  Converts (conversion w k) state x n
:= converts_cast h rfl rfl

/-- An `FVec` whose limbs are all below `2^w` converts to the number they encode. -/
lemma converts_of_FVec_lt [NeZero p] {vals : Vector (ZMod p) k}
  (h : Converts FVec.conversion state x vals) (h_vals : ∀ i : Fin k, vals[i].val < 2 ^ w) :
  Converts (conversion w k) state x (limbsToNat w vals.toList)
:= converts_cast h rfl (by
    have := natToLimbs_limbsToNat (w := w) (l := vals.toList) (by
      intro y hy
      obtain ⟨i, h_i, rfl⟩ := List.getElem_of_mem hy
      simpa using h_vals ⟨i, by simpa using h_i⟩)
    simpa using this.symm)

lemma converts_getElem {n i : ℕ} (h : Converts (conversion w k) state x n) (h_i : i < k) :
  Converts F.conversion state x[i] (natToLimbsV p w k n)[i]
:= FVec.converts_getElem (converts_FVec h) h_i

/-- Values that agree modulo `2^(w*k)` convert alike. -/
lemma converts_congr {a b : ℕ} (h_ab : a % 2 ^ (w * k) = b % 2 ^ (w * k))
  (h : Converts (conversion w k) state x a) :
  Converts (conversion w k) state x b
:= converts_cast h rfl (natToLimbs_congr h_ab)

lemma convertsM_congr {action : ClapM p (FVec p k)} {a b : ℕ} {constraints : Prop}
  (h_ab : a % 2 ^ (w * k) = b % 2 ^ (w * k))
  (h : ConvertsM (conversion w k) action state a constraints) :
  ConvertsM (conversion w k) action state b constraints
:= ⟨converts_congr h_ab h.result, h.wellFormed, h.constraints⟩

end Limbs

/-- `a * b mod p'` on bignums of `k` limbs of `w` bits, least significant limb first.
Satisfiable exactly when every limb of `a`, `b` and `p'` is below `2^w` and `p'` is nonzero. -/
def fpmul (w k : ℕ) (a b p' : FVec p k) : ClapM p (FVec p k) :=
  Clap.fpmul w k a b p'

namespace fpmul

variable {w k : ℕ} {state : ClapMState p} {a b p' : FVec p k}
  {a_vals b_vals p'_vals : Vector (ZMod p) k}

/-- A converting `e` keeps its value against any extension of its heap. -/
private lemma eval_frame {e : F p} {e_val : ZMod p} {σ' : HashConsSt p}
  (h_e : Converts F.conversion state e e_val) (h_prefix : state.σ.exprs.isPrefixOf σ'.exprs)
:
  [state.varStore|⦃e, σ'⦄] = some e_val
:= by
  have h_e_eq : [state.varStore|⦃e, state.σ⦄] = some e_val := by
    have := h_e.value_eq; simpa using this
  have h_e_wf : (Expr.mk e state.σ).wellFormed := by
    have := h_e.expr_wf; simpa using this
  rw [eval_eq_evalRec (Expr.wellFormed_frame (e' := Expr.mk e σ') h_e_wf h_prefix rfl),
      ←evalRec_of_wellFormed_of_prefix h_prefix h_e_wf, ←eval_eq_evalRec h_e_wf, h_e_eq]

/-- The three facts `wellFormed_fpmul` asks of each operand. -/
private lemma gateOperand_of_converts {e : F p} {e_val : ZMod p}
  (h : Converts F.conversion state e e_val)
:
  e < state.σ.size ∧ (∀ v ∈ Expr.varSet ⟨e, state.σ⟩, v ∈ state.varStore) ∧
    Expr.varSet_wellFormed ⟨e, state.σ⟩ state.numAlloc
:= by
  obtain ⟨_, h_varSet, h_wellFormed, h_result⟩ := h
  simp at *
  refine ⟨by grind, ?_, by grind⟩
  have : [state.varStore|⦃e, state.σ⦄].isSome = true := by grind
  grind

/-- Output `i` of the gate's `k` allocations converts to whatever it stored at `numAlloc + i`. -/
private lemma converts_ofFnM_alloc_getElem
  {state' : ClapMState p} {vals : Vector (ZMod p) k}
  (h_σ : state'.σ =
    (Vector.ofFnM fun (_ : Fin k) ↦ (ClapM.alloc : ClapM p ExprRef)).getHashConsState
      state.numAlloc state.σ)
  (h_numAlloc : state'.numAlloc = state.numAlloc + k)
  (h_varStore : ∀ i : Fin k, state'.varStore[state.numAlloc + i.val]? = some vals[i])
  (i : Fin k)
:
  Converts F.conversion state'
    ((Vector.ofFnM fun (_ : Fin k) ↦ (ClapM.alloc : ClapM p ExprRef)).getResult
      state.numAlloc state.σ)[i]
    vals[i]
:= by
  have h_deref :=
    num2bits.key_getElem_ofFnM_alloc (w := k) (numAlloc := state.numAlloc) (σ := state.σ) i
  have h_wf :
    (Expr.mk
      ((Vector.ofFnM (fun (_ : Fin k) => (ClapM.alloc : ClapM p ExprRef))).getResult state.numAlloc state.σ)[i.val]
      ((Vector.ofFnM (fun (_ : Fin k) => (ClapM.alloc : ClapM p ExprRef))).getHashConsState state.numAlloc state.σ)
    ).wellFormed
  := Expr.wellFormed_iff_isSome.mpr (by rw [h_deref]; rfl)
  have h_eval :
    [state'.varStore|⟨
      ((Vector.ofFnM (fun (_ : Fin k) => (ClapM.alloc : ClapM p ExprRef))).getResult state.numAlloc state.σ)[i.val],
      (Vector.ofFnM (fun (_ : Fin k) => (ClapM.alloc : ClapM p ExprRef))).getHashConsState state.numAlloc state.σ⟩] =
    some vals[i]
  := by rw [eval_eq_evalRec h_wf, evalRec_eq_of_deref_eq_some_v h_deref]; exact h_varStore i
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
    rfl

private lemma operands {x : FVec p k} {x_vals : Vector (ZMod p) k}
  (h : Converts FVec.conversion state x x_vals)
:
  (∀ e ∈ x, e < state.σ.size) ∧
  (∀ e ∈ x, ∀ v ∈ Expr.varSet ⟨e, state.σ⟩, v ∈ state.varStore) ∧
  (∀ e ∈ x, Expr.varSet_wellFormed ⟨e, state.σ⟩ state.numAlloc)
:= by
  have hx : ∀ e ∈ x, e < state.σ.size ∧ (∀ v ∈ Expr.varSet ⟨e, state.σ⟩, v ∈ state.varStore) ∧
      Expr.varSet_wellFormed ⟨e, state.σ⟩ state.numAlloc := by
    intro e he
    obtain ⟨i, h_i, rfl⟩ := Vector.mem_iff_getElem.mp he
    exact gateOperand_of_converts (FVec.converts_getElem h h_i)
  exact ⟨fun e he ↦ (hx e he).1, fun e he ↦ (hx e he).2.1, fun e he ↦ (hx e he).2.2⟩

/-- The heap right after the gate's allocations, against which its operands are read. -/
private abbrev σ' (state : ClapMState p) (k : ℕ) : HashConsSt p :=
  (Vector.ofFnM fun (_ : Fin k) ↦ (ClapM.alloc : ClapM p ExprRef)).getHashConsState
    state.numAlloc state.σ

/-- An operand read against the post-allocation heap gives back its values. -/
private lemma lookup_eq {x : FVec p k} {x_vals : Vector (ZMod p) k}
  (h : Converts FVec.conversion state x x_vals)
:
  x.map (fun e ↦ [state.varStore|⦃e, σ' state k⦄].getD 0) = x_vals
:= by
  ext i h_i
  simp [eval_frame (FVec.converts_getElem h h_i) isPrefixOf_getHashConsState_Vector_ofFnM_alloc]

/-- The gate's pure semantics is `natToLimbs` of the product modulo the modulus. -/
private lemma fpMulPureV_eq :
  EvalSt.fpMulPureV w k a_vals b_vals p'_vals =
  natToLimbsV p w k
    (limbsToNat w a_vals.toList * limbsToNat w b_vals.toList % limbsToNat w p'_vals.toList)
:= by
  simp only [EvalSt.fpMulPureV, limbsToNat_toList_eq_sum]

lemma wellFormed
  (h_a : Converts FVec.conversion state a a_vals)
  (h_b : Converts FVec.conversion state b b_vals)
  (h_p' : Converts FVec.conversion state p' p'_vals)
:
  (fpmul w k a b p').wellFormed state.numAlloc state.varStore state.σ
:= by
  obtain ⟨a₁, a₂, a₃⟩ := operands h_a
  obtain ⟨b₁, b₂, b₃⟩ := operands h_b
  obtain ⟨c₁, c₂, c₃⟩ := operands h_p'
  exact Clap.wellFormed_fpmul a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃

lemma converts
  (h_a : Converts FVec.conversion state a a_vals)
  (h_b : Converts FVec.conversion state b b_vals)
  (h_p' : Converts FVec.conversion state p' p'_vals)
:
  Converts (Limbs.conversion w k)
    ((fpmul w k a b p').getState state)
    ((fpmul w k a b p').getResult state.numAlloc state.σ)
    (limbsToNat w a_vals.toList * limbsToNat w b_vals.toList % limbsToNat w p'_vals.toList)
:= by
  apply Limbs.converts_of_FVec
  rw [← fpMulPureV_eq, fpmul, Clap.getResult_fpmul, FVec.converts_iff_F_converts]
  apply converts_ofFnM_alloc_getElem
  -- No `getHashConsState` / `getNumAlloc` lemma exists for the gate: unfold it, as `num2bits` does.
  · unfold Clap.fpmul ClapM.getState
    simp
  · unfold Clap.fpmul ClapM.getState
    simp [Clap.getNumAlloc_Vector_ofFnM_alloc]
  · intro i
    simp only [ClapM.getState, Clap.getVarStore_fpmul]
    rw [lookup_eq h_a, lookup_eq h_b, lookup_eq h_p', Std.ExtTreeMap.insertMany_vector_list]
    apply Std.ExtTreeMap.getElem?_insertMany_list_of_mem (k := state.numAlloc + i.val) (by simp)
    · rw [List.pairwise_iff_getElem]
      intro a b ha hb hab
      simp
      omega
    · rw [List.mem_iff_getElem]
      refine ⟨i.val, by simp, ?_⟩
      simp
      omega

lemma constraints
  (h_a : Converts FVec.conversion state a a_vals)
  (h_b : Converts FVec.conversion state b b_vals)
  (h_p' : Converts FVec.conversion state p' p'_vals)
:
  ((fpmul w k a b p').runAndEval state.numAlloc state.varStore state.σ).2.constraints ↔
  ((∀ i : Fin k, a_vals[i].val < 2 ^ w) ∧ (∀ i : Fin k, b_vals[i].val < 2 ^ w) ∧
   (∀ i : Fin k, p'_vals[i].val < 2 ^ w) ∧ 0 < limbsToNat w p'_vals.toList)
:= by
  have h_some : ∀ {x : FVec p k} {x_vals : Vector (ZMod p) k},
      Converts FVec.conversion state x x_vals → ∀ i (h_i : i < k),
      [state.varStore|⦃x[i], σ' state k⦄] = some x_vals[i] :=
    fun h _ h_i ↦ eval_frame (FVec.converts_getElem h h_i) isPrefixOf_getHashConsState_Vector_ofFnM_alloc
  have h_range : ∀ {x : FVec p k} {x_vals : Vector (ZMod p) k},
      Converts FVec.conversion state x x_vals →
      ((∀ e ∈ x, ([state.varStore|⦃e, σ' state k⦄].getD 0).val < 2 ^ w) ↔
        ∀ i : Fin k, x_vals[i].val < 2 ^ w) := by
    intro x x_vals h
    constructor
    · intro hx ⟨i, h_i⟩
      simpa [h_some h i h_i] using hx x[i] (Vector.getElem_mem h_i)
    · intro hx e he
      obtain ⟨i, h_i, rfl⟩ := Vector.mem_iff_getElem.mp he
      simpa [h_some h i h_i] using hx ⟨i, h_i⟩
  have h_allocated : ∀ e, e ∈ a ∨ e ∈ b ∨ e ∈ p' →
      [state.varStore|⦃e, σ' state k⦄].isSome = true := by
    have h_mem : ∀ {x : FVec p k} {x_vals : Vector (ZMod p) k},
        Converts FVec.conversion state x x_vals → ∀ e ∈ x,
        [state.varStore|⦃e, σ' state k⦄].isSome = true := by
      intro x x_vals h e he
      obtain ⟨i, h_i, rfl⟩ := Vector.mem_iff_getElem.mp he
      simp [h_some h i h_i]
    rintro e (he | he | he)
    · exact h_mem h_a e he
    · exact h_mem h_b e he
    · exact h_mem h_p' e he
  have h_sum : ∑ i : Fin k, ([state.varStore|⦃p'[i.val], σ' state k⦄].getD 0).val * (2 ^ w) ^ i.val =
      limbsToNat w p'_vals.toList := by
    rw [limbsToNat_toList_eq_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by simp [h_some h_p' i.val i.isLt]
  unfold fpmul
  rw [Clap.eval_edsl_fpmul]
  simp only [EvalSt.constraints_stepFpmul]
  simp
  simp only [h_range h_a, h_range h_b, h_range h_p', h_sum]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h_allocated, h⟩⟩

lemma convertsM
  (h_a : Converts FVec.conversion state a a_vals)
  (h_b : Converts FVec.conversion state b b_vals)
  (h_p' : Converts FVec.conversion state p' p'_vals)
:
  ConvertsM (Limbs.conversion w k) (fpmul w k a b p') state
    (limbsToNat w a_vals.toList * limbsToNat w b_vals.toList % limbsToNat w p'_vals.toList)
    ((∀ i : Fin k, a_vals[i].val < 2 ^ w) ∧ (∀ i : Fin k, b_vals[i].val < 2 ^ w) ∧
     (∀ i : Fin k, p'_vals[i].val < 2 ^ w) ∧ 0 < limbsToNat w p'_vals.toList)
where
  result := converts h_a h_b h_p'
  wellFormed := wellFormed h_a h_b h_p'
  constraints := constraints h_a h_b h_p'

end fpmul

section examples

/-- Evaluate `fpmul w k a b c` on constant operands. -/
private def evalFpmul {k : ℕ} (q w : ℕ) (a b c : Vector (ZMod q) k) : Option (Vector (ZMod q) k) :=
  let cmd : ClapM q (HashConsSt q × FVec q k) := do
    let a ← a.mapM (fun x ↦ liftM (HashConsM.mkConstant (p := q) x))
    let b ← b.mapM (fun x ↦ liftM (HashConsM.mkConstant (p := q) x))
    let c ← c.mapM (fun x ↦ liftM (HashConsM.mkConstant (p := q) x))
    let r ← fpmul w k a b c
    let σ ← getThe (HashConsSt q)
    return (σ, r)
  let Γ := cmd.getVarStore {} 0 {}
  let r := (cmd.run 0 {}).1.1.1
  r.2.mapM fun e ↦ [Γ, r.1|e]

-- base 2^4, k = 2: 3 * 5 mod 7 = 1
example : evalFpmul 17 4 #v[3, 0] #v[5, 0] #v[7, 0] = some #v[1, 0] := by native_decide
-- zero operand
example : evalFpmul 17 4 #v[0, 0] #v[5, 0] #v[7, 0] = some #v[0, 0] := by native_decide
-- 2 * 3 mod 100 = 6, with 100 = 4 + 6·16
example : evalFpmul 17 4 #v[2, 0] #v[3, 0] #v[4, 6] = some #v[6, 0] := by native_decide
-- 15 * 15 mod 230 = 225 = 1 + 14·16
example : evalFpmul 17 4 #v[15, 0] #v[15, 0] #v[6, 14] = some #v[1, 14] := by native_decide
-- 7 * 11 mod 13 = 12
example : evalFpmul 17 4 #v[7] #v[11] #v[13] = some #v[12] := by native_decide
-- 100 * 50 mod 77 = 72
example : evalFpmul 17 4 #v[4, 6, 0] #v[2, 3, 0] #v[13, 4, 0] = some #v[8, 4, 0] := by native_decide
-- 12345 * 67890 mod 1000003 = 99536, at bn254 with 64-bit limbs
example : evalFpmul Primes.bn254 64 #v[12345] #v[67890] #v[1000003] = some #v[99536] := by
  native_decide
-- B = 2^64: (5B + 100)(7B + 50) mod (B² - 1) = 950B + 5035
example : evalFpmul Primes.bn254 64 #v[100, 5] #v[50, 7] #v[2^64 - 1, 2^64 - 1] =
    some #v[5035, 950] := by native_decide
-- 2^70 · 2^70 mod (2^140 + 1) = 2^140, on four 64-bit limbs
example : evalFpmul Primes.bn254 64 #v[0, 2^6, 0, 0] #v[0, 2^6, 0, 0] #v[1, 0, 2^12, 0] =
    some #v[0, 0, 2^12, 0] := by native_decide

end examples

end Clap.Lang
