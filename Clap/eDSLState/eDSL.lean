import Clap.eDSLState.Monad
import Clap.eDSLState.HashCons.Eval
import Mathlib.Tactic

namespace Clap

open HashConsM

variable {p : ℕ}

@[irreducible]
def eq0 (e : ExprRef) : ClapM p Unit := do
  tell #[.eq0 e]

@[irreducible]
def share (e : ExprRef) : ClapM p (ExprRef) := do
  tell #[.share e]
  ClapM.alloc

@[irreducible]
def isZero (e : ExprRef) : ClapM p (ExprRef) := do
  tell #[.isZero e]
  ClapM.alloc

@[irreducible]
def num2bits (width : ℕ) (e : ExprRef) : ClapM p (Vector (ExprRef) width) := do
  tell #[.num2bits width e]
  Vector.ofFnM fun (_ : Fin width) ↦ ClapM.alloc

@[irreducible]
def fpmul (width k : ℕ) (a b p' : Vector ExprRef k) : ClapM p (Vector (ExprRef) k) := do
  tell #[.fpmul width k a b p']
  Vector.ofFnM fun (_ : Fin k) ↦ ClapM.alloc

section wellFormed

variable {numAlloc : ℕ} {e : Expr p} {e! : ExprRef} {Γ : VarStore p} {σ : HashConsSt p}
         {gate : Gate}

@[aesop unsafe, grind .]
lemma wellFormed_tell_eq0 (h₁ : e! < σ.size)
                          (h₂ : ∀ v ∈ Expr.varSet ⟨e!, σ⟩, v ∈ Γ)
                          (h₃ : Expr.varSet_wellFormed ⟨e!, σ⟩ numAlloc) :
  (tell (M := ClapM _) #[Gate.eq0 e!]).wellFormed numAlloc Γ σ := by
  unfold ClapM.wellFormed
  split_ands
  · simp [Circuit.refsValid]
    grind [eval_eq_evalRec]
  · simp [ClapM.numAlloc_wellFormed]
  . simp [ClapM.hashConsState_wellFormed]

@[aesop unsafe, grind .]
lemma wellFormed_eq0 (h₁ : e! < σ.size) (h₂ : ∀ v ∈ Expr.varSet ⟨e!, σ⟩, v ∈ Γ) (h₃ : Expr.varSet_wellFormed ⟨e!, σ⟩ numAlloc) :
  (eq0 e!).wellFormed numAlloc Γ σ
:= by
  convert wellFormed_tell_eq0 h₁ h₂ h₃
  cbv

@[simp, grind =]
lemma exprs_st_pushExpr {e : CacheExpr p} {h} :
  (σ.size, HashConsSt.pushExpr e σ h).2.exprs = σ.exprs.push e := rfl

@[simp, grind .]
lemma isPrefixOf_saveExpr {e : CacheExpr p} :
  σ.exprs.isPrefixOf ((saveExpr e).getHashConsState σ).exprs := by
  grind

@[simp, grind .]
lemma isPrefixOf_mkVar : σ.exprs.isPrefixOf ((mkVar numAlloc).getHashConsState σ).exprs := by
  unfold mkVar
  simp

@[aesop unsafe, grind .]
lemma wellFormed_mk_saveExpr_of_wellFormed {e} (h : (⟨e!, σ⟩ : Expr _).wellFormed) :
  {ref := e!, σ := (saveExpr e).getHashConsState σ : Expr _}.wellFormed := by
  change { ref := e!, σ := ((saveExpr e).run σ).2 : Expr _}.wellFormed
  unfold run
  aesop (add safe (by grind)) (add simp [saveExpr])

lemma wellFormed_tell_share_bind_alloc
        (h₁ : (Expr.mk e! σ).wellFormed) (h₂ : ∀ v ∈ Expr.varSet ⟨e!, σ⟩, v ∈ Γ) (h₃ : Expr.varSet_wellFormed ⟨e!, σ⟩ numAlloc) :
  (do tell #[Gate.share e!]; ClapM.alloc).wellFormed numAlloc Γ σ := by
  have : [Γ,σ|e!].isSome := by grind [eval_eq_evalRec]
  unfold ClapM.wellFormed
  split_ands
  · simp
    split_ands
    · unfold Circuit.refsValid
      intro gate h_gate
      aesop (add safe (by grind))
    · simp [Circuit.varsAllocated]
      split_ands
      · apply isSome_eval_of_prefix (by grind) this
        . grind
        . grind
      · intros i hi
        have : {ref := e!, σ := (saveExpr (CacheExpr.v numAlloc)).getHashConsState σ : Expr _}.varSet =
               {ref := e!, σ := σ : Expr _}.varSet := by
          apply varSet.varSet_eq_of_prefix (by grind) (by grind)
          grind
        grind
  · grind
  · grind

@[aesop safe, grind .]
lemma wellFormed_share (h₁ : e! < σ.size) (h₂ : ∀ v ∈ Expr.varSet ⟨e!, σ⟩, v ∈ Γ) (h₃ : Expr.varSet_wellFormed ⟨e!, σ⟩ numAlloc) :
  (share e!).wellFormed numAlloc Γ σ
:= by
  unfold share
  apply wellFormed_tell_share_bind_alloc (by grind) (by grind) (by grind)

@[aesop safe, grind .]
lemma wellFormed_isZero
  (h₁ : e! < σ.size) (h₂ : ∀ v ∈ Expr.varSet ⟨e!, σ⟩, v ∈ Γ) (h₃ : Expr.varSet_wellFormed ⟨e!, σ⟩ numAlloc)
:
  (isZero e!).wellFormed numAlloc Γ σ
:= by
  unfold isZero
  have : [Γ,σ|e!].isSome := by grind [eval_eq_evalRec]
  unfold ClapM.wellFormed
  split_ands
  · simp [Circuit.refsValid]
    split_ands
    · grind
    · simp [Circuit.varsAllocated]
      split_ands
      · apply isSome_eval_of_prefix _ this <;> grind
      · intros i hi
        have : { ref := e!, σ := (saveExpr (CacheExpr.v numAlloc)).getHashConsState σ : Expr _ }.varSet =
               { ref := e!, σ := σ : Expr _}.varSet := by
          apply varSet.varSet_eq_of_prefix (by grind) (by grind)
          grind
        grind
  · grind
  · grind

@[simp]
abbrev num2bitsSansTellApply (p w numAlloc : ℕ) (σ : HashConsSt p) : ((List ExprRef × Circuit) × ℕ) × HashConsSt p :=
  (List.ofFnM (n := w) (m := ClapM p)
    (
      fun _ => ClapM.alloc
    )).run numAlloc σ

def num2bitsButSane (width : ℕ) (e : ExprRef) : ClapM p (List (ExprRef)) := do
  tell #[.num2bits width e]
  num2bitsSansTellApply p width

lemma map_toList_num2bits_eq_num2bitsButSane {w e} :
  Vector.toList <$> num2bits (p := p) w e = num2bitsButSane w e := by
  unfold num2bitsButSane num2bitsSansTellApply
  simp [num2bits]
  rfl

@[aesop safe, grind .]
lemma wellFormed_of_wellFormed_toList {α} {w} {action : ClapM p (Vector α w)}
  (h : (Vector.toList <$> action).wellFormed numAlloc Γ σ) :
  action.wellFormed numAlloc Γ σ := by
  aesop (add simp [ClapM.wellFormed, Clap.monads])

@[simp, grind .]
lemma size_le_size_run_mkVar :
  σ.size ≤
  ((mkVar numAlloc).getHashConsState σ).size
:= by
  grind

@[simp, grind .]
lemma size_le_size_getHashConsState_alloc :
  σ.size ≤
  (ClapM.alloc.getHashConsState numAlloc σ).size
:= by
  aesop (add safe (by grind)) (add safe (by exact size_le_size_run_mkVar))

@[simp, grind .]
lemma size_le_size_Vector_ofFnM_alloc
  {k : ℕ}
:
  σ.size ≤
  ((Vector.ofFnM λ (_ : Fin k) => ClapM.alloc).getHashConsState numAlloc σ).size
:= by
  induction' k with k h_k
  . grind
  . rewrite [Vector.ofFnM_succ]
    grind

@[simp, grind =]
lemma getCircuit_Vector_ofFnM_alloc
  {k : ℕ}
:
  (Vector.ofFnM λ (_ : Fin k) => ClapM.alloc).getCircuit numAlloc σ =
  #[]
:= by
  induction' k with k h_k
  . grind
  . rewrite [Vector.ofFnM_succ]
    grind

@[simp, grind =]
lemma isPrefixOf_getHashConsState_Vector_ofFnM_alloc
  {k : ℕ}
:
  σ.exprs.isPrefixOf ((Vector.ofFnM λ (_ : Fin k) => ClapM.alloc).getHashConsState numAlloc σ).exprs = true
:= by
  induction' k with k h_k
  . grind
  . rewrite [Vector.ofFnM_succ]
    simp [ClapM.getHashConsState_bind]
    grind [Array.isPrefixOf_trans]

@[simp, grind =]
lemma getNumAlloc_Vector_ofFnM_alloc
  {k : ℕ}
:
  (Vector.ofFnM λ (_ : Fin k) => ClapM.alloc).getNumAlloc numAlloc σ =
  numAlloc + k
:= by
  induction' k with k h_k
  . grind
  . rewrite [Vector.ofFnM_succ]
    simp [h_k]
    omega


@[aesop safe, grind .]
lemma wellFormed_num2bits {width : ℕ}
  (h₁ : e! < σ.size) (h₂ : ∀ v ∈ Expr.varSet ⟨e!, σ⟩, v ∈ Γ) (h₃ : Expr.varSet_wellFormed ⟨e!, σ⟩ numAlloc)
:
  (num2bits width e!).wellFormed numAlloc Γ σ
:= by
  unfold num2bits
  have h_isSome : [Γ,σ|e!].isSome := by grind [eval_eq_evalRec]
  have h_wellFormed : (Expr.mk e! σ).wellFormed := by grind
  unfold ClapM.wellFormed
  split_ands
  · simp [Circuit.refsValid]
    split_ands
    . exact lt_of_lt_of_le h₁ (by grind)
    . unfold Circuit.varsAllocated
      intro i h_i
      obtain _ | ⟨i⟩ := i <;> simp
      . split_ands
        . apply isSome_eval_of_prefix (by grind) h_isSome (by trivial)
          grind
        . intro x h_x
          rewrite [varSet.varSet_eq_of_prefix (by grind) h_wellFormed] at h_x
          . grind
          . grind
      . grind
  . grind
  . grind

@[grind =>]
lemma wellFormed_fpmul {width k : ℕ} {a b p' : Vector ExprRef k}
  (h₁ : ∀ e! ∈ a, e! < σ.size)
  (h₂ : ∀ e! ∈ b, e! < σ.size)
  (h₃ : ∀ e! ∈ p', e! < σ.size)
  (h₄ : ∀ e! ∈ a, ∀ v ∈ Expr.varSet ⟨e!, σ⟩, v ∈ Γ)
  (h₅ : ∀ e! ∈ b, ∀ v ∈ Expr.varSet ⟨e!, σ⟩, v ∈ Γ)
  (h₆ : ∀ e! ∈ p', ∀ v ∈ Expr.varSet ⟨e!, σ⟩, v ∈ Γ)
  (h₇ : ∀ e! ∈ a, Expr.varSet_wellFormed ⟨e!, σ⟩ numAlloc)
  (h₈ : ∀ e! ∈ b, Expr.varSet_wellFormed ⟨e!, σ⟩ numAlloc)
  (h₉ : ∀ e! ∈ p', Expr.varSet_wellFormed ⟨e!, σ⟩ numAlloc) :
  (fpmul width k a b p').wellFormed numAlloc Γ σ := by
  unfold fpmul
  have h_isSome₁ : ∀ e! ∈ a, [Γ,σ|e!].isSome := by grind [eval_eq_evalRec]
  have h_isSome₂ : ∀ e! ∈ b, [Γ,σ|e!].isSome := by grind [eval_eq_evalRec]
  have h_isSome₃ : ∀ e! ∈ p', [Γ,σ|e!].isSome := by grind [eval_eq_evalRec]
  have h_wellFormed₁ : ∀ e! ∈ a, (Expr.mk e! σ).wellFormed := by grind
  have h_wellFormed₂ : ∀ e! ∈ b, (Expr.mk e! σ).wellFormed := by grind
  have h_wellFormed₃ : ∀ e! ∈ p', (Expr.mk e! σ).wellFormed := by grind
  unfold ClapM.wellFormed
  split_ands
  · simp [Circuit.refsValid]
    split_ands
    . intros ref href
      have : ref < σ.size := by
        rcases href with h | h | h <;> specialize_all ref <;> grind
      exact lt_of_lt_of_le this (by grind)
    . unfold Circuit.varsAllocated
      intro i h_i
      obtain _ | ⟨i⟩ := i <;> simp
      . split_ands
        . intros ref href
          specialize_all ref
          rcases href with h | h | h <;> specialize_all h
          · apply isSome_eval_of_prefix (by grind) (h_isSome₁) (by grind)
            grind
          · apply isSome_eval_of_prefix (by grind) (h_isSome₂) (by grind)
            grind
          · apply isSome_eval_of_prefix (by grind) (h_isSome₃) (by grind)
            grind
        . intro x h_x ref href
          specialize_all x
          rcases h_x with h | h | h <;>
          · have := varSet.varSet_eq_of_prefix
                      (e₁ := ⟨x, σ⟩)
                      (e₂ := { ref := x, σ := (Vector.ofFnM (n := k) fun x => ClapM.alloc).getHashConsState numAlloc σ : Expr _})
                      (by grind) (show (⟨x, σ⟩ : Expr _).wellFormed by grind)
            rewrite [this] at href
            grind
            grind
      . grind
  . grind
  . grind

end wellFormed

section Eval

variable {e! : ExprRef} {numAlloc : ℕ} {varStore : VarStore p} {σ : HashConsSt p}

@[simp, grind =]
lemma eval_edsl_eq0
:
  (eq0 e!).runAndEval numAlloc varStore σ =
  ⟨(), [varStore, σ, numAlloc|#[Gate.eq0 e!]]ₑ⟩
:= by
  grind [eq0]

@[simp, grind =]
lemma eval_edsl_share
:
  (share e!).runAndEval numAlloc varStore σ =
  ⟨((mkVar numAlloc).getResult σ), [varStore, (mkVar numAlloc).getHashConsState σ, numAlloc|#[Gate.share e!]]ₑ⟩
:= by
  grind [share, ClapM.runAndEval]

@[simp, grind =]
lemma eval_edsl_isZero :
  (isZero e!).runAndEval numAlloc varStore σ =
  ⟨(mkVar numAlloc).getResult σ, [varStore, (mkVar numAlloc).getHashConsState σ, numAlloc|#[Gate.isZero e!]]ₑ⟩
:= by
  grind [isZero, ClapM.runAndEval]

@[simp, grind =]
lemma eval_edsl_num2bits
  {width : ℕ}
:
  (num2bits width e!).runAndEval numAlloc varStore σ =
  ⟨
    (Vector.ofFnM fun (_ : Fin width) => ClapM.alloc).getResult numAlloc σ,
    [varStore, (Vector.ofFnM fun (_ : Fin width) => ClapM.alloc).getHashConsState numAlloc σ, numAlloc|#[Gate.num2bits width e!]]ₑ
  ⟩
:= by
  simp [num2bits, ClapM.runAndEval]

@[simp, grind =]
lemma eval_edsl_fpmul
  {width k : ℕ} {a b p' : Vector ExprRef k}
:
  (fpmul width k a b p').runAndEval numAlloc varStore σ =
  ⟨
    (Vector.ofFnM fun (_ : Fin k) => ClapM.alloc).getResult numAlloc σ,
    unconstrained[numAlloc][varStore].stepFpmul
      ((Vector.ofFnM fun (_ : Fin k) => ClapM.alloc).getHashConsState numAlloc σ) width k a b p'
  ⟩
:= by
  simp [fpmul, ClapM.runAndEval]

end Eval

section GetResult

variable {e! : ExprRef} {numAlloc w k : ℕ} {σ : HashConsSt p} {a b p' : Vector ExprRef k}

@[simp, grind =]
lemma getResult_eq0 :
  (eq0 e!).getResult numAlloc σ = (HashConsM.mkVar numAlloc).getResult σ := by
  unfold eq0; rfl

@[simp, grind =]
lemma getResult_share :
  (share e!).getResult numAlloc σ = (HashConsM.mkVar numAlloc).getResult σ := by
  unfold share; rfl

@[simp, grind =]
lemma getResult_isZero :
  (isZero e!).getResult numAlloc σ = (HashConsM.mkVar numAlloc).getResult σ := by
  unfold isZero; rfl

@[simp, grind =]
lemma getResult_num2bits :
  (num2bits w e!).getResult numAlloc σ = (Vector.ofFnM fun _ => ClapM.alloc).getResult numAlloc σ := by
  unfold num2bits; rfl

@[simp, grind =]
lemma getResult_fpmul :
  (fpmul w k a b p').getResult numAlloc σ = (Vector.ofFnM fun _ => ClapM.alloc).getResult numAlloc σ := by
  unfold fpmul; rfl

end GetResult

section GetVarstore

variable {e! : ExprRef} {numAlloc w k : ℕ} {σ : HashConsSt p} {a b p' : Vector ExprRef k}
         {Γ : VarStore p}

@[simp, grind =]
lemma getVarStore_eq0 :
  (eq0 e!).getVarStore Γ numAlloc σ = Γ := by
  simp [eq0]

@[simp, grind =]
lemma getVarStore_share :
  (share e!).getVarStore Γ numAlloc σ =
  Γ.insert numAlloc ([Γ|⦃e!, (mkVar numAlloc).getHashConsState σ⦄].getD 0) := by
  simp [share, ClapM.getVarStore]

@[simp, grind =]
lemma getVarStore_isZero :
  (isZero e!).getVarStore Γ numAlloc σ =
  Std.ExtTreeMap.insert Γ numAlloc (if [Γ|⦃e!, (mkVar numAlloc).getHashConsState σ⦄] = some 0 then 1 else 0) := by
  simp [isZero, ClapM.getVarStore]
  rfl

@[simp, grind =]
lemma getVarStore_num2bits :
  (num2bits w e!).getVarStore Γ numAlloc σ =
  Γ.insertMany
    (((Vector.range w).map (fun x => x + numAlloc)).zip
      (num2bitsLsbPureV w ([Γ|⦃e!, (Vector.ofFnM fun _ : Fin w => ClapM.alloc).getHashConsState numAlloc σ⦄].getD 0))) := by
  unfold num2bits ClapM.getVarStore
  simp

@[simp, grind =]
lemma getVarStore_fpmul :
  (fpmul w k a b p').getVarStore Γ numAlloc σ =
  letI map := (Vector.ofFnM fun _ : Fin k => ClapM.alloc).getHashConsState numAlloc σ
  Γ.insertMany
    (((Vector.range k).map (fun x => x + numAlloc)).zip
    (EvalSt.fpMulPureV w k
      (a.map (fun e => [Γ|⦃e, map⦄].getD 0))
      (b.map (fun e => [Γ|⦃e, map⦄].getD 0))
      (p'.map (fun e => [Γ|⦃e, map⦄].getD 0)))) := by
  unfold fpmul ClapM.getVarStore
  simp

end GetVarstore

end Clap
