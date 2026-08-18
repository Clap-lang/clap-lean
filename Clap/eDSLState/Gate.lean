import Clap.eDSLState.HashCons.Eval

namespace Clap

@[grind cases]
inductive Gate where
  | eq0 (e : ExprRef)
  | share (e : ExprRef)
  | isZero (e : ExprRef)
  | num2bits (w : ℕ) (e : ExprRef)
  | fpmul (w k : ℕ) (a b p' : Vector ExprRef k)
deriving Inhabited

namespace Gate

section Gate

variable {p : ℕ}

@[grind =]
def exprs (gate : Gate) : Finset ExprRef :=
  match gate with
  | .fpmul _ _ a b p' => a.toList.toFinset ∪ b.toList.toFinset ∪ p'.toList.toFinset
  | .eq0 e | .share e | .isZero e | .num2bits _ e => {e}

section

variable {ref : ℕ} {σ : HashConsSt p} {e : Expr p}

@[simp, grind =]
lemma expr_mk_eq0 : (Gate.eq0 ref).exprs = {ref} := rfl

@[simp, grind =]
lemma expr_mk_share : (Gate.share ref).exprs = {ref} := rfl

@[simp, grind =]
lemma expr_mk_isZero : (Gate.isZero ref).exprs = {ref} := rfl

@[simp, grind =]
lemma expr_mk_num2bits {w} : (Gate.num2bits w ref).exprs = {ref} := rfl

@[simp, grind =]
lemma expr_mk_fpmul {w k} {a b p'} :
  (Gate.fpmul w k a b p').exprs =
  a.toList.toFinset ∪ b.toList.toFinset ∪ p'.toList.toFinset := rfl

end

@[grind =]
def refsValid (gate : Gate) (bound : ℕ) : Prop := ∀ e ∈ gate.exprs, e < bound

@[grind =]
def varsAllocated (gate : Gate) (Γ : VarStore p) (σ : HashConsSt p) : Prop :=
  ∀ e ∈ gate.exprs, [Γ, σ|e].isSome

@[aesop safe cases, grind]
structure wellFormed (gate : Gate) (Γ : VarStore p) (σ : HashConsSt p) : Prop where
  refsValid : gate.refsValid σ.size
  varsAllocated : gate.varsAllocated Γ σ

variable {gate : Gate} {Γ : VarStore p} {σ : HashConsSt p} {e! : ExprRef} {bound : ℕ}

instance : Decidable (gate.refsValid bound) :=
  inferInstanceAs <| Decidable (∀ e ∈ gate.exprs, e < bound)

instance : Decidable (gate.varsAllocated Γ σ) :=
  inferInstanceAs <| Decidable (∀ e ∈ gate.exprs, [Γ, σ|e].isSome)

@[simp, grind =]
lemma varsAllocated_eq0 : varsAllocated (.eq0 e!) Γ σ = [Γ, σ|e!].isSome := by grind

@[simp, grind =]
lemma varsAllocated_share : varsAllocated (.share e!) Γ σ = [Γ, σ|e!].isSome := by grind

@[simp, grind =]
lemma varsAllocated_isZero : varsAllocated (.isZero e!) Γ σ = [Γ, σ|e!].isSome := by grind

@[simp, grind =]
lemma varsAllocated_num2bits {w} : varsAllocated (.num2bits w e!) Γ σ = [Γ, σ|e!].isSome := by grind

@[simp, grind =]
lemma varsAllocated_fpmul {w k} {a b p'} :
  varsAllocated (.fpmul w k a b p') Γ σ =
  (∀ ref ∈ a ++ b ++ p', [Γ, σ|ref].isSome) := by
  simp [varsAllocated, exprs]

@[simp, grind =]
lemma wellFormed_iff :
  gate.wellFormed Γ σ ↔ (gate.refsValid σ.size ∧ gate.varsAllocated Γ σ) := by grind

@[grind =>]
lemma refsValid_of_refsValid_of_le
  {bound_low bound_high : ℕ}
  (h_refsValid : gate.refsValid bound_low)
  (h_le : bound_low ≤ bound_high)
:
  gate.refsValid bound_high
:= by
  grind

@[grind .]
lemma refsValid_iff_wellFormed_mk :
  (∀ e ∈ gate.exprs, (Expr.mk e σ).wellFormed) ↔ gate.refsValid σ.size := by
  grind

@[simp, grind =]
lemma refsValid_eq0 : (Gate.eq0 e!).refsValid bound ↔ e! < bound := by
  simp [refsValid]

@[simp, grind =]
lemma refsValid_share : (Gate.share e!).refsValid bound ↔ e! < bound := by
  simp [refsValid]

@[simp, grind =]
lemma refsValid_isZero : (Gate.isZero e!).refsValid bound ↔ e! < bound := by
  simp [refsValid]

@[simp, grind =]
lemma refsValid_num2bits {w : ℕ} : (Gate.num2bits w e!).refsValid bound ↔ e! < bound := by
  simp [refsValid]

@[simp, grind =]
lemma refsValid_fpmul {w k : ℕ} {a b p'} :
  (Gate.fpmul w k a b p').refsValid bound ↔
  (∀ ref ∈ a ++ b ++ p', ref < bound) := by
  simp [refsValid, exprs]

section Precedes

variable {gate : Gate} {Γ₁ Γ₂ Γ₃ : VarStore p}

@[grind .]
lemma wellFormed_of_wellFormed_precedes
  (h_refsValid : gate.wellFormed Γ₁ σ)
  (h : [σ|Γ₁ ⊑ Γ₂])
:
  gate.wellFormed Γ₂ σ
:= by
  grind

@[grind .]
lemma varsAllocated_of_wellFormed_precedes
  {varStore1 varStore2 : VarStore p}
  (h_refsValid : gate.wellFormed varStore1 σ)
  (h : [σ|varStore1 ⊑ varStore2])
:
  gate.varsAllocated varStore2 σ
:= by
  grind

end Precedes

section Prefix

@[grind ->]
lemma wellFormed_of_wellFormed_isPrefixOf
  {p : ℕ}
  {e₁ e₂ : Expr p}
  (h : e₁.ref = e₂.ref)
  (h_prefix : e₁.σ.exprs.isPrefixOf e₂.σ.exprs = true)
  (this : e₁.wellFormed) : e₂.wellFormed := by
  grind

@[grind .]
lemma varsAllocated_eq_of_prefix_refsValid
  {σ σ' : HashConsSt p}
  {Γ : VarStore p}
  {gate : Gate}
  (h_prefix : σ.exprs.isPrefixOf σ'.exprs = true)
  (h_refsValid : gate.refsValid σ.size) :
  gate.varsAllocated Γ σ' =
  gate.varsAllocated Γ σ := by
  unfold Gate.varsAllocated
  simp only [eq_iff_iff]
  refine ⟨fun h v h₂ ↦ ?p₁, fun h v h₂ ↦ ?p₂⟩
  · specialize h _ h₂
    set e₁ : Expr _ := {ref := v, σ := σ}
    set e₂ : Expr _ := {ref := v, σ := σ'}
    have wf₁ : e₁.wellFormed := by grind
    have wf₂ : e₂.wellFormed := by
      apply wellFormed_of_wellFormed_isPrefixOf (e₁ := e₁) _ h_prefix <;> grind
    simp [eval_eq_evalRec, wf₁, wf₂] at ⊢ h
    intros ref href
    apply h
    replace h_prefix : e₁.σ.exprs.isPrefixOf e₂.σ.exprs = true := by grind
    rewrite [←varSet.varSet_eq_of_prefix (h₂ := h_prefix)] <;> grind
  · specialize h _ h₂
    set e₁ : Expr _ := {ref := v, σ := σ}
    set e₂ : Expr _ := {ref := v, σ := σ'}
    have wf₁ : e₁.wellFormed := by grind
    have wf₂ : e₂.wellFormed := by
      apply wellFormed_of_wellFormed_isPrefixOf (e₁ := e₁) _ h_prefix <;> grind
    simp [eval_eq_evalRec, wf₁, wf₂] at ⊢ h
    intros ref href
    apply h
    replace h_prefix : e₁.σ.exprs.isPrefixOf e₂.σ.exprs = true := by grind
    rewrite [varSet.varSet_eq_of_prefix (h₂ := h_prefix)] <;> grind

end Prefix

section NumAlloc

def numAllocStep : Gate → ℕ
  | .eq0 _ => 0
  | .share _ => 1
  | .isZero _ => 1
  | .num2bits w _ => w
  | .fpmul (k := k) .. => k

@[simp, grind =]
lemma numAllocStep_eq0 {e : ExprRef}:
  (Gate.eq0 e).numAllocStep = 0
:= rfl

@[simp, grind =]
lemma numAllocStep_share {e : ExprRef}:
  (Gate.share e).numAllocStep = 1
:= rfl

@[simp, grind =]
lemma numAllocStep_isZero {e : ExprRef}:
  (Gate.isZero e).numAllocStep = 1
:= rfl

@[simp, grind =]
lemma numAllocStep_num2bits {width} {e : ExprRef}:
  (Gate.num2bits width e).numAllocStep = width
:= rfl

@[simp, grind =]
lemma numAllocStep_fpmul {w} {k} {a b p'} :
  (Gate.fpmul w k a b p').numAllocStep = k
:= rfl

end NumAlloc

end Gate

end Gate

end Clap
