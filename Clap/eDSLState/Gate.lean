import Clap.eDSLState.HashCons.Eval

namespace Clap

-- TODO remove p?
@[grind cases]
inductive Gate (p : ℕ) where
  | eq0 (e : ExprRef)
  | share (e : ExprRef)
  | isZero (e : ExprRef)
  | num2bits (w : ℕ) (e : ExprRef)
deriving Inhabited

namespace Gate

section Gate

variable {p : ℕ}

@[grind =]
def expr (gate : Gate p) : ExprRef :=
  match gate with
  | .eq0 e | .share e | .isZero e | .num2bits _ e => e

section

variable {e : ℕ}

@[simp, grind =]
lemma expr_mk_eq0 : (Gate.eq0 (p := p) e).expr = e := rfl

@[simp, grind =]
lemma expr_mk_share : (Gate.share (p := p) e).expr = e := rfl

@[simp, grind =]
lemma expr_mk_isZero : (Gate.isZero (p := p) e).expr = e := rfl

@[simp, grind =]
lemma expr_mk_num2bits {w} : (Gate.num2bits (p := p) w e).expr = e := rfl

end

@[grind =]
def refsValid (gate : Gate p) (bound : ℕ) : Prop := gate.expr < bound

@[grind =]
def varsAllocated (gate : Gate p) (Γ : VarStore p) (σ : HashConsSt p) : Prop :=
  [Γ, σ|gate.expr].isSome

@[aesop safe cases, grind]
structure wellFormed (gate : Gate p) (Γ : VarStore p) (σ : HashConsSt p) : Prop where
  refsValid : gate.refsValid σ.size
  varsAllocated : gate.varsAllocated Γ σ

variable {gate : Gate p} {Γ : VarStore p} {σ : HashConsSt p} {e! : ExprRef} {bound : ℕ}

instance : Decidable (gate.refsValid bound) :=
  inferInstanceAs <| Decidable (gate.expr < bound)

instance a : Decidable (gate.varsAllocated Γ σ) :=
  inferInstanceAs <| Decidable ([Γ, σ|gate.expr].isSome)

@[simp, grind =]
lemma varsAllocated_eq0 : varsAllocated (.eq0 e!) Γ σ = [Γ, σ|e!].isSome := rfl

@[simp, grind =]
lemma varsAllocated_share : varsAllocated (.share e!) Γ σ = [Γ, σ|e!].isSome := rfl

@[simp, grind =]
lemma varsAllocated_isZero : varsAllocated (.isZero e!) Γ σ = [Γ, σ|e!].isSome := rfl

@[simp, grind =]
lemma varsAllocated_num2bits {w} : varsAllocated (.num2bits w e!) Γ σ = [Γ, σ|e!].isSome := rfl

@[simp, grind =]
lemma wellFormed_iff :
  gate.wellFormed Γ σ ↔ (gate.refsValid σ.size ∧ gate.varsAllocated Γ σ) := by grind

section Precedes

variable {gate : Gate p} {Γ₁ Γ₂ Γ₃ : VarStore p}

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

section NumAlloc

def numAllocStep : Gate p → ℕ
  | .eq0 _ => 0
  | .share _ => 1
  | .isZero _ => 1
  | .num2bits w _ => w

@[simp, grind =]
lemma numAllocStep_eq0 {e : ExprRef}:
  (Gate.eq0 (p := p) e).numAllocStep = 0
:= rfl

@[simp, grind =]
lemma numAllocStep_share {e : ExprRef}:
  (Gate.share (p := p) e).numAllocStep = 1
:= rfl

@[simp, grind =]
lemma numAllocStep_isZero {e : ExprRef}:
  (Gate.isZero (p := p) e).numAllocStep = 1
:= rfl

@[simp, grind =]
lemma numAllocStep_num2bits {width} {e : ExprRef}:
  (Gate.num2bits (p := p) width e).numAllocStep = width
:= rfl

end NumAlloc

end Gate

end Gate

end Clap
