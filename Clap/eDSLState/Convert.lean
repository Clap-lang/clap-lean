import Clap.eDSLState.eDSL

import Clap.Lang.Wheels

namespace Clap

class Sized (α : Type) where
  size : ℕ

notation "|" α "|" => Sized.size α

class Convertible (p : ℕ) (α : Type) [Sized α] where
  IdealT : Type -- Can split off `IdealT` to allow e.g. `Bool` being ideal without prime, I guess
  toRepresents : IdealT → Vector (ZMod p) |α|

export Convertible (toRepresents IdealT)

structure Converts {p : ℕ}
  {α : Type} [Sized α] [φ : Convertible p α]
  (varStore : VarStore p)
  (σ : HashConsSt p)
  (numAlloc : ℕ)
  (exprs : Vector ExprRef |α|)
  (val : IdealT p α)
: Prop where
  varSet_wf : ∀ (i : Fin |α|), ⦃exprs[i], σ⦄.varSet_wellFormed numAlloc
  expr_wf   : ∀ (i : Fin |α|), ⦃exprs[i], σ⦄.wellFormed
  value_eq  : ∀ (i : Fin |α|), [varStore|⦃exprs[i], σ⦄] = .some (toRepresents val)[i]

structure Converts' {p : ℕ}
  {α : Type}
  (conversion : α → List (ZMod p))
  (varStore : VarStore p)
  (σ : HashConsSt p)
  (numAlloc : ℕ)
  (exprs : List ExprRef)
  (val : α)
: Prop where
  h_conversion : (conversion val).length = exprs.length
  varSet_wf : ∀ (i : Fin exprs.length), ⦃exprs[i], σ⦄.varSet_wellFormed numAlloc
  expr_wf   : ∀ (i : Fin exprs.length), ⦃exprs[i], σ⦄.wellFormed
  value_eq  : ∀ (i : Fin exprs.length), [varStore|⦃exprs[i], σ⦄] = .some ((conversion val)[i])

@[aesop unsafe apply, grind .]
lemma converts_of_converts' {p}
  {α} [Sized α][Convertible p α]
  {varStore : VarStore p} {σ : HashConsSt p} {numAlloc : ℕ}
  {exprs : Vector ExprRef |α|} {val : IdealT p α}
  {conversionList : IdealT p α → List (ZMod p)}
  (h : Converts' conversionList varStore σ numAlloc exprs.toList val) 
  (h_conversion :
    ∀ i : Fin |α|,
      (conversionList val)[i]'(by grind [cases Converts']) = (toRepresents val)[i]) :
  Converts varStore σ numAlloc exprs val := by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  rw! (castMode := .all) [show exprs.toList.length = |α| by aesop] at h₁ h₂ h₃ h₄
  constructor <;> aesop (add safe (by grind))

section OfDubiousWorth

/-
Typeclasses make these awkward.
-/

@[aesop unsafe apply, grind .]
lemma converts'_of_converts {p}
  {α} [Sized α] [Convertible p α]
  {varStore : VarStore p} {σ : HashConsSt p} {numAlloc : ℕ}
  {exprs : Vector ExprRef |α|} {val : IdealT p α}
  {conversionList : IdealT p α → List (ZMod p)}
  (h_len : (conversionList val).length = |α|)
  (h : Converts varStore σ numAlloc exprs val)
  (h_conversion : ∀ i : Fin |α|, (conversionList val)[i] = (toRepresents val)[i]) :
  Converts' conversionList varStore σ numAlloc exprs.toList val := by
  rcases h with ⟨h₁, h₂, h₃⟩
  constructor
  all_goals
    try intros i
        rcases i with ⟨i, hi⟩
    specialize_all (⟨i, by grind⟩ : Fin |α|)
    aesop (add safe (by grind))

@[grind .]
lemma converts_iff_converts' {p}
  {α} [Sized α] [Convertible p α]
  {varStore : VarStore p} {σ : HashConsSt p} {numAlloc : ℕ}
  {exprs : Vector ExprRef |α|} {val : IdealT p α}
  {conversionList : IdealT p α → List (ZMod p)}
  (h_len : (conversionList val).length = |α|)
  (h_conversion : ∀ i : Fin |α|, (conversionList val)[i] = (toRepresents val)[i]) :
  Converts varStore σ numAlloc exprs val ↔
  Converts' conversionList varStore σ numAlloc exprs.toList val :=
  ⟨
    fun h ↦ converts'_of_converts h_len h h_conversion,
    fun h ↦ converts_of_converts' h h_conversion
  ⟩
  
end OfDubiousWorth

section Lemmas

variable
  {p k : ℕ}
  {α : Type}
  {β : Type} [Sized β] [Convertible p β]
  {conversionVec : β → Vector (ZMod p) |β|}
  {conversionList : α  → List (ZMod p)}
  {exprsVec : Vector ExprRef |β|}
  {exprsList : List ExprRef}
  {valVec : IdealT p β}
  {valList : α}
  {Γ : VarStore p}
  {σ : HashConsSt p}
  {numAlloc : ℕ}
  {x : ZMod p}
  {actionList : ClapM p α}
  {actionVec : ClapM p β}
  {circuit : Circuit}

@[grind .]
lemma coverts_of_converts_eq {val₁ val₂}
  (h : val₁ = val₂)
:
  Converts Γ σ numAlloc exprsVec val₁ ↔
  Converts Γ σ numAlloc exprsVec val₂
:= by
  grind

@[aesop unsafe]
lemma isSome_eval_of_isSome_toIdeal
  (h : Converts Γ σ numAlloc exprsVec valVec)
:
  ∀ i : Fin |β|, [Γ, σ|exprsVec[i]].isSome = true
:= fun i ↦ Option.isSome_iff_exists.2 ⟨_, h.value_eq i⟩

@[aesop unsafe]
lemma eval_varStore_eval_eq_some
  (h₁ : Converts Γ σ numAlloc exprsVec valVec)
  (h₂ : actionVec.hashConsState_wellFormed numAlloc σ)
:
  letI varStore' := [Γ, actionVec.getHashConsState numAlloc σ, numAlloc|circuit]ₑ.varStore
  ∀ i : Fin |β|,
    [varStore'|⦃exprsVec[i], actionVec.getHashConsState numAlloc σ⦄] =
    some (toRepresents valVec)[i]
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
        set vashtorr := [unconstrained[numAlloc][Γ], actionVec.getHashConsState numAlloc σ|hd]ₛ.varStore
        rewrite [Circuit.getElem?_eval_eq_getElem?_of_lt (by grind [Converts])]
        rewrite [Circuit.getElem?_eval_eq_getElem?_of_lt (by grind [Converts])]
        choose k vec h_vec using @EvalSt.exists_varStore_step_eq_insertMany
        simp [vashtorr, h_vec.1]
        rw [Std.ExtTreeMap.getElem?_insertMany_eq_getElem?_of_neq]
        grind [Converts]

lemma eval_varStore_eval_eq_some'
  (h₁ : Converts' conversionList Γ σ numAlloc exprsList valList)
  (h₂ : actionList.hashConsState_wellFormed numAlloc σ)
:
  letI varStore' := [Γ, actionList.getHashConsState numAlloc σ, numAlloc|circuit]ₑ.varStore
  ∀ i : Fin exprsList.length,
    [varStore'|⦃exprsList[i], actionList.getHashConsState numAlloc σ⦄] =
    some ((conversionList valList)[i]'(by grind [cases Converts']))
:= by
  intros i  
  rcases circuit with ⟨l⟩
  induction' eq : l.length with len ih generalizing l
  · rcases l <;> grind [Converts']
  · rcases l with _ | ⟨hd, tl⟩
    · simp at eq
    · simp [-Fin.getElem_fin]
      specialize ih tl (by grind)
      rewrite [←ih]; clear ih
      apply eval_eq_of_varStore_eq_at_varSet
      . grind [Converts']
      . intro v h_v
        set vashtorr := [unconstrained[numAlloc][Γ], actionList.getHashConsState numAlloc σ|hd]ₛ.varStore
        rewrite [Circuit.getElem?_eval_eq_getElem?_of_lt (by grind [Converts'])]
        rewrite [Circuit.getElem?_eval_eq_getElem?_of_lt (by grind [Converts'])]
        choose k vec h_vec using @EvalSt.exists_varStore_step_eq_insertMany
        simp [vashtorr, h_vec.1]
        rw [Std.ExtTreeMap.getElem?_insertMany_eq_getElem?_of_neq]
        grind [Converts']

lemma toIdeal_run_of_toIdeal
  (h_a_wf : actionVec.wellFormed numAlloc Γ σ)
  (h : Converts Γ σ numAlloc exprsVec valVec) :
  Converts (actionVec.getVarStore Γ numAlloc σ)
           (actionVec.getHashConsState numAlloc σ)
           (actionVec.getNumAlloc numAlloc σ)
           exprsVec
           valVec := by
  rcases h with ⟨h₁, h₂, h₃⟩
  constructor
  · grind [=Expr.varSet_wellFormed]
  · grind
  · rcases h_a_wf with ⟨⟨h₄, h₅⟩, ⟨h₆, h₇⟩⟩
    intro i
    unfold ClapM.getVarStore
    rw [eval_varStore_eval_eq_some] -- a-HA!
    . constructor <;> assumption
    . assumption

end Lemmas

end Clap
