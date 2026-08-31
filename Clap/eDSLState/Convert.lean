import Clap.eDSLState.eDSL

import Clap.Lang.Wheels

namespace Clap

structure Converts {p : ℕ} {α : Type}
  (k : ℕ)
  (conversion : α → Vector (ZMod p) k)
  (varStore : VarStore p)
  (σ : HashConsSt p)
  (numAlloc : ℕ)
  (exprs : Vector ExprRef k)
  (val : α)
: Prop where
  varSet_wf : ∀ (i : Fin k), ⦃exprs[i], σ⦄.varSet_wellFormed numAlloc
  expr_wf   : ∀ (i : Fin k), ⦃exprs[i], σ⦄.wellFormed
  value_eq  : ∀ (i : Fin k), [varStore|⦃exprs[i], σ⦄] = .some (conversion val)[i]

structure Converts' {p : ℕ} {α : Type}
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
  {conversion : α → Vector (ZMod p) k}
  {Γ : VarStore p}
  {σ : HashConsSt p}
  {numAlloc : ℕ}
  {exprs : Vector ExprRef k}
  {val : α}
  {x : ZMod p}
  {action : ClapM p α}
  {circuit : Circuit}

lemma converts_of_converts_eq
  {val₁ : α} (val₂ : α)
  (h : val₁ = val₂)
:
  Converts k conversion Γ σ numAlloc exprs val₁ ↔
  Converts k conversion Γ σ numAlloc exprs val₂
:= by
  grind

@[aesop unsafe]
lemma isSome_eval_of_isSome_toIdeal
  (h : Converts k conversion Γ σ numAlloc exprs val)
:
  ∀ i : Fin k, [Γ, σ|exprs[i]].isSome = true
:= fun i ↦ Option.isSome_iff_exists.2 ⟨_, h.value_eq i⟩

lemma eval_varStore_eval_eq_some
  {β}
  {action : ClapM p β}
  (h₁ : Converts k conversion Γ σ numAlloc exprs val)
  (h₂ : action.hashConsState_wellFormed numAlloc σ)
:
  letI varStore' := [Γ, action.getHashConsState numAlloc σ, numAlloc|circuit]ₑ.varStore
  ∀ i : Fin k, [varStore'|⦃exprs[i], action.getHashConsState numAlloc σ⦄] = some (conversion val)[i]
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
        set vashtorr := [unconstrained[numAlloc][Γ], action.getHashConsState numAlloc σ|hd]ₛ.varStore
        rewrite [Circuit.getElem?_eval_eq_getElem?_of_lt (by grind [Converts])]
        rewrite [Circuit.getElem?_eval_eq_getElem?_of_lt (by grind [Converts])]
        choose k vec h_vec using @EvalSt.exists_varStore_step_eq_insertMany
        simp [vashtorr, h_vec.1]
        rw [Std.ExtTreeMap.getElem?_insertMany_eq_getElem?_of_neq]
        grind [Converts]

lemma toIdeal_run_of_toIdeal
  {β}
  (action : ClapM p β)
  (h_a_wf : action.wellFormed numAlloc Γ σ)
  (h : Converts k conversion Γ σ numAlloc exprs val) :
  Converts k
           conversion
           (action.getVarStore Γ numAlloc σ)
           (action.getHashConsState numAlloc σ)
           (action.getNumAlloc numAlloc σ)
           exprs
           val := by
  rcases h with ⟨h₁, h₂, h₃⟩
  constructor
  · grind [=Expr.varSet_wellFormed]
  · grind
  · rcases h_a_wf with ⟨⟨h₄, h₅⟩, ⟨h₆, h₇⟩⟩
    intro i
    unfold ClapM.getVarStore
    rw [eval_varStore_eval_eq_some (conversion := conversion) (val := val)]
    . constructor <;> assumption
    . assumption

end Lemmas

end Clap

-- structure Convert.toIdeal (varStore : VarStore p)
--                           (σ : HashConsSt p)
--                           (numAlloc : ℕ)
--                           (result : F)
--                           (x : ZMod p) : Prop where
--   varSet_wf : ⦃result, σ⦄.varSet_wellFormed numAlloc
--   expr_wf   : ⦃result, σ⦄.wellFormed
--   value_eq  : [varStore, σ|result] = .some x

-- structure _root_.Clap.Lang.FB.Convert.toIdeal (varStore : VarStore p)
--                                               (σ : HashConsSt p)
--                                               (numAlloc : ℕ)
--                                               (result : FB)
--                                               (x : Bool) : Prop where
--   varSet_wf : ⦃result, σ⦄.varSet_wellFormed numAlloc
--   expr_wf   : ⦃result, σ⦄.wellFormed
--   value_eq  : [varStore, σ|result] = .some (if x then 1 else 0)

-- structure _root_.Clap.Lang.FArray.Convert.toIdeal (varStore : VarStore p)
--                                                   (σ : HashConsSt p)
--                                                   (numAlloc : ℕ)
--                                                   {k : ℕ}
--                                                   (result : FArray k)
--                                                   (x : Vector Bool k) : Prop where
--   varSet_wf : ∀ elem ∈ result, ⦃elem, σ⦄.varSet_wellFormed numAlloc
--   expr_wf   : ∀ elem ∈ result, ⦃elem, σ⦄.wellFormed
--   value_eq  : ∀ (i : Fin k), [varStore, σ|result[i]] = .some (if x[i] then 1 else 0)



































-- import Clap.eDSLState.IsValid

-- namespace Clap

-- class Convert (p : ℕ) (representsT idealT : Type) extends IsValid p representsT where
--   toIdeal : (VarStore p) → (HashConsSt p) → representsT → Option idealT
--   toRepresents : idealT → HashConsM p representsT
--   isValid_iff_isSome_toIdeal :
--     ∀ (varStore : VarStore p) (σ : HashConsSt p) (x : representsT),
--       isValid varStore σ x ↔ (toIdeal varStore σ x).isSome
--   toIdeal_toRepresents :
--     ∀ (varStore : VarStore p) (σ : HashConsSt p) (x : idealT),
--       toIdeal varStore ((toRepresents x).getHashConsState σ) ((toRepresents x).getResult σ) = .some x

-- @[simp, grind =]
-- lemma Convert.toRepresents_toIdeal
--   {p : ℕ}
--   {representsT idealT : Type}
--   [inst: Convert p representsT idealT]
--   {varStore : VarStore p}
--   {σ : HashConsSt p}
--   {x : representsT}
--   (h : IsValid.isValid varStore σ x)
-- :
--   toIdeal (representsT := representsT) (idealT := idealT) varStore σ
--     ((toRepresents (representsT := representsT) ((toIdeal (idealT := idealT) varStore σ x).get ((isValid_iff_isSome_toIdeal varStore σ x).mp h))).getResult σ) =
--   inst.toIdeal varStore σ x
-- := by
--   have := inst.toIdeal_toRepresents
--   simp [HashConsM.getHashConsState, HashConsM.getResult] at this ⊢

--   simp [inst.toIdeal_toRepresents]

-- instance {p : ℕ} : Convert p Unit Unit where
--   isValid := fun _ _ _ ↦ True
--   toIdeal _ x := .some x
--   toRepresents x := x
--   isValid_iff_isSome_toIdeal _ _ := by grind
--   toIdeal_toRepresents _ _ := by grind

-- @[simp, grind .]
-- lemma isValid_iff_isSome_toIdeal {p} {α β : Type} [Convert p α β]
--   {varStore : VarStore p} {σ : HashConsSt p} {x : α}
-- :
--   (Convert.toIdeal (idealT := β) varStore x).isSome ↔
--   IsValid.isValid varStore σ x
-- := by
--   aesop (add safe cases Convert)

-- @[grind .]
-- lemma isValid_of_toIdeal_eq_some {p} {α β : Type} [Convert p α β]
--   {varStore : VarStore p} {x : α} {b : β}
--   (h : (Convert.toIdeal (idealT := β) varStore x) = .some b)
-- :
--   IsValid.isValid varStore x
-- := by
--   have := Option.isSome_of_eq_some h
--   grind

-- @[simp, grind .]
-- lemma toIdealtoRepresents_of_convert {p} {α β : Type} [Convert p α β]
--   {varStore : VarStore p} {x : β}
-- :
--   Convert.toIdeal (representsT := α) varStore (Convert.toRepresents p x) = .some x
-- := by
--   aesop (add safe cases Convert)

-- end Clap
