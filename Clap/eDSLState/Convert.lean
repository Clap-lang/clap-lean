import Clap.eDSLState.eDSL

import Clap.Lang.Wheels

namespace Clap

-- class Sized (α : Type) where
--   size : ℕ

-- notation "|" α "|" => Sized.size α

class Convertible (p : ℕ) (α : Type) where
  IdealT : Type -- Can split off `IdealT` to allow e.g. `Bool` being ideal without prime, I guess
  toRepresents : IdealT → ZMod p

export Convertible (toRepresents IdealT)

structure ClapState (p : ℕ) where
  varStore : VarStore p
  σ : HashConsSt p
  numAlloc : ℕ

def ClapM.getState {p : ℕ} {α} (cmd : ClapM p α) (state : ClapState p) : ClapState p where
  varStore := cmd.getVarStore state.varStore state.numAlloc state.σ
  σ := cmd.getHashConsState state.numAlloc state.σ
  numAlloc := cmd.getNumAlloc state.numAlloc state.σ

attribute [local grind] ClapM.getState

structure Converts {p : ℕ}
  {α : Type} [φ : Convertible p α]
  (state : ClapState p)
  (exprs : List ExprRef)
  (vals : List (IdealT p α))
: Prop where
  h_len     : exprs.length = vals.length
  varSet_wf : ∀ (i : Fin exprs.length), ⦃exprs[i], state.σ⦄.varSet_wellFormed state.numAlloc
  expr_wf   : ∀ (i : Fin exprs.length), ⦃exprs[i], state.σ⦄.wellFormed
  value_eq  : ∀ (i : Fin exprs.length), [state.varStore|⦃exprs[i], state.σ⦄] = .some (toRepresents vals[i])

class ConvertibleM (p : ℕ) (α : Type) extends Convertible p α where
  getResultToExprs : α → List ExprRef

-- def ClapM.getExprs (p : ℕ) (α : Type) [ConvertibleM p α]
--   getExprs : ClapM p α → ClapState p → List ExprRef
--   abc (cmd : ClapM p α) (state : ClapState p) : getResultToExprs (cmd.getResult state.numAlloc state.σ) = getExprs cmd state

abbrev _root_.Clap.ClapM.getExprs {p α} [ConvertibleM p α]
  (cmd : ClapM p α) (state : ClapState p) : List ExprRef :=
    ConvertibleM.getResultToExprs p (cmd.getResult state.numAlloc state.σ)

structure ConvertsM {p} {α}
  [ConvertibleM p α]
  (cmd : ClapM p α) (state : ClapState p) (vals : List (IdealT p α))
: Prop where
  result : Converts (cmd.getState state) (cmd.getExprs state) vals
  wellFormed : cmd.wellFormed state.numAlloc state.varStore state.σ

section Lemmas

variable
  {p : ℕ} {α : Type}
  {state : ClapState p}
  [Convertible p α]
  {exprs : List ExprRef}
  {vals vals₁ vals₂ : List (IdealT p α)}
  {cmd : ClapM p α}
  {circuit : Circuit}

@[grind .]
lemma coverts_of_converts_eq (h : vals₁ = vals₂)
:
  Converts state exprs vals₁ ↔
  Converts state exprs vals₂
:= by
  grind

@[aesop unsafe, grind .]
lemma isSome_eval_of_mem
  (h : Converts state exprs vals)
  {e : ExprRef}
  (h_mem : e ∈ exprs)
:
  [state.varStore, state.σ|e].isSome = true
:= by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  rw [List.mem_iff_getElem?] at h_mem
  rcases h_mem with ⟨w, hw⟩
  specialize h₄ ⟨w, by grind⟩
  grind

@[aesop unsafe]
lemma eval_varStore_eval_eq_some
  (h₁ : Converts state exprs vals)
  (h₂ : cmd.hashConsState_wellFormed state.numAlloc state.σ)
:
  letI varStore' := [state.varStore, (cmd.getState state).σ, state.numAlloc|circuit]ₑ.varStore
  ∀ i : Fin exprs.length,
    [varStore'|⦃exprs[i], (cmd.getState state).σ⦄] =
    some (toRepresents (vals[i]'(by grind [cases Converts])))
:= by
  intros i
  rcases circuit with ⟨l⟩
  induction' eq : l.length with len ih generalizing l
  · rcases l <;> grind [Converts, ClapM.getState]
  · rcases l with _ | ⟨hd, tl⟩
    · simp at eq
    · simp [-Fin.getElem_fin]
      specialize ih tl (by grind)
      rewrite [←ih]; clear ih
      apply eval_eq_of_varStore_eq_at_varSet
      . grind [Converts, ClapM.getState]
      . intro v h_v
        set vashtorr := [unconstrained[state.numAlloc][state.varStore], (cmd.getState state).σ|hd]ₛ.varStore
        rewrite [Circuit.getElem?_eval_eq_getElem?_of_lt (by grind [Converts, ClapM.getState])]
        rewrite [Circuit.getElem?_eval_eq_getElem?_of_lt (by grind [Converts, ClapM.getState])]
        choose k vec h_vec using @EvalSt.exists_varStore_step_eq_insertMany
        simp [vashtorr, h_vec.1]
        rw [Std.ExtTreeMap.getElem?_insertMany_eq_getElem?_of_neq]
        grind [Converts, ClapM.getState]

lemma converts_getState_of_wellFormed
  (h_a_wf : cmd.wellFormed state.numAlloc state.varStore state.σ)
  (h : Converts state exprs vals)
:
  Converts (cmd.getState state) exprs vals
:= by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  constructor
  case h_len => assumption
  · grind [=Expr.varSet_wellFormed]
  · grind
  · rcases h_a_wf with ⟨⟨h₄, h₅⟩, ⟨h₆, h₇⟩⟩
    intro i
    rw [show (cmd.getState state).varStore = cmd.getVarStore state.varStore state.numAlloc state.σ from rfl]
    unfold ClapM.getVarStore
    change
      [[state.varStore, (cmd.getState state).σ,
              state.numAlloc|cmd.getCircuit state.numAlloc
                state.σ]ₑ.varStore|⦃exprs[i], (cmd.getState state).σ⦄] =
        some (toRepresents vals[i])
    rw [eval_varStore_eval_eq_some]
    . constructor <;> assumption
    . assumption

end Lemmas

section LemmasM

variable
  {p : ℕ} {α : Type}
  {state : ClapState p}
  [ConvertibleM p α]
  {exprs : List ExprRef}
  {vals : List (IdealT p α)}
  {cmd cmd₁ cmd₂ : ClapM p α}

lemma converts_getState
  {skip_vals}
  (h_skip : ConvertsM cmd state skip_vals)
  (h_vals : Converts state exprs vals)
:
  Converts (cmd.getState state) exprs vals
:=
  converts_getState_of_wellFormed
    h_skip.wellFormed
    h_vals

end LemmasM

end Clap
