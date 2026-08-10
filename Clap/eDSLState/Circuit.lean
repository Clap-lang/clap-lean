import Mathlib.Control.Monad.Writer
import Mathlib.Tactic

import Clap.BitVec
import Clap.eDSLState.CircuitEvalSt
import Clap.eDSLState.HashCons.CacheExpr
import Clap.eDSLState.HashCons.Eval
import Clap.eDSLState.Varstore
import Clap.eDSLState.Gate

namespace Clap

open HashConsM

abbrev Circuit (p : ℕ) := Array (Gate p)

section Clap

variable {p : ℕ}

namespace Circuit

@[grind =]
def refsValid (c : Circuit p) (bound : ℕ) : Prop :=
  ∀ gate ∈ c, gate.refsValid bound

end Circuit

/--
Hic sunt dracones.
-/
lemma stupidext (result : EvalSt p) :
  result = ⟨result.numAlloc, result.varStore, result.constraints⟩ := rfl

section CircuitEval

namespace Circuit

section Circuit

variable {circuit : Circuit p}
         {varStore Γ : VarStore p}
         {σ : HashConsSt p}
         {numAlloc : ℕ}
         {e! : ExprRef}
         {e : Expr p}
         {st : EvalSt p}

abbrev evalInOrder (circuit : Circuit p)
                   (σ : HashConsSt p)
                   (st : EvalSt p) :=
  circuit.foldl (EvalSt.step (σ := σ)) st

def eval (circuit : Circuit p) (varStore : VarStore p) (numAlloc : ℕ) (σ : HashConsSt p) : EvalSt p :=
  circuit.evalInOrder σ ⟨numAlloc, varStore, True⟩

notation "[" varStore ", " σ ", " numAlloc "|" circuit "]ₑ" => Circuit.eval circuit varStore numAlloc σ

@[grind =]
def varsAllocated (c : Circuit p) (varStore : VarStore p) (σ : HashConsSt p) (numAlloc : ℕ) : Prop :=
  ∀ i (h: i < c.size),
    c[i].varsAllocated [varStore, σ, numAlloc|(c.take i)]ₑ.varStore σ

@[aesop safe cases, grind]
structure wellFormed (circuit : Circuit p) (Γ : VarStore p) (σ : HashConsSt p) (numAlloc : ℕ) : Prop where
  refsValid : circuit.refsValid σ.size
  varsAllocated : circuit.varsAllocated Γ σ numAlloc

@[simp, grind =]
lemma wellFormed_iff :
  circuit.wellFormed Γ σ numAlloc ↔ (circuit.refsValid σ.size ∧ circuit.varsAllocated Γ σ numAlloc) := by
  grind

@[simp, grind =]
lemma eval_push_eq0_varStore
  
:
  [varStore, σ, numAlloc|circuit.push (.eq0 e!)]ₑ.varStore =
  [varStore, σ, numAlloc|circuit]ₑ.varStore
:= by
  simp [eval]

@[simp, grind =]
lemma eval_push_share_varStore
:
  [varStore, σ, numAlloc|circuit.push (.share e!)]ₑ.varStore =
  [varStore, σ, numAlloc|circuit]ₑ.varStore.insert
    [varStore, σ, numAlloc|circuit]ₑ.numAlloc
    ([varStore, σ, numAlloc|circuit]ₑ[Expr.mk e! σ]?.getD 0)
:= by
  simp [eval]

@[simp, grind =]
lemma eval_push_isZero_varStore
:
  [varStore, σ, numAlloc|circuit.push (.isZero e!)]ₑ.varStore =
  [varStore, σ, numAlloc|circuit]ₑ.varStore.insert
    [varStore, σ, numAlloc|circuit]ₑ.numAlloc
    (if [varStore, σ, numAlloc|circuit]ₑ[Expr.mk e! σ]? = some 0 then 1 else 0)
:= by
  simp [eval]
  rfl

@[simp, grind =]
lemma eval_push_num2bits_varStore
  {w : ℕ}
:
  [varStore, σ, numAlloc|circuit.push (.num2bits w e!)]ₑ.varStore =
  [varStore, σ, numAlloc|circuit]ₑ.varStore.insertMany
    ((Vector.map
      (λ x => x + [varStore, σ, numAlloc|circuit]ₑ.numAlloc)
      (Vector.range w)
    ).zip
      (num2bitsLsbPureV w
        ([varStore, σ, numAlloc|circuit]ₑ[Expr.mk e! σ]?.getD 0)
      )
    )
:= by
  simp [eval]

@[grind .]
lemma eval_varStore_insert_isSome_of_isSome
  {key : ℕ}
  {value : ZMod p}
  (h : [varStore|e].isSome)
  (h₁ : e.wellFormed)
:
  [varStore.insert key value|e].isSome
:= by
  rw [Expr.eval_eq_evalRec h₁] at h ⊢
  unfold Expr.evalRec at *
  obtain ⟨exp, wexp⟩ : ∃ a, *e = some a := by grind
  split at h
  · aesop
  · expose_names
    split at h
    · grind
    · grind
    · simp at *
      split
      · simp at h
        expose_names
        rw [show Option.map = Functor.map from rfl, Expr.binaryOp_isSome_iff] at h ⊢
        grind
      · rw [show Option.map = Functor.map from rfl, Expr.binaryOp_isSome_iff] at h ⊢
        grind
      · rw [show Option.map = Functor.map from rfl, Expr.binaryOp_isSome_iff] at h ⊢
        grind

@[simp, grind =]
lemma insertMany_vector_list
  {k : ℕ} {arr : List (ℕ × ZMod p)}
          {harr : {toList := arr : Array _}.size = k} :
  varStore.insertMany (Vector.mk {toList := arr} harr) =
  varStore.insertMany arr := by
  simp [Std.ExtTreeMap.insertMany, Std.ExtDTreeMap.Const.insertMany]

@[aesop simp, grind .]
lemma eval_varStore_insertMany_isSome_of_isSome
  {k : ℕ}
  {inserts : Vector (ℕ × (ZMod p)) k}
  (h : [varStore|e].isSome = true)
  (h₁ : e.wellFormed) 
:
  [varStore.insertMany inserts|e].isSome = true
:= by
  rcases inserts with ⟨⟨arr⟩, harr⟩
  rw [insertMany_vector_list]
  clear harr
  induction' h : arr.length with n ih generalizing arr
  . grind
  . have : arr = arr.take (arr.length - 1) ++ [arr.getLast (by grind)] := by simp
    grind

lemma eval_empty
:
  [varStore, σ, numAlloc|#[]]ₑ =
  ⟨numAlloc, varStore, True⟩
:= rfl

lemma eval_varStore_eval_insert_isSome_of_isSome
  {p : ℕ}
  {varStore : VarStore p}
  {σ : HashConsSt p}
  {numAlloc : ℕ}
  {circuit : Circuit p}
  {e : ExprRef}
  {key : ℕ}
  {value : ZMod p}
  (h_lt : e < σ.size)
  (h : [[varStore, σ, numAlloc|circuit]ₑ.varStore,σ|e].isSome = true)
  (h_key : key ≥ numAlloc)
:
  [[varStore.insert key value, σ, numAlloc|circuit]ₑ.varStore, σ|e].isSome = true
:= by
  obtain ⟨circuit⟩ := circuit
  rewrite [←List.reverse_reverse circuit] at ⊢ h
  apply HashConsM.isSome_eval_of_isSome_eval_subset h h_lt
  induction' h_head_tail : circuit.reverse with head tail h_tail
  . simp [eval_empty]
    sorry
    done
  . sorry
    done

@[grind .]
lemma _root_.Clap.Gate.varsAllocated_step_of_wellFormed
  {gate1 gate2 : Gate p}
  (h_wf : gate2.wellFormed st.varStore σ)
:
  gate2.varsAllocated [st, σ|gate1]ₛ.varStore σ
:= by
  grind

@[grind .]
lemma _root_.Clap.Gate.wellFormed_step_of_wellFormed
  {gate1 gate2 : Gate p}
  (h_wf : gate2.wellFormed st.varStore σ)
:
  gate2.wellFormed [st, σ|gate1]ₛ.varStore σ
:= by
  grind

variable {gate : Gate p} {Γ₁ Γ₂ Γ₃ : VarStore p}

@[grind →]
lemma precedes_trans (h₁ : [σ|Γ₁ ⊑ Γ₂]) (h₂ : [σ|Γ₂ ⊑ Γ₃]) : [σ|Γ₁ ⊑ Γ₃] := by grind

@[grind .]
lemma precedes_rfl : [σ|Γ ⊑ Γ] := by grind

-- example
--   {σ : HashConsSt p}
--   {numAlloc1 numAlloc2 : ℕ}
--   {circuit : Circuit p}
--   (h_wf : circuit.wellFormed Γ₁ σ numAlloc1)
--   (h : [σ|Γ₁ ⊑ Γ₂])
-- :
--   circuit.varsAllocated Γ₂ σ numAlloc2
-- := by
--   unfold varsAllocated
--   intro i h_i
--   induction' i with size h_size generalizing circuit
--   . simp [eval]
--     simp at h_wf
--     unfold refsValid at h_wf
--     unfold varsAllocated at h_wf
--     have := h_wf.2 0 (by assumption)
--     simp [eval] at this
--     apply Gate.varsAllocated_of_wellFormed_precedes
--       (by grind)
--       h
--   . have : circuit.take (size + 1) = (circuit.take size).push circuit[size] := by grind
--     rewrite [this]
--     have :
--       [Γ₂, σ, numAlloc2|(Array.take circuit size).push circuit[size]]ₑ =
--       [[Γ₂, σ, numAlloc2|(Array.take circuit size)]ₑ, σ|circuit[size]]ₛ
--     := by
--       unfold eval
--       grind
--     rewrite [this]
--     apply Gate.varsAllocated_step_of_wellFormed
--     simp only [Gate.wellFormed_iff]
--     split_ands
--     · grind
--     . refine Gate.varsAllocated_of_wellFormed_precedes (varStore1 := Γ₁) ⟨by grind, ?p₂⟩ ?p₃ 
--       simp at h_wf
--       unfold Circuit.varsAllocated at h_wf
--       rcases h_wf with ⟨l, r⟩
--       specialize r (size + 1) (by grind)
      
--       simp at h_wf ⊢ --(by grind) (h_varsAllocated (size+1) h_i)
--       split_ands
--       grind
--       intro e h_e h_varStore1
      
        


--       done
--     done
--     -- have : Circuit.refsValid (circuit.take size) σ.size := by grind
--     -- specialize ih_size this (by grind) (by grind)
--     -- unfold varsAllocated
--     -- intro i h_i
--     -- by_cases i = size
--     -- . subst i
--     --   cases circuit[size]
--     --   . simp [Gate.varsAllocated]
--     --     simp [varsAllocated] at ih_size
--     --   done
--     -- . convert ih_size i (by grind) using 1
--     --   . grind
--     --   . grind
--     --   done
--     -- done

-- lemma varsAllocated_eval_append_left
--   {p i : ℕ}
--   {circuit a : Circuit p}
--   {varStore : VarStore p}
--   {σ : HashConsSt p}
--   {numAlloc : ℕ}
--   {h_get}
--   (h₀ : circuit.refsValid σ.size)
--   (h : (circuit[i]'h_get).varsAllocated [varStore, σ, numAlloc|circuit.extract 0 i]ₑ.varStore σ)
-- :
--   (circuit[i]'h_get).varsAllocated [varStore, σ, numAlloc|a ++ circuit.extract 0 i]ₑ.varStore σ
-- := by
--   unfold Gate.varsAllocated at h ⊢
--   rcases a with ⟨a⟩
--   induction' a with hd tl ih
--   · grind
--   · split <;> expose_names <;> simp at *
--     simp [heq] at ih
--     · rw [HashConsM.isSome_eval_of_isSome_eval_subset ih (by grind)]
--       suffices
--         [varStore, σ, numAlloc|⟨tl⟩ ++ Array.extract circuit 0 i]ₑ.varStore ⊆
--         [varStore, σ, numAlloc|#[hd] ++ (⟨tl⟩ ++ Array.extract circuit 0 i)]ₑ.varStore by
--         grind

--       grind
--     all_goals sorry

--     -- all_goals {
--     --   rw [HashConsM.isSome_eval_of_isSome_eval_subset]
--     -- }
--   done

lemma varsAllocated_eval_append_right
  {i : ℕ}
  {a : Circuit p}
  {h_get : i < circuit.size}
  (h₀ : circuit.refsValid σ.size)
  (h : (circuit[i]'h_get).varsAllocated [varStore, σ, numAlloc|circuit.extract 0 i]ₑ.varStore σ)
:
  (circuit[i]'h_get).varsAllocated [varStore, σ, numAlloc|circuit.extract 0 i ++ a]ₑ.varStore σ
:= by
  obtain ⟨a⟩ := a
  rewrite [←List.reverse_reverse a]
  induction' a.reverse with head tail h_tail
  . simp [h]
  . suffices (circuit[i]'h_get).varsAllocated [varStore, σ, numAlloc|circuit.extract 0 i ++ ⟨tail.reverse⟩ ++ #[head]]ₑ.varStore σ by grind
    simp [Gate.varsAllocated] at h_tail ⊢
    have (a: Array (Gate p)) (l : List (Gate p)) (gate : Gate p)
      : a ++ (l ++ [gate]).toArray = (a ++ ⟨l⟩).push gate
    := by grind
    split <;> cases head
    all_goals (
      expose_names
      rewrite [this]
      set x := circuit.extract 0 i ++ ⟨tail.reverse⟩
      have : e < σ.size := by grind
      simp_all [eval_varStore_insert_isSome_of_isSome, eval_varStore_insertMany_isSome_of_isSome]
    )

/--
TODO: In terms of `Circuit.wellFormed`
-/
lemma Circuit.varsAllocated_append {p : ℕ}
  (a b : Circuit p)
  {varStore : VarStore p}
  {σ : HashConsSt p}
  {numAlloc : ℕ}
  (h₀ : a.refsValid σ.size)
  (h₁ : b.refsValid σ.size)
  (h_a : a.varsAllocated varStore σ numAlloc)
  (h_b : b.varsAllocated varStore σ numAlloc)
:
  (a ++ b).varsAllocated varStore σ numAlloc
:= by
  simp [varsAllocated] at ⊢ h_a h_b
  . intro i h_i
    simp [Array.getElem_append]
    split_ifs with h_i'
    . specialize h_a i h_i'
      exact varsAllocated_eval_append_right h₀ h_a
    . specialize h_b (i - a.size) (by omega)
      simp (disch := omega) [Array.extract_eq_self_of_le]
      exact varsAllocated_eval_append_left h_b

end

end Circuit
end CircuitEval

namespace Edsl.EvalSt

variable {p pc numAlloc : ℕ} {σ : HashConsSt p} {constraints constraints1 constraints2 : Prop}
         {varStore : VarStore p} {circuit : Circuit p} {e! : ExprRef} {gate : Gate p}
         {result : EvalSt p}

@[ext, grind ext]
lemma ext {p : ℕ} {r1 r2 : EvalSt p}
  (h_numAlloc : r1.numAlloc = r2.numAlloc)
  (h_varStore : r1.varStore = r2.varStore)
  (h_constraints : r1.constraints = r2.constraints)
:
  r1 = r2
:= by
  grind [cases EvalSt]

lemma evalInOrder_step_numAlloc_independent_of_constraints
:
  (Circuit.evalInOrder circuit σ ⟨numAlloc, varStore, constraints1⟩).numAlloc =
  (Circuit.evalInOrder circuit σ ⟨numAlloc, varStore, constraints2⟩).numAlloc
:= by
  rcases circuit with ⟨circuit⟩
  unfold Circuit.evalInOrder
  simp only [List.size_toArray]
  rewrite [←List.reverse_reverse circuit]
  induction' circuit.reverse <;> aesop (add safe (by grind))

lemma foldl_step_numAlloc_independent_of_constraints {circuit : List (Gate p)}
:
  (circuit.foldl (fun result next => [result, σ|next]ₛ) ⟨numAlloc, varStore, constraints1⟩).numAlloc =
  (circuit.foldl (fun result next => [result, σ|next]ₛ) ⟨numAlloc, varStore, constraints2⟩).numAlloc
:= by
  have := @evalInOrder_step_numAlloc_independent_of_constraints (circuit := ⟨circuit⟩) (σ := σ)
  aesop

lemma foldr_step_numAlloc_independent_of_constraints
:
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints1⟩ circuit).numAlloc =
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints2⟩ circuit).numAlloc
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  rw [show Array.mk circuit.reverse.reverse = Array.reverse ⟨circuit.reverse⟩ by simp]
  simp only [Array.foldr_reverse]
  exact evalInOrder_step_numAlloc_independent_of_constraints

lemma foldr_step_numAlloc_independent_of_constraints'
:
  (List.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints1⟩ circuit.toList).numAlloc =
  (List.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints2⟩ circuit.toList).numAlloc
:= by
  simp only [Array.foldr_toList]
  exact foldr_step_numAlloc_independent_of_constraints

lemma evalInOrder_step_varStore_independent_of_constraints
:
  (Circuit.evalInOrder circuit σ ⟨numAlloc, varStore, constraints1⟩).varStore =
  (Circuit.evalInOrder circuit σ ⟨numAlloc, varStore, constraints2⟩).varStore
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  induction circuit.reverse <;> aesop (config := { warnOnNonterminal := false}) (add safe (by grind))
  cases head
  . grind
  . simp [tail_ih, foldr_step_numAlloc_independent_of_constraints' (constraints2 := constraints2), EvalSt.getD, EvalSt.get?]
  . simp [tail_ih, foldr_step_numAlloc_independent_of_constraints' (constraints2 := constraints2), GetElem?.getElem?, EvalSt.get?]
    rfl
  . simp [tail_ih, foldr_step_numAlloc_independent_of_constraints' (constraints2 := constraints2), GetElem?.getElem?, EvalSt.get?]

lemma foldl_step_varStore_independent_of_constraints {circuit : List (Gate p)}
:
  (circuit.foldl (fun result next => [result, σ|next]ₛ) ⟨numAlloc, varStore, constraints1⟩).varStore =
  (circuit.foldl (fun result next => [result, σ|next]ₛ) ⟨numAlloc, varStore, constraints2⟩).varStore
:= by
  have := @evalInOrder_step_varStore_independent_of_constraints (circuit := ⟨circuit⟩) (σ := σ)
  aesop

lemma foldr_step_varStore_independent_of_constraints
:
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints1⟩ circuit).varStore =
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints2⟩ circuit).varStore
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  rw [show Array.mk circuit.reverse.reverse = Array.reverse ⟨circuit.reverse⟩ by simp]
  simp only [Array.foldr_reverse]
  exact evalInOrder_step_varStore_independent_of_constraints

lemma foldr_step_varStore_independent_of_constraints'
:
  (List.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints1⟩ circuit.toList).varStore =
  (List.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints2⟩ circuit.toList).varStore
:= by
  simp only [Array.foldr_toList]
  exact foldr_step_varStore_independent_of_constraints

@[grind .]
lemma getElem_foldr_independent_of_constraints
:
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints1⟩ circuit)[(e!, σ)]? =
  (Array.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints2⟩ circuit)[(e!, σ)]?
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  rw [show Array.mk circuit.reverse.reverse = Array.reverse ⟨circuit.reverse⟩ by simp]
  simp only [Array.foldr_reverse]
  simp [GetElem?.getElem?, get?]
  rw [foldr_step_varStore_independent_of_constraints']

/--
This exists to appease `grind`.

NB this is useless now.
-/
-- @[grind! .] -- I don't think there's an easy way to teach grind about the `σ` under the lambda
lemma foldr_step_varStore_independent_of_constraints''
  {circuit : Circuit p}
  {σ₁ σ₂ : EvalSt p}
  (h₁ : σ₁.numAlloc = σ₂.numAlloc)
  (h₂ : σ₁.varStore = σ₂.varStore)
:
  (Array.foldr (λ x y => [y, σ|x]ₛ) σ₁ circuit).varStore =
  (Array.foldr (λ x y => [y, σ|x]ₛ) σ₂ circuit).varStore
:= by
  convert foldr_step_varStore_independent_of_constraints using 4 <;> grind

lemma foldr_step_varStore_independent_of_constraints'''
  {circuit : Circuit p}
  {σ₁ σ₂ : EvalSt p}
  (h₁ : σ₁.numAlloc = σ₂.numAlloc)
  (h₂ : σ₁.varStore = σ₂.varStore) :
  (List.foldr (λ x y => [y, σ|x]ₛ) σ₁ circuit.toList).varStore =
  (List.foldr (λ x y => [y, σ|x]ₛ) σ₂ circuit.toList).varStore := by
  simp [Array.foldr_toList]
  apply foldr_step_varStore_independent_of_constraints'' <;> grind

@[simp, grind .]
lemma isSome_foldr_split {result : EvalSt p} {circuit : Circuit p} {e : ExprRef} :
  (List.foldr (fun x y => [y, σ|x]ₛ) result.split circuit.toList)[(e, σ)]?.isSome ↔
  (List.foldr (fun x y => [y, σ|x]ₛ) result circuit.toList)[(e, σ)]?.isSome := by
  rcases result
  simp [split]
  grind

@[simp, grind .]
lemma isSome_foldr_split' {result : EvalSt p} {circuit : Circuit p} {e : ExprRef} :
  (Array.foldr (fun x y => [y, σ|x]ₛ) result.split circuit)[(e, σ)]?.isSome ↔
  (Array.foldr (fun x y => [y, σ|x]ₛ) result circuit)[(e, σ)]?.isSome := by
  rcases result
  simp [split]
  grind

lemma evalInOrder_step_constraints_and
:
  (Circuit.evalInOrder circuit σ result).constraints = (
    result.constraints ∧
    (Circuit.evalInOrder circuit σ result.split).constraints
  )
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  induction circuit.reverse
  . simp
  next hd tl ih =>
    simp at *
    rcases hd with _ | _ | _ | _
    · simp
      unfold GetElem?.getElem?
      unfold instGetElem?ProdExprRefHashConsStZModMem
      rw [Array.foldr_toList, Array.foldr_toList]
      simp [get?]
      rw [ih]
      rw [foldr_step_varStore_independent_of_constraints''' (σ₂ := result.split)] <;>
      aesop
    · rw [Array.foldr_toList, Array.foldr_toList]
      simp [ih]
      expose_names
      rw [isSome_foldr_split]
      aesop
    · simp only [step_isZero]
      unfold GetElem?.getElem?
      unfold instGetElem?ProdExprRefHashConsStZModMem
      rw [Array.foldr_toList, Array.foldr_toList]
      grind [GetElem?.getElem?, instGetElemProdExprRefHashConsStZModMem]
    · simp
      unfold GetElem?.getElem?
      rw [Array.foldr_toList, Array.foldr_toList]
      grind

lemma foldl_step_constraints_and {circuit : List (Gate p)} :
  (circuit.foldl (fun result next => [result, σ|next]ₛ) result).constraints =
  (result.constraints ∧ (circuit.foldl (fun result next => [result, σ|next]ₛ) result.split).constraints) := by
  have := @evalInOrder_step_constraints_and (circuit := ⟨circuit⟩) (σ := σ) (result := result)
  aesop

@[grind .]
lemma abc {p} {varStore : VarStore p} {σ : HashConsSt p} {numAlloc : ℕ}
              {a b : Circuit p} :
  [varStore, σ, numAlloc|b]ₑ.varStore ⊆
  [varStore, σ, numAlloc|a ++ b]ₑ.varStore := by
  intros i h
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  induction' a with hd tl ih
  · simp
  · rw [show ⟨hd :: tl⟩ ++ ⟨b⟩ = #[hd] ++ (⟨tl⟩ ++ ⟨b⟩) by grind]
    rcases hd with e | e | e | ⟨w, e⟩
    · simp [ih]
      unfold Circuit.eval
      simp
      have :
        (List.foldl (fun result next => [result, σ|next]ₛ)
        { numAlloc := numAlloc, varStore := varStore, constraints := [varStore,σ|e] = some 0 } tl) =
        ({
          numAlloc := (List.foldl (fun result next => [result, σ|next]ₛ)
          { numAlloc := numAlloc, varStore := varStore, constraints := True } tl).numAlloc,
          varStore := (List.foldl (fun result next => [result, σ|next]ₛ)
          { numAlloc := numAlloc, varStore := varStore, constraints := True } tl).varStore,
          constraints := [varStore,σ|e] = some 0 ∧ (List.foldl (fun result next => [result, σ|next]ₛ)
          { numAlloc := numAlloc, varStore := varStore, constraints := True } tl).constraints }) := by
        rw [stupidext (result := List.foldl (fun result next => [result, σ|next]ₛ)
          { numAlloc := numAlloc, varStore := varStore, constraints := [varStore,σ|e] = some 0 } tl)]
        congr 1
        apply foldl_step_numAlloc_independent_of_constraints
        apply foldl_step_varStore_independent_of_constraints
        apply foldl_step_constraints_and
      rw [this]
      rw [foldl_step_varStore_independent_of_constraints]
    · simp [ih]
      unfold Circuit.eval
      simp [-List.foldl_append]
      simp [ih] at h
      clear ih
      set l := tl ++ b
      rw [←List.reverse_reverse l]
      induction' l.reverse with hd tl ih
      · simp

      done
    · done

  done


end Edsl.EvalSt

namespace Circuit

variable {p numAlloc : ℕ} {circuit1 circuit2 : Circuit p} {varStore : VarStore p}
         {σ : HashConsSt p}

def seq (circuit₁ circuit₂ : Circuit p)
        (varStore : VarStore p)
        (numAlloc : ℕ)
        (σ : HashConsSt p)
: Edsl.EvalSt p :=
  let ⟨numAllocMid, varStoreMid, constraintsMid⟩ := [varStore, σ, numAlloc| circuit₁]ₑ
  let ⟨numAllocPost, varStorePost, constraintsPost⟩ := [varStoreMid, σ, numAllocMid| circuit₂]ₑ
  ⟨numAllocPost, varStorePost, constraintsMid ∧ constraintsPost⟩

syntax "[" term ", " term ", " term "|" term "; " term "]" : term
macro_rules
  | `(term| [$Γ, $σ, $numAlloc | $c₁; $c₂]) => `(seq $c₁ $c₂ $Γ $numAlloc $σ)

@[app_unexpander seq]
def unexpandSeq : Lean.PrettyPrinter.Unexpander
  | `($_ $c₁ $c₂ $Γ $numAlloc $σ) =>
    `([$Γ, $numAlloc, $σ | $c₁; $c₂])
  | _ => throw ()

@[simp]
lemma numAlloc_seq :
  [varStore, σ, numAlloc | circuit1; circuit2].numAlloc =
  let mid := [varStore, σ, numAlloc|circuit1]ₑ
  [mid.varStore, σ, mid.numAlloc|circuit2]ₑ.numAlloc
:= rfl

@[simp]
lemma varStore_seq :
  (Circuit.seq circuit1 circuit2 varStore numAlloc σ).varStore =
  let mid := [varStore, σ, numAlloc|circuit1]ₑ
  [mid.varStore, σ, mid.numAlloc|circuit2]ₑ.varStore
:= rfl

@[simp, grind=]
lemma constraints_seq :
  (Circuit.seq circuit1 circuit2 varStore numAlloc σ).constraints =
  let mid := [varStore, σ, numAlloc|circuit1]ₑ
  mid.constraints ∧ [mid.varStore, σ, mid.numAlloc|circuit2]ₑ.constraints
:= rfl

@[simp, grind =]
lemma eval_append
:
  [varStore, σ, numAlloc | circuit1 ++ circuit2]ₑ = seq circuit1 circuit2 varStore numAlloc σ
:= by
  simp [eval]
  ext1
  all_goals dsimp [seq]
  . exact Edsl.EvalSt.foldl_step_numAlloc_independent_of_constraints
  . exact Edsl.EvalSt.foldl_step_varStore_independent_of_constraints
  . exact Edsl.EvalSt.foldl_step_constraints_and

@[simp high, grind =]
lemma eval_singleton
  {numAlloc}
  {command : Gate p}
  {varStore}
  {σ}
:
  [varStore, σ, numAlloc | #[command]]ₑ =
  [unconstrained[numAlloc][varStore], σ | command]ₛ := by
  simp [eval, Edsl.EvalSt.step_unconstrained]

@[simp, grind =]
lemma eval_cons
  {numAlloc}
  {command : Gate p}
  {circuit : Circuit p}
  {varStore}
  {σ}
:
  [varStore, σ, numAlloc | ⟨command :: circuit.toList⟩]ₑ =
  seq #[command] circuit varStore numAlloc σ:= by
  rw [show ⟨command :: circuit.toList⟩ = #[command] ++ circuit by simp]
  exact eval_append

section

variable {numAlloc : ℕ} {varStore : VarStore p} {e: ExprRef} {σ : HashConsSt p}

@[simp, grind =]
lemma eval_empty :
  [varStore, σ, numAlloc | #[]]ₑ = unconstrained[numAlloc][varStore]
:= by rfl

@[simp, grind =]
lemma eval_empty_collection :
  [varStore, σ, numAlloc | ∅]ₑ =
  unconstrained[numAlloc][varStore]
:= by rfl

@[simp, grind =]
lemma eval_eq0 :
  [varStore, σ, numAlloc | #[.eq0 e]]ₑ =
  unconstrained[numAlloc][varStore].step (.eq0 e) σ
:= by simp [eval, Edsl.EvalSt.addConstraint_unconstrained]

@[simp, grind =]
lemma eval_share :
  [varStore, σ, numAlloc | #[.share e]]ₑ =
  unconstrained[numAlloc][varStore].step (.share e) σ
:= by
  simp [eval]

@[simp, grind =]
lemma eval_isZero :
  [varStore, σ, numAlloc | #[.isZero e]]ₑ =
  unconstrained[numAlloc][varStore].step (.isZero e) σ
:= by
  simp [eval]
  rfl

@[simp, grind =]
lemma eval_num2bits {width : ℕ} :
  [varStore, σ, numAlloc | #[.num2bits width e]]ₑ =
  unconstrained[numAlloc][varStore].step (.num2bits width e) σ
:= by
  simp [eval]

@[simp, grind =]
lemma seq_cons_nil {cmd : Gate p} {circuit : Circuit p} {varStore} {numAlloc} :
  seq (⟨cmd :: circuit.toList⟩) #[] varStore numAlloc σ =
  seq #[cmd] circuit varStore numAlloc σ := by
  aesop (add simp seq)

@[simp high, grind =]
lemma seq_singleton_nil {cmd : Gate p} {varStore} {numAlloc} :
  seq #[cmd] #[] varStore numAlloc σ =
  [varStore, σ, numAlloc| #[cmd]]ₑ := by
  simp [seq]

end

-- TODO prove for eval
-- TODO move up
lemma step_of_refsValid_prefix
  {σ σ' : HashConsSt p}
  {circuit : Gate p}
  {result: Edsl.EvalSt p}
  (h_prefix : σ.exprs.isPrefixOf σ'.exprs)
  (h_refsValid : circuit.refsValid (σ.exprs.size))
:
  [result, σ'|circuit]ₛ =
  [result, σ|circuit]ₛ
:= by
  unfold Edsl.EvalSt.step
  cases circuit
  all_goals {
    simp
    expose_names
    have : e < σ.exprs.size := by
      unfold Gate.refsValid at h_refsValid
      grind
    have : result[(e, σ')]? = result[(e, σ)]? := by
      unfold_projs
      simp [Edsl.EvalSt.get?, HashConsM.eval]
      congr 1
      symm
      exact HashConsM.evalCache_of_lt_prefix h_prefix this
    grind
  }

@[simp, grind _=_]
lemma refsValid_append_iff {a b : Circuit p} {numAlloc : ℕ}
:
  (a ++ b).refsValid numAlloc ↔
  a.refsValid numAlloc ∧ b.refsValid numAlloc
:= by
  grind

end Circuit

end Circuit

end Clap

end Clap
