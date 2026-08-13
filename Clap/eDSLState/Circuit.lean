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

@[grind =]
def numAllocStep (c : Circuit p) : ℕ :=
  (c.map Gate.numAllocStep).sum

@[simp, grind =]
lemma numAllocStep_singleton {gate : Gate p}
:
  numAllocStep #[gate] =
  gate.numAllocStep
:= by grind

@[simp, grind =]
lemma numAllocStep_singleton_list {gate : Gate p}
:
  numAllocStep ⟨[gate]⟩ =
  gate.numAllocStep
:= by grind

@[simp, grind =]
lemma numAllocStep_append {c1 c2: Circuit p}
:
  numAllocStep (c1 ++ c2) =
  numAllocStep c1 + numAllocStep c2
:= by grind

@[simp, grind =]
lemma numAllocStep_append_list {l1 l2 : List (Gate p)}
:
  numAllocStep ⟨l1 ++ l2⟩ =
  numAllocStep ⟨l1⟩ + numAllocStep ⟨l2⟩
:= by grind

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

@[simp, grind =]
lemma eval_numAlloc
  {circuit : Circuit p}
:
  [varStore, σ, numAlloc|circuit]ₑ.numAlloc =
  numAlloc + circuit.numAllocStep
:= by
  obtain ⟨circuit⟩ := circuit
  rewrite [←circuit.reverse_reverse]
  induction' circuit.reverse with body tail h_body
  . grind [=eval]
  . grind [=eval]

@[simp, grind =]
lemma eval_varStore_keys
  {circuit : Circuit p}
:
  [varStore, σ, numAlloc|circuit]ₑ.varStore.keys.toFinset =
  varStore.keys.toFinset ∪ (List.range' numAlloc circuit.numAllocStep).toFinset
:= by
  obtain ⟨circuit⟩ := circuit
  rewrite [←circuit.reverse_reverse]
  induction' circuit.reverse with head tail h_tail
  . simp [eval, numAllocStep]
  . simp [numAllocStep, eval] at ⊢ h_tail
    simp [h_tail]; clear h_tail
    congr
    ext
    have := @eval_numAlloc _ varStore σ numAlloc ⟨tail.reverse⟩
    simp [eval] at this
    simp [this]; clear this
    expose_names
    simp [numAllocStep]
    grind

@[simp, grind =]
lemma mem_eval_varStore
  {circuit : Circuit p}
  {k}
:
  k ∈ [varStore, σ, numAlloc|circuit]ₑ.varStore ↔
  (k ∈ varStore ∨ (numAlloc ≤ k ∧ k < numAlloc + circuit.numAllocStep))
:= by
  simp [VarStore.mem_iff_mem_keys, -Std.ExtTreeMap.mem_keys, ←List.mem_toFinset]
  aesop

@[grind =]
def varsAllocated (c : Circuit p) (varStore : VarStore p) (σ : HashConsSt p) (numAlloc : ℕ) : Prop :=
  ∀ i (h : i < c.size),
    letI evalSt := [varStore, σ, numAlloc|c.take i]ₑ
    c[i].varsAllocated evalSt.varStore σ ∧
    ∀ x ∈ Expr.varSet ⟨c[i].expr, σ⟩, x < evalSt.numAlloc

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

@[simp, grind =]
lemma eval_empty :
  [varStore, σ, numAlloc | #[]]ₑ = unconstrained[numAlloc][varStore]
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
:
  [[varStore.insert key value, σ, numAlloc|circuit]ₑ.varStore, σ|e].isSome = true
:= by
  grind

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
    have : circuit[i].expr < σ.size := by
      aesop (add safe (by grind))
    grind

end Circuit

end Circuit

namespace EvalSt

variable {p pc numAlloc : ℕ} {σ : HashConsSt p} {constraints constraints1 constraints2 : Prop}
         {varStore : VarStore p} {circuit : Circuit p} {e! : ExprRef} {gate : Gate p}
         {st : EvalSt p}

@[ext, grind ext]
lemma ext {p : ℕ} {r1 r2 : EvalSt p}
  (h_numAlloc : r1.numAlloc = r2.numAlloc)
  (h_varStore : r1.varStore = r2.varStore)
  (h_constraints : r1.constraints = r2.constraints)
:
  r1 = r2
:= by
  grind [cases EvalSt]

lemma evalInOrder_numAlloc_independent_of_constraints
:
  (circuit.evalInOrder σ ⟨numAlloc, varStore, constraints1⟩).numAlloc =
  (circuit.evalInOrder σ ⟨numAlloc, varStore, constraints2⟩).numAlloc
:= by
  rcases circuit with ⟨circuit⟩
  unfold Circuit.evalInOrder
  simp only [List.size_toArray]
  rewrite [←List.reverse_reverse circuit]
  induction' circuit.reverse <;> aesop (add safe (by grind))

lemma foldl_step_numAlloc_independent_of_constraints' {circuit : List (Gate p)}
:
  (circuit.foldl (fun result next => [result, σ|next]ₛ) ⟨numAlloc, varStore, constraints1⟩).numAlloc =
  (circuit.foldl (fun result next => [result, σ|next]ₛ) ⟨numAlloc, varStore, constraints2⟩).numAlloc
:= by
  have := @evalInOrder_numAlloc_independent_of_constraints (circuit := ⟨circuit⟩) (σ := σ)
  grind

lemma foldr_step_numAlloc_independent_of_constraints
:
  (circuit.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints1⟩).numAlloc =
  (circuit.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints2⟩).numAlloc
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  rw [show Array.mk circuit.reverse.reverse = Array.reverse ⟨circuit.reverse⟩ by simp]
  simp only [Array.foldr_reverse]
  exact evalInOrder_numAlloc_independent_of_constraints

lemma foldr_step_numAlloc_independent_of_constraints'
:
  (circuit.toList.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints1⟩).numAlloc =
  (circuit.toList.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints2⟩).numAlloc
:= by
  simp only [Array.foldr_toList]
  exact foldr_step_numAlloc_independent_of_constraints

lemma evalInOrder_varStore_independent_of_constraints
:
  (circuit.evalInOrder σ ⟨numAlloc, varStore, constraints1⟩).varStore =
  (circuit.evalInOrder σ ⟨numAlloc, varStore, constraints2⟩).varStore
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
  have := @evalInOrder_varStore_independent_of_constraints (circuit := ⟨circuit⟩) (σ := σ)
  aesop

lemma foldr_step_varStore_independent_of_constraints
:
  (circuit.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints1⟩).varStore =
  (circuit.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints2⟩).varStore
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  rw [show Array.mk circuit.reverse.reverse = Array.reverse ⟨circuit.reverse⟩ by simp]
  simp only [Array.foldr_reverse]
  exact evalInOrder_varStore_independent_of_constraints

lemma foldr_step_varStore_independent_of_constraints'
:
  (circuit.toList.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints1⟩).varStore =
  (circuit.toList.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints2⟩).varStore
:= by
  simp only [Array.foldr_toList]
  exact foldr_step_varStore_independent_of_constraints

@[grind .]
lemma getElem_foldr_independent_of_constraints
:
  (circuit.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints1⟩)[Expr.mk e! σ]? =
  (circuit.foldr (λ x y => [y, σ|x]ₛ) ⟨numAlloc, varStore, constraints2⟩)[Expr.mk e! σ]?
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
  (circuit.foldr (λ x y => [y, σ|x]ₛ) σ₁).varStore =
  (circuit.foldr (λ x y => [y, σ|x]ₛ) σ₂).varStore
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
lemma isSome_foldr_split :
  (circuit.toList.foldr (fun x y => [y, σ|x]ₛ) st.split)[Expr.mk e! σ]?.isSome ↔
  (circuit.toList.foldr (fun x y => [y, σ|x]ₛ) st)[Expr.mk e! σ]?.isSome := by
  rcases st
  simp [split]
  grind

@[simp, grind .]
lemma isSome_foldr_split' :
  (circuit.foldr (fun x y => [y, σ|x]ₛ) st.split)[Expr.mk e! σ]?.isSome ↔
  (circuit.foldr (fun x y => [y, σ|x]ₛ) st)[Expr.mk e! σ]?.isSome := by
  rcases st
  simp [split]
  grind

lemma evalInOrder_constraints_and
:
  (circuit.evalInOrder σ st).constraints = (
    st.constraints ∧
    (circuit.evalInOrder σ st.split).constraints
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
      unfold instGetElem?ExprZModMem
      rw [Array.foldr_toList, Array.foldr_toList]
      simp [get?]
      rw [ih]
      rw [foldr_step_varStore_independent_of_constraints''' (σ₂ := st.split)] <;>
      aesop
    · rw [Array.foldr_toList, Array.foldr_toList]
      simp [ih]
      expose_names
      rw [isSome_foldr_split]
      aesop
    · simp only [step_isZero]
      unfold GetElem?.getElem?
      unfold instGetElem?ExprZModMem
      rw [Array.foldr_toList, Array.foldr_toList]
      grind [GetElem?.getElem?, instGetElemExprZModMem]
    · simp
      unfold GetElem?.getElem?
      rw [Array.foldr_toList, Array.foldr_toList]
      grind

lemma foldl_step_constraints_and {circuit : List (Gate p)} :
  (circuit.foldl (fun result next => [result, σ|next]ₛ) st).constraints =
  (st.constraints ∧ (circuit.foldl (fun result next => [result, σ|next]ₛ) st.split).constraints) := by
  have := @evalInOrder_constraints_and (circuit := ⟨circuit⟩) (σ := σ) (st := st)
  aesop

/-
TODO: TODO
-/
/-
@[grind .]
lemma abc {varStore : VarStore p} {σ : HashConsSt p} {numAlloc : ℕ} {a b : Circuit p} :
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
        rw [stupidext (st := List.foldl (fun result next => [result, σ|next]ₛ)
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
-/
end EvalSt

namespace Circuit

variable {numAlloc : ℕ} {circuit1 circuit2 : Circuit p} {varStore : VarStore p}
         {σ : HashConsSt p}

def seq (circuit₁ circuit₂ : Circuit p)
        (varStore : VarStore p)
        (numAlloc : ℕ)
        (σ : HashConsSt p)
: EvalSt p :=
  let ⟨numAllocMid, varStoreMid, constraintsMid⟩ := [varStore, σ, numAlloc| circuit₁]ₑ
  let ⟨numAllocPost, varStorePost, constraintsPost⟩ := [varStoreMid, σ, numAllocMid| circuit₂]ₑ
  ⟨numAllocPost, varStorePost, constraintsMid ∧ constraintsPost⟩

syntax "[" term ", " term ", " term "|" term "; " term "]ₑ" : term
macro_rules
  | `(term| [$Γ, $σ, $numAlloc | $c₁; $c₂]ₑ) => `(seq $c₁ $c₂ $Γ $numAlloc $σ)

@[app_unexpander seq]
def unexpandSeq : Lean.PrettyPrinter.Unexpander
  | `($_ $c₁ $c₂ $Γ $numAlloc $σ) =>
    `([$Γ, $numAlloc, $σ | $c₁; $c₂]ₑ)
  | _ => throw ()

@[simp]
lemma numAlloc_seq :
  [varStore, σ, numAlloc | circuit1; circuit2]ₑ.numAlloc =
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
  . exact EvalSt.evalInOrder_numAlloc_independent_of_constraints
  . exact EvalSt.evalInOrder_varStore_independent_of_constraints
  . exact EvalSt.evalInOrder_constraints_and

variable {gate : Gate p}

@[simp high, grind =]
lemma eval_singleton
:
  [varStore, σ, numAlloc | #[gate]]ₑ =
  [unconstrained[numAlloc][varStore], σ | gate]ₛ := by
  simp [eval, EvalSt.step_unconstrained]

@[simp, grind =]
lemma eval_cons {circuit : Circuit p}
:
  [varStore, σ, numAlloc | ⟨gate :: circuit.toList⟩]ₑ =
  seq #[gate] circuit varStore numAlloc σ:= by
  rw [show ⟨gate :: circuit.toList⟩ = #[gate] ++ circuit by simp]
  exact eval_append

@[simp, grind =]
lemma eval_cons' {circuit_list : List (Gate p)}
:
  [varStore, σ, numAlloc | ⟨gate :: circuit_list⟩]ₑ =
  seq #[gate] circuit_list.toArray varStore numAlloc σ
:= by
  convert eval_cons

section

variable {numAlloc : ℕ} {varStore : VarStore p} {e : Expr p} {e! : ExprRef} {σ : HashConsSt p}

@[simp, grind =]
lemma eval_empty_collection :
  [varStore, σ, numAlloc | ∅]ₑ =
  unconstrained[numAlloc][varStore]
:= by rfl

@[simp, grind =]
lemma eval_eq0 :
  [varStore, σ, numAlloc | #[.eq0 e!]]ₑ =
  unconstrained[numAlloc][varStore].step (.eq0 e!) σ
:= by simp [eval, EvalSt.addConstraint_unconstrained]

@[simp, grind =]
lemma eval_share :
  [varStore, σ, numAlloc | #[.share e!]]ₑ =
  unconstrained[numAlloc][varStore].step (.share e!) σ
:= by
  simp [eval]

@[simp, grind =]
lemma eval_isZero :
  [varStore, σ, numAlloc | #[.isZero e!]]ₑ =
  unconstrained[numAlloc][varStore].step (.isZero e!) σ
:= by
  simp [eval]
  rfl

@[simp, grind =]
lemma eval_num2bits {width : ℕ} :
  [varStore, σ, numAlloc | #[.num2bits width e!]]ₑ =
  unconstrained[numAlloc][varStore].step (.num2bits width e!) σ
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
  grind [=seq]

lemma step_of_refsValid_prefix
  {σ σ' : HashConsSt p}
  {circuit : Gate p}
  {st : EvalSt p}
  (h_prefix : σ.exprs.isPrefixOf σ'.exprs)
  (h_refsValid : circuit.refsValid (σ.exprs.size))
:
  [st, σ'|circuit]ₛ =
  [st, σ|circuit]ₛ
:= by
  unfold EvalSt.step
  cases circuit
  all_goals {
    simp
    expose_names
    have : e < σ.exprs.size := by
      unfold Gate.refsValid at h_refsValid
      grind
    have : st[Expr.mk e σ']? = st[Expr.mk e σ]? := by
      unfold_projs
      simp [EvalSt.get?, Expr.eval]
      congr 1
      symm
      exact HashConsM.evalCache_of_lt_prefix h_prefix this
    grind
  }

@[grind .]
lemma eval_of_refsValid_prefix
  {σ σ' : HashConsSt p}
  {circuit : Circuit p}
  {Γ : VarStore p}
  (h_prefix : σ.exprs.isPrefixOf σ'.exprs)
  (h_refsValid : circuit.refsValid σ.size)
:
  [Γ, σ', numAlloc|circuit]ₑ =
  [Γ, σ, numAlloc|circuit]ₑ
:= by
  simp [Circuit.eval, Circuit.evalInOrder]
  induction' h : circuit.size with len ih generalizing circuit
  · aesop
  · rcases circuit with ⟨circuit⟩
    rw [←circuit.reverse_reverse] at h ⊢
    rcases h₁ : circuit.reverse with _ | ⟨hd, tl⟩
    · aesop
    · rw [h₁] at h
      rw [←h]
      simp
      specialize @ih ⟨tl.reverse⟩ (by aesop (add simp Circuit.refsValid)) (by grind)
      have : (⟨tl.reverse⟩ : Array _).size = len := by grind
      simp [this] at ih
      rewrite [ih]
      exact Circuit.step_of_refsValid_prefix h_prefix (by aesop)

end

@[simp, grind _=_]
lemma refsValid_append_iff {a b : Circuit p} {numAlloc : ℕ}
:
  (a ++ b).refsValid numAlloc ↔
  a.refsValid numAlloc ∧ b.refsValid numAlloc
:= by
  grind

-- /-
-- TODO: In terms of `Circuit.wellFormed`
-- -/
-- lemma varsAllocated_append
--   (a b : Circuit p)
--   {varStore : VarStore p}
--   {σ : HashConsSt p}
--   {numAlloc : ℕ}
--   (h₀ : a.refsValid σ.size)
--   (h₁ : b.refsValid σ.size)
--   (h_a : a.varsAllocated varStore σ numAlloc)
--   (h_b : b.varsAllocated varStore σ numAlloc)
-- :
--   (a ++ b).varsAllocated varStore σ numAlloc
-- := by
--   simp [varsAllocated] at ⊢ h_a h_b
--   . intro i h_i
--     simp [Array.getElem_append]
--     split_ifs with h_i'
--     . specialize h_a i h_i'
--       exact varsAllocated_eval_append_right h₀ h_a
--     . specialize h_b (i - a.size) (by omega)
--       simp (disch := omega) [Array.extract_eq_self_of_le]
--       exact varsAllocated_eval_append_left h_b

@[grind →]
lemma varsAllocated_of_append_singleton
        {circuit : Circuit p}
        (h : varsAllocated (circuit ++ #[gate]) varStore σ numAlloc) :
        varsAllocated circuit varStore σ numAlloc := by
  unfold varsAllocated at h ⊢
  intros i hi
  specialize h i (by grind)
  grind

@[grind →]
lemma wellFormed_of_append_singleton_left
        {circuit : Circuit p}
        (h : wellFormed (circuit ++ #[gate]) varStore σ numAlloc) :
        wellFormed circuit varStore σ numAlloc := by
  simp only [wellFormed_iff] at h ⊢
  grind

@[grind →]
lemma wellFormed_of_append_singleton_right
        {circuit : Circuit p}
        (h : wellFormed (circuit ++ #[gate]) varStore σ numAlloc) :
        gate.wellFormed [varStore, σ, numAlloc|circuit]ₑ.varStore σ := by
  simp only [wellFormed_iff] at h ⊢
  simp [refsValid, varsAllocated] at h ⊢
  rcases h with ⟨h₁, h₂⟩
  split_ands
  · aesop
  · specialize h₂ circuit.size (le_refl _)
    simpa using h₂.1

@[grind .]
lemma _root_.Clap.Gate.refsValid_iff_wellFormed_mk :
  (Expr.mk gate.expr σ).wellFormed ↔ gate.refsValid σ.exprs.size := by
  grind

@[grind →]
lemma _root_.Clap.Expr.wellFormed_of_append_singleton
        {circuit : Circuit p}
        (h : wellFormed (circuit ++ #[gate]) varStore σ numAlloc) :
        (Expr.mk gate.expr σ).wellFormed := by
  grind

/-
Why is this direction not grind in the first place?
-/
attribute [grind =_] List.append_toArray

@[grind .]
lemma _root_.Std.ExtTreeMap.mem_insertMany_of_mem
  {α β}
  {cmp}
  [BEq α] [Std.TransCmp cmp] [Std.LawfulBEqCmp cmp]
  {k : α}
  {manyLen : ℕ}
  {many : Vector (α × β) manyLen}
  {map : Std.ExtTreeMap α β cmp}
  (h_mem : k ∈ map)
:
  k ∈ map.insertMany many
:= by
  obtain ⟨⟨manyList⟩, h_manyList⟩ := many
  have := (@Std.ExtTreeMap.mem_insertMany_list _ _ _ map _ _ _ manyList k).mpr
  simp [Std.ExtTreeMap.insertMany, Std.ExtDTreeMap.Const.insertMany] at ⊢ this
  apply this
  left
  assumption

@[simp, grind =]
lemma _root_.Std.ExtTreeMap.mem_insertMany_vector.{u, v}
  {α : Type u}
  {β : Type v}
  {cmp : α → α → Ordering}
  {t : Std.ExtTreeMap α β cmp}
  [Std.TransCmp cmp] [BEq α] [Std.LawfulBEqCmp cmp]
  {len : ℕ}
  {v : Vector (α × β) len}
  {k : α}
:
  k ∈ t.insertMany v ↔ k ∈ t ∨ (v.map Prod.fst).contains k = true
:= by
  obtain ⟨⟨manyList⟩, h_manyList⟩ := v
  have := (@Std.ExtTreeMap.mem_insertMany_list _ _ _ t _ _ _ manyList k).mpr
  simp [Std.ExtTreeMap.insertMany, Std.ExtDTreeMap.Const.insertMany] at ⊢ this
  subst h_manyList
  apply Iff.intro
  · intro a
    simp_all only [implies_true]
    convert Std.ExtTreeMap.mem_insertMany_list.mp _ using 1
    . aesop
    . assumption
    . simpa [Std.ExtTreeMap.insertMany, Std.ExtDTreeMap.Const.insertMany]
  · intro a
    simp_all only [forall_const]

@[grind =>]
lemma mem_eval_varStore_of_mem
  {k : ℕ}
  {circuit : Circuit p}
  (h_mem : k ∈ varStore)
:
  k ∈ [varStore, σ, numAlloc|circuit]ₑ.varStore
:= by
  obtain ⟨list⟩ := circuit
  rewrite [←list.reverse_reverse]
  induction' list.reverse with head tail h_tail
  . grind
  . grind

@[simp, grind _=_]
lemma eval_list_append
  {body : List (Gate p)}
  {tail : Gate p}
:
  [varStore, σ, numAlloc|⟨body ++ [tail]⟩]ₑ =
  [varStore, σ, numAlloc|⟨body⟩ ; (#[tail])]ₑ
:= by
  grind

@[grind =]
lemma varsAllocated_eval_share_cons
  {val : ZMod p}
  {circuit : Circuit p}
  {e : Expr p}
  (h_e : e.wellFormed)
  (h: [[varStore, e.σ, numAlloc|circuit]ₑ.varStore|e].isSome = true)
:
  [[varStore.insert numAlloc val, e.σ, numAlloc+1|circuit]ₑ.varStore|e].isSome
:= by
  simp [Expr.eval_eq_evalRec h_e] at ⊢ h
  grind

lemma varsAllocated_eval_cons
  {head : Gate p}
  {tail : List (Gate p)}
  (h_refsValid : gate.refsValid σ.size)
  (h : gate.varsAllocated [varStore, σ, numAlloc|⟨tail⟩]ₑ.varStore σ)
:
  gate.varsAllocated [varStore, σ, numAlloc|⟨head :: tail⟩]ₑ.varStore σ
:= by
  simp [Gate.varsAllocated] at ⊢ h
  have : (Expr.mk gate.expr σ).wellFormed := by grind
  simp [Expr.eval_eq_evalRec this] at ⊢ h
  simp [h]
  intro v h_varset
  obtain ⟨h1, h2⟩ := h
  specialize h2 v h_varset
  simp [VarStore.mem_iff_mem_keys, -Std.ExtTreeMap.mem_keys, ←List.mem_toFinset]
  simp
  grind

lemma varsAllocated_eval_append_left
  {circuit1 circuit2 : Circuit p}
  (h_refsValid : gate.refsValid σ.size)
  (h : gate.varsAllocated [varStore, σ, numAlloc|circuit2]ₑ.varStore σ)
:
  gate.varsAllocated [varStore, σ, numAlloc|circuit1 ++ circuit2]ₑ.varStore σ
:= by
  grind

end Circuit

end CircuitEval

end Clap

end Clap
