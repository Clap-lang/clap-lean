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

abbrev Circuit := Array Gate

section Clap

variable {p : ℕ}

namespace Circuit

@[grind =]
def refsValid (c : Circuit) (bound : ℕ) : Prop :=
  ∀ gate ∈ c, gate.refsValid bound

@[grind =]
def numAllocStep (c : Circuit) : ℕ :=
  (c.map Gate.numAllocStep).sum

@[simp, grind =]
lemma numAllocStep_nil : numAllocStep #[] = 0 := by
  simp [numAllocStep]

@[simp, grind =]
lemma numAllocStep_singleton {gate : Gate}
:
  numAllocStep #[gate] =
  gate.numAllocStep
:= by grind

@[simp, grind =]
lemma numAllocStep_singleton_list {gate : Gate}
:
  numAllocStep ⟨[gate]⟩ =
  gate.numAllocStep
:= by grind

@[simp, grind =]
lemma numAllocStep_append {c1 c2: Circuit}
:
  numAllocStep (c1 ++ c2) =
  numAllocStep c1 + numAllocStep c2
:= by grind

@[simp, grind =]
lemma numAllocStep_append_list {l1 l2 : List (Gate)}
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

variable {circuit : Circuit}
         {varStore Γ : VarStore p}
         {σ : HashConsSt p}
         {numAlloc : ℕ}
         {e! : ExprRef}
         {e : Expr p}
         {st : EvalSt p}

abbrev evalInOrder (circuit : Circuit)
                   (σ : HashConsSt p)
                   (st : EvalSt p) :=
  circuit.foldl (EvalSt.step (σ := σ)) st

def eval (circuit : Circuit) (varStore : VarStore p) (numAlloc : ℕ) (σ : HashConsSt p) : EvalSt p :=
  circuit.evalInOrder σ ⟨numAlloc, varStore, True⟩

notation "[" varStore ", " σ ", " numAlloc "|" circuit "]ₑ" => Circuit.eval circuit varStore numAlloc σ

-- TODO grind
@[simp]
lemma evalInOrder_numAlloc
:
  (evalInOrder circuit σ st).numAlloc =
  st.numAlloc + circuit.numAllocStep
:= by
  obtain ⟨circuit⟩ := circuit
  rewrite [←circuit.reverse_reverse]
  induction' circuit.reverse with body tail h_body
  . grind [=eval]
  . grind [=eval]

@[simp, grind =]
lemma eval_numAlloc
  {circuit : Circuit}
:
  [varStore, σ, numAlloc|circuit]ₑ.numAlloc =
  numAlloc + circuit.numAllocStep
:= evalInOrder_numAlloc

@[simp, grind =]
lemma eval_varStore_keys
  {circuit : Circuit}
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
  {circuit : Circuit}
  {k}
:
  k ∈ [varStore, σ, numAlloc|circuit]ₑ.varStore ↔
  (k ∈ varStore ∨ (numAlloc ≤ k ∧ k < numAlloc + circuit.numAllocStep))
:= by
  simp [VarStore.mem_iff_mem_keys, -Std.ExtTreeMap.mem_keys, ←List.mem_toFinset]
  aesop

@[grind =]
def varsAllocated (c : Circuit) (varStore : VarStore p) (σ : HashConsSt p) (numAlloc : ℕ) : Prop :=
  ∀ i (h : i < c.size),
    letI evalSt := [varStore, σ, numAlloc|c.take i]ₑ
    c[i].varsAllocated evalSt.varStore σ ∧
    ∀ e ∈ c[i].exprs, ∀ x ∈ Expr.varSet ⟨e, σ⟩, x < evalSt.numAlloc

@[aesop safe cases, grind]
structure wellFormed (circuit : Circuit) (Γ : VarStore p) (σ : HashConsSt p) (numAlloc : ℕ) : Prop where
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
  rw [eval_eq_evalRec h₁] at h ⊢
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
        rw [show Option.map = Functor.map from rfl, binaryOp_isSome_iff] at h ⊢
        grind
      · rw [show Option.map = Functor.map from rfl, binaryOp_isSome_iff] at h ⊢
        grind
      · rw [show Option.map = Functor.map from rfl, binaryOp_isSome_iff] at h ⊢
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
  {circuit : Circuit}
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
  {gate1 gate2 : Gate}
  (h_wf : gate2.wellFormed st.varStore σ)
:
  gate2.varsAllocated [st, σ|gate1]ₛ.varStore σ
:= by
  grind

@[grind .]
lemma _root_.Clap.Gate.wellFormed_step_of_wellFormed
  {gate1 gate2 : Gate}
  (h_wf : gate2.wellFormed st.varStore σ)
:
  gate2.wellFormed [st, σ|gate1]ₛ.varStore σ
:= by
  grind

variable {gate : Gate} {Γ₁ Γ₂ Γ₃ : VarStore p}

lemma varsAllocated_eval_append_right
  {i : ℕ}
  {a : Circuit}
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
    have (a: Array (Gate)) (l : List (Gate)) (gate : Gate)
      : a ++ (l ++ [gate]).toArray = (a ++ ⟨l⟩).push gate
    := by grind
    intros e he
    have : e < σ.size := by
      aesop (add safe (by grind))
    grind

@[grind .]
lemma varsAllocated_singleton_iff :
  varsAllocated #[gate] Γ σ numAlloc ↔
  (gate.varsAllocated Γ σ ∧ ∀ e ∈ gate.exprs, ∀ x ∈ (Expr.mk e σ).varSet, x < numAlloc) := by
  refine ⟨fun h ↦ ?p₁, fun h ↦ ?p₂⟩
  · unfold Circuit.varsAllocated at h
    specialize h 0 (by grind)
    simp at h
    grind
  · unfold varsAllocated
    grind

end Circuit

end Circuit

namespace EvalSt

variable {p pc numAlloc : ℕ} {σ : HashConsSt p} {constraints constraints1 constraints2 : Prop}
         {varStore : VarStore p} {circuit : Circuit} {e! : ExprRef} {gate : Gate}
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

lemma foldl_step_numAlloc_independent_of_constraints' {circuit : List (Gate)}
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

@[aesop safe, grind .]
lemma getElem?_eq_getElem?_of_varStore_eq {st₁ st₂ : EvalSt p} {e : Expr p} (h : st₁.varStore = st₂.varStore) :
  st₁[e]? = st₂[e]? := by
  grind [cases EvalSt]

lemma evalInOrder_varStore_independent_of_constraints
:
  (circuit.evalInOrder σ ⟨numAlloc, varStore, constraints1⟩).varStore =
  (circuit.evalInOrder σ ⟨numAlloc, varStore, constraints2⟩).varStore
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  induction circuit.reverse
  · grind
  next hd tail h_tail =>
    have := @foldr_step_numAlloc_independent_of_constraints' p numAlloc σ constraints1 constraints2 varStore ⟨tail⟩
    grind

@[grind .]
lemma numAlloc_evalInOrder_eq_numAlloc_eval
:
  (circuit.evalInOrder σ st).numAlloc =
  [st.varStore, σ, st.numAlloc|circuit]ₑ.numAlloc
:= by
  unfold Circuit.eval
  convert evalInOrder_numAlloc_independent_of_constraints

@[simp, grind .]
lemma varStore_evalInOrder_eq_varStore_eval
:
  (circuit.evalInOrder σ st).varStore =
  [st.varStore, σ, st.numAlloc|circuit]ₑ.varStore
:= by
  unfold Circuit.eval
  convert evalInOrder_varStore_independent_of_constraints

@[simp, grind =]
lemma eval_list_append_singleton
  {init : List Gate}
  {last : Gate}
:
  [varStore, σ, numAlloc|⟨init ++ [last]⟩]ₑ =
  [[varStore, σ, numAlloc|⟨init⟩]ₑ, σ|last]ₛ
:= by
  simp [Circuit.eval]

@[simp, grind .]
lemma constraints_evalInOrder_iff
:
  (circuit.evalInOrder σ st).constraints ↔
  st.constraints ∧ [st.varStore, σ, st.numAlloc|circuit]ₑ.constraints
:= by
  rcases circuit with ⟨circuit⟩
  rewrite [←List.reverse_reverse circuit]
  induction circuit.reverse <;> grind

lemma foldl_step_varStore_independent_of_constraints {circuit : List (Gate)}
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
  {circuit : Circuit}
  {σ₁ σ₂ : EvalSt p}
  (h₁ : σ₁.numAlloc = σ₂.numAlloc)
  (h₂ : σ₁.varStore = σ₂.varStore)
:
  (circuit.foldr (λ x y => [y, σ|x]ₛ) σ₁).varStore =
  (circuit.foldr (λ x y => [y, σ|x]ₛ) σ₂).varStore
:= by
  convert foldr_step_varStore_independent_of_constraints using 4 <;> grind

lemma foldr_step_varStore_independent_of_constraints'''
  {circuit : Circuit}
  {σ₁ σ₂ : EvalSt p}
  (h₁ : σ₁.numAlloc = σ₂.numAlloc)
  (h₂ : σ₁.varStore = σ₂.varStore) :
  (List.foldr (λ x y => [y, σ|x]ₛ) σ₁ circuit.toList).varStore =
  (List.foldr (λ x y => [y, σ|x]ₛ) σ₂ circuit.toList).varStore := by
  simp [Array.foldr_toList]
  apply foldr_step_varStore_independent_of_constraints'' <;> grind

@[simp, grind =]
lemma varStore_step_split_eq_varStore_step {gate : Gate} :
  [st.split, σ|gate]ₛ.varStore =
  [st, σ|gate]ₛ.varStore := by
  grind

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

end EvalSt


namespace Circuit

variable {numAlloc : ℕ} {circuit1 circuit2 : Circuit} {varStore : VarStore p}
         {σ : HashConsSt p}

def seq (circuit₁ circuit₂ : Circuit)
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
  [varStore, σ, numAlloc|circuit1; circuit2]ₑ.varStore =
  let mid := [varStore, σ, numAlloc|circuit1]ₑ
  [mid.varStore, σ, mid.numAlloc|circuit2]ₑ.varStore
:= rfl

@[simp, grind=]
lemma constraints_seq :
  [varStore, σ, numAlloc|circuit1; circuit2]ₑ.constraints =
  let mid := [varStore, σ, numAlloc|circuit1]ₑ
  mid.constraints ∧ [mid.varStore, σ, mid.numAlloc|circuit2]ₑ.constraints
:= rfl

@[simp, grind =]
lemma eval_append
:
  [varStore, σ, numAlloc | circuit1 ++ circuit2]ₑ = [varStore, σ, numAlloc|circuit1; circuit2]ₑ
:= by
  simp [eval]
  ext1
  all_goals dsimp [seq]
  . exact EvalSt.evalInOrder_numAlloc_independent_of_constraints
  . exact EvalSt.evalInOrder_varStore_independent_of_constraints
  . simp

variable {gate : Gate} {circuit : Circuit} {circuit_list : List Gate}

@[simp high, grind =]
lemma eval_singleton
:
  [varStore, σ, numAlloc | #[gate]]ₑ =
  [unconstrained[numAlloc][varStore], σ | gate]ₛ := by
  simp [eval, EvalSt.step_unconstrained]

@[simp, grind =]
lemma eval_cons
:
  [varStore, σ, numAlloc | ⟨gate :: circuit.toList⟩]ₑ =
  [varStore, σ, numAlloc|#[gate]; circuit]ₑ := by
  rw [show ⟨gate :: circuit.toList⟩ = #[gate] ++ circuit by simp]
  exact eval_append

@[simp, grind =]
lemma eval_cons'
:
  [varStore, σ, numAlloc | ⟨gate :: circuit_list⟩]ₑ =
  [varStore, σ, numAlloc|#[gate]; circuit_list.toArray]ₑ
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
:= rfl

@[simp, grind =]
lemma eval_share :
  [varStore, σ, numAlloc | #[.share e!]]ₑ =
  unconstrained[numAlloc][varStore].step (.share e!) σ
:= rfl

@[simp, grind =]
lemma eval_isZero :
  [varStore, σ, numAlloc | #[.isZero e!]]ₑ =
  unconstrained[numAlloc][varStore].step (.isZero e!) σ
:= rfl

@[simp, grind =]
lemma eval_num2bits {width : ℕ} :
  [varStore, σ, numAlloc | #[.num2bits width e!]]ₑ =
  unconstrained[numAlloc][varStore].step (.num2bits width e!) σ
:= rfl

@[simp, grind =]
lemma eval_fpmul {width k : ℕ} {a b p' : Vector ExprRef k} :
  [varStore, σ, numAlloc | #[.fpmul width k a b p']]ₑ =
  unconstrained[numAlloc][varStore].step (.fpmul width k a b p') σ
:= rfl


@[simp, grind =]
lemma seq_cons_nil {cmd : Gate} {circuit : Circuit} {varStore} {numAlloc} :
  [varStore, σ, numAlloc|(⟨cmd :: circuit.toList⟩); #[]]ₑ =
  [varStore, σ, numAlloc|#[cmd]; circuit]ₑ := by
  aesop (add simp seq)

@[simp high, grind =]
lemma seq_singleton_nil {cmd : Gate} {varStore} {numAlloc} :
  [varStore, σ, numAlloc|#[cmd]; #[]]ₑ =
  [varStore, σ, numAlloc|#[cmd]]ₑ := by
  grind [=seq]

variable {σ σ' : HashConsSt p} {gate : Gate} {st : EvalSt p} {circuit : Circuit} {Γ : VarStore p}

@[simp, grind =]
lemma assertAllocated_singleton :
  st.assertAllocated #v[e] =
  st.addConstraint (e ∈ st) := by
    simp [EvalSt.assertAllocated]

@[grind =>]
lemma step_of_refsValid_prefix
  (h_prefix : σ.exprs.isPrefixOf σ'.exprs)
  (h_refsValid : gate.refsValid σ.size)
:
  [st, σ'|gate]ₛ =
  [st, σ|gate]ₛ
:= by
  unfold EvalSt.step
  cases gate
  · grind
  · grind
  · grind
  · grind
  · simp [EvalSt.assertAllocated, EvalSt.stepFpmul]
    simp at h_refsValid
    congr 1
    . congr
      . simp
        constructor <;> intros h e he
        . obtain ⟨a, ⟨ha, he⟩⟩ | ⟨b, ⟨hb, he⟩⟩ | ⟨p', ⟨hp', he⟩⟩ := he
          . specialize h ⟨a, σ'⟩
            grind
          . specialize h ⟨b, σ'⟩
            grind
          . specialize h ⟨p', σ'⟩
            grind
        . obtain ⟨a, ⟨ha, he⟩⟩ | ⟨b, ⟨hb, he⟩⟩ | ⟨p', ⟨hp', he⟩⟩ := he
          . specialize h ⟨a, σ⟩
            grind
          . specialize h ⟨b, σ⟩
            grind
          . specialize h ⟨p', σ⟩
            grind
      . grind
      . grind
      . grind
      . grind
    . expose_names
      congr 1
      all_goals grind


@[grind .]
lemma eval_of_refsValid_prefix
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
lemma refsValid_append_iff {a b : Circuit} {numAlloc : ℕ}
:
  (a ++ b).refsValid numAlloc ↔
  a.refsValid numAlloc ∧ b.refsValid numAlloc
:= by
  grind

@[grind →]
lemma varsAllocated_of_append_singleton
        (h : varsAllocated (circuit ++ #[gate]) varStore σ numAlloc) :
        varsAllocated circuit varStore σ numAlloc := by
  unfold varsAllocated at h ⊢
  intros i hi
  specialize h i (by grind)
  grind

@[grind →]
lemma wellFormed_of_append_singleton_left
        (h : wellFormed (circuit ++ #[gate]) varStore σ numAlloc) :
        wellFormed circuit varStore σ numAlloc := by
  simp only [wellFormed_iff] at h ⊢
  grind

@[grind →]
lemma wellFormed_of_append_singleton_right
        (h : wellFormed (circuit ++ #[gate]) varStore σ numAlloc) :
        gate.wellFormed [varStore, σ, numAlloc|circuit]ₑ.varStore σ := by
  simp only [wellFormed_iff] at h ⊢
  simp [refsValid, varsAllocated] at h ⊢
  rcases h with ⟨h₁, h₂⟩
  split_ands
  · aesop
  · specialize h₂ circuit.size (le_refl _)
    simpa using h₂.1

@[grind →]
lemma wellFormed_of_append_singleton
  {e : ExprRef}
  (h : wellFormed (circuit ++ #[gate]) varStore σ numAlloc)
  (h_mem : e ∈ gate.exprs)
:
  (Expr.mk e σ).wellFormed
:= by
  grind

attribute [grind =_] List.append_toArray

variable {circuit : Circuit} {k : ℕ} {val : ZMod p} {e : Expr p}
         {body tail : List (Gate)} {head last : Gate}

@[grind =>]
lemma mem_eval_varStore_of_mem (h_mem : k ∈ varStore)
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

:
  [varStore, σ, numAlloc|⟨body ++ [last]⟩]ₑ =
  [varStore, σ, numAlloc|⟨body⟩ ; (#[last])]ₑ
:= by
  grind

@[grind =]
lemma varsAllocated_eval_share_cons
  (h_e : e.wellFormed)
  (h: [[varStore, e.σ, numAlloc|circuit]ₑ.varStore|e].isSome = true)
:
  [[varStore.insert numAlloc val, e.σ, numAlloc+1|circuit]ₑ.varStore|e].isSome
:= by
  simp [eval_eq_evalRec h_e] at ⊢ h
  grind

lemma varsAllocated_eval_cons
  (h_refsValid : gate.refsValid σ.size)
  (h : gate.varsAllocated [varStore, σ, numAlloc|⟨tail⟩]ₑ.varStore σ)
:
  gate.varsAllocated [varStore, σ, numAlloc|⟨head :: tail⟩]ₑ.varStore σ
:= by
  simp [Gate.varsAllocated] at ⊢ h
  intro e h_e
  have : (Expr.mk e σ).wellFormed := by grind
  specialize h e h_e
  simp [eval_eq_evalRec this]
  simp [eval_eq_evalRec this] at h
  simp [h]
  intro v h_varset
  obtain ⟨h1, h2⟩ := h
  specialize h2 v h_varset
  simp [VarStore.mem_iff_mem_keys, -Std.ExtTreeMap.mem_keys, ←List.mem_toFinset]
  simp
  grind

lemma varsAllocated_eval_append_left
  (h_refsValid : gate.refsValid σ.size)
  (h : gate.varsAllocated [varStore, σ, numAlloc|circuit2]ₑ.varStore σ)
:
  gate.varsAllocated [varStore, σ, numAlloc|circuit1 ++ circuit2]ₑ.varStore σ
:= by
  grind

@[grind <=]
lemma refsValid_take_of_refsValid {k bound : ℕ} {circuit : Circuit} (h : circuit.refsValid bound) :
  Circuit.refsValid (circuit.take k) bound := by
  unfold Circuit.refsValid at *
  intro gate a
  apply h gate
  rw [Array.mem_extract_iff_getElem] at a
  rcases a with ⟨w, w', hw⟩
  grind

@[grind .]
lemma refsValid_of_refsValid_of_le
  {low_bound high_bound : ℕ}
  (h_valid : circuit.refsValid low_bound)
  (h_le : low_bound ≤ high_bound)
:
  circuit.refsValid high_bound
:= by
  aesop (add simp [Circuit.refsValid, Gate.refsValid]) (add safe (by grind))

end Circuit

end CircuitEval

end Clap

end Clap
