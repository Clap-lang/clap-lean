import Mathlib.Tactic

import Clap.eDSLState.Expr

namespace Clap

variable {p : ℕ}

namespace Expr

def evalCore {p} (Γ : VarStore p) (expr : CacheExpr p) (cache : ValueCache p) : Option (ZMod p) :=
  match expr with
  | .c k => .some k
  | .v idx => Γ[idx]?
  | .binary_op lhs rhs op =>
    let op := match op with
              | .add => (· + ·)
              | .sub => (· - ·)
              | .mul => (· * ·)
    let lhs := cache[lhs]!
    let rhs := cache[rhs]!
    op <$> lhs <*> rhs

def evalWithCache (Γ : VarStore p) (cache : ValueCache p) (e : Expr p) : ValueCache p :=
  if e.ref < cache.size
  then cache
  else
    match e.σ[cache.size]? with
    | .none => cache
    | .some expr =>
      let val := evalCore Γ expr cache
      evalWithCache Γ (cache.push val) e
  termination_by e.ref + 1 - cache.size
  decreasing_by grind

def evalRec (Γ : VarStore p) (e : Expr p) : Option (ZMod p) :=
  match h : *e with
  | .none => .none
  | .some expr =>
    match expr with
    | .c k => some k
    | .v idx => Γ[idx]?
    | .binary_op lhs rhs op =>
      let f := match op with
        | .add => (· + ·)
        | .sub => (· - ·)
        | .mul => (· * ·)
      f <$> evalRec Γ ⟨lhs, e.σ⟩  <*> evalRec Γ ⟨rhs, e.σ⟩
  termination_by e.ref
  decreasing_by all_goals grind

def varSet (e : Expr p) : Set ℕ := match _h : *e with
  | .some (.c _) => {}
  | .some (.v idx) => {idx}
  | .some (.binary_op lhs rhs _op) =>
    varSet ⟨lhs, e.σ⟩ ∪ varSet ⟨rhs, e.σ⟩
  | .none => {}
termination_by e.ref
decreasing_by all_goals grind

/--
Depends only on variables allocated at < numAlloc.
-/
def varSet_wellFormed (e : Expr p) (numAlloc : ℕ) : Prop :=
  ∀ x ∈ e.varSet, x < numAlloc

end Expr

namespace varSet

section

open Expr

@[grind ->]
lemma lt_of_varSet_wellFormed_mem {e! : ExprRef} {e : Expr p} {numAlloc : ℕ}
  (h₁ : e! ∈ e.varSet)
  (h₂ : varSet_wellFormed e numAlloc) :
  e! < numAlloc := by
  unfold varSet_wellFormed at h₂
  grind

@[grind ->]
lemma deref_eq_of_ref_eq_prefix {e₁ e₂ : Expr p}
  (h₀ : e₁.ref = e₂.ref)
  (h₁ : e₁.wellFormed)
  (h₂ : e₁.σ.exprs.isPrefixOf e₂.σ.exprs = true) :
  *e₁ = *e₂ := by
  unfold deref
  rcases eq₁ : e₁.σ.exprs with ⟨l₁⟩
  rcases eq₂ : e₂.σ.exprs with ⟨l₂⟩
  rw [←h₀]
  simp [eq₁, eq₂] at h₂
  simp
  rw [List.prefix_iff_getElem?] at h₂
  specialize h₂ e₁.ref (by grind)
  grind

@[grind ->]
lemma varSet_eq_of_prefix {e₁ e₂ : Expr p}
  (h₀ : e₁.ref = e₂.ref)
  (h₁ : e₁.wellFormed)
  (h₂ : e₁.σ.exprs.isPrefixOf e₂.σ.exprs = true) : varSet e₂ = varSet e₁ := by
  fun_induction varSet e₁ generalizing e₂
  . grind [=varSet]
  . grind [=varSet]
  . rewrite [varSet.eq_def]
    grind
  . grind [=varSet]

@[grind ->]
lemma varSet_mk_eq_of_prefix
  {e : ExprRef}
  {σ1 σ2 : HashConsSt p}
  (h_e_wf : (Expr.mk e σ1).wellFormed)
  (h_prefix : σ1.exprs.isPrefixOf σ2.exprs = true)
:
  varSet ⟨e, σ2⟩ = varSet ⟨e, σ1⟩
:= by
  apply varSet_eq_of_prefix <;> grind

@[grind =]
lemma varSet_mkConstant
  {c}
  {σ : HashConsSt p}
:
  (Expr.mk
    ((HashConsM.mkConstant c).getResult σ)
    ((HashConsM.mkConstant c).getHashConsState σ)
  ).varSet = {}
:= by
  grind [=varSet]

@[grind =]
lemma varSet_mkAdd
  {l r}
  {σ : HashConsSt p}
  (h_l : (Expr.mk l σ).wellFormed)
  (h_r : (Expr.mk r σ).wellFormed)
:
  (Expr.mk
    ((HashConsM.mkAdd l r).getResult σ)
    ((HashConsM.mkAdd l r).getHashConsState σ)
  ).varSet =
  (Expr.mk l σ).varSet ∪ (Expr.mk r σ).varSet
:= by
  rewrite [HashConsM.getResult_mkAdd_of_wellFormed (by grind) (by grind)]
  rewrite [HashConsM.getHashConsState_mkAdd_of_wellFormed (by grind) (by grind)]
  split_ifs
  . grind [=varSet]
  . unfold varSet
    rewrite [deref_mk_size_push]
    simp
    -- TODO: remove varSet_mk_eq_of_prefix
    grind [=varSet, varSet_mk_eq_of_prefix (e := r) (σ1 := σ)]

@[grind =]
lemma varSet_mkSub
  {l r}
  {σ : HashConsSt p}
  (h_l : (Expr.mk l σ).wellFormed)
  (h_r : (Expr.mk r σ).wellFormed)
:
  (Expr.mk
    ((HashConsM.mkSub l r).getResult σ)
    ((HashConsM.mkSub l r).getHashConsState σ)
  ).varSet =
  (Expr.mk l σ).varSet ∪ (Expr.mk r σ).varSet
:= by
  rewrite [HashConsM.getResult_mkSub_of_wellFormed (by grind) (by grind)]
  rewrite [HashConsM.getHashConsState_mkSub_of_wellFormed (by grind) (by grind)]
  split_ifs
  . grind [=varSet]
  . unfold varSet
    rewrite [deref_mk_size_push]
    simp
    -- TODO: remove varSet_mk_eq_of_prefix
    grind [=varSet, varSet_mk_eq_of_prefix (e := r) (σ1 := σ)]

@[grind =]
lemma varSet_mkMul
  {l r}
  {σ : HashConsSt p}
  (h_l : (Expr.mk l σ).wellFormed)
  (h_r : (Expr.mk r σ).wellFormed)
:
  (Expr.mk
    ((HashConsM.mkMul l r).getResult σ)
    ((HashConsM.mkMul l r).getHashConsState σ)
  ).varSet =
  (Expr.mk l σ).varSet ∪ (Expr.mk r σ).varSet
:= by
  rewrite [HashConsM.getResult_mkMul_of_wellFormed (by grind) (by grind)]
  rewrite [HashConsM.getHashConsState_mkMul_of_wellFormed (by grind) (by grind)]
  split_ifs
  . grind [=varSet]
  . unfold varSet
    rewrite [deref_mk_size_push]
    simp
    -- TODO: remove varSet_mk_eq_of_prefix
    grind [=varSet, varSet_mk_eq_of_prefix (e := r) (σ1 := σ)]

section MemVarset

variable {var : ℕ} {e : Expr p} {x x₁ x₂ : ExprRef} {op : BinaryOp}

@[grind =>]
lemma mem_varSet_of_deref_c (h : *e = .some (.c x)) : var ∈ varSet e ↔ False := by
  grind [varSet]

@[grind =>]
lemma mem_varSet_of_deref_v (h : *e = .some (.v x)) : var ∈ varSet e ↔ var = x := by
  grind [varSet]

@[grind =>]
lemma mem_varSet_of_deref_binOp (h : *e = .some (.binary_op x₁ x₂ op)) :
  var ∈ varSet e ↔ var ∈ (Expr.mk x₁ e.σ).varSet ∨ var ∈ (Expr.mk x₂ e.σ).varSet := by
  grind [=varSet]

end MemVarset

end

end varSet

section Eval

variable {Γ : VarStore p} {e : Expr p}

open Expr

@[grind =>]
lemma evalRec_eq_none_of_not_wellFormed (h : ¬e.wellFormed) : evalRec Γ e = .none := by
  unfold evalRec
  grind

@[grind =>]
lemma evalRec_eq_none_of_ {idx}
  (h₁ : *e = .some (.v idx)) (h₂ : idx ∉ Γ) : evalRec Γ e = .none := by
  unfold evalRec
  grind

@[simp, grind .]
lemma binaryOp_isSome_iff {p} {f : ZMod p → ZMod p → ZMod p} {a b : Option (ZMod p)} :
  (f <$> a <*> b).isSome ↔ (a.isSome ∧ b.isSome) := by
  unfold_projs at *
  aesop (add simp Option.map)

@[simp]
lemma binaryOp_eq_none_iff {p} {f : ZMod p → ZMod p → ZMod p} {a b : Option (ZMod p)} :
  (f <$> a <*> b = .none) ↔ (a = .none ∨ b = .none) := by
  unfold_projs at *
  aesop (add simp Option.map)

@[grind ->]
lemma wellFormed_of_deref_eq_binop {lhs rhs op} (h : *e = some (CacheExpr.binary_op lhs rhs op)) :
  (Expr.mk lhs e.σ).wellFormed ∧ (Expr.mk rhs e.σ).wellFormed := by
  grind

@[grind ->]
lemma evalRec_eq_none_of_binOp_evalRec_eq_none {lhs rhs op}
  (h₁ : evalRec Γ ⟨lhs, e.σ⟩ = .none ∨ evalRec Γ ⟨rhs, e.σ⟩ = .none)
  (h₂ : *e = .some (CacheExpr.binary_op lhs rhs op)) :
  evalRec Γ e = .none := by
  rcases e with ⟨ref, σ⟩
  simp at *
  unfold evalRec
  split
  · grind
  next e' he' =>
  split
  · grind
  · grind
  · dsimp
    rw [show Option.map = Functor.map from rfl, binaryOp_eq_none_iff]
    grind

open HashConsM in
@[grind ->]
lemma wellFormed_of_wellFormed_isPrefixOf
  {p : ℕ}
  {e₁ e₂ : Expr p}
  (h : e₁.ref = e₂.ref)
  (h_prefix : e₁.σ.exprs.isPrefixOf e₂.σ.exprs = true)
  (this : e₁.wellFormed) : e₂.wellFormed := by
  grind

open HashConsM in
@[grind ->]
lemma wellFormed_mk_of_wellFormed_isPrefixOf
  {p : ℕ}
  {e : ExprRef}
  {σ₁ σ₂ : HashConsSt p}
  (h_prefix : σ₁.exprs.isPrefixOf σ₂.exprs = true)
  (this : (⟨e, σ₁⟩ : Expr _).wellFormed) : (⟨e, σ₂⟩ : Expr _).wellFormed := by
  apply wellFormed_of_wellFormed_isPrefixOf (e₁ := ⟨e, σ₁⟩) <;> grind

@[grind .]
lemma isSome_evalRec_insert_of_isSome_evalRec {k : ℕ} {v : ZMod p}
  (h : (evalRec Γ e).isSome) : (evalRec (Γ.insert k v) e).isSome := by
  fun_induction evalRec Γ e
  · grind
  · expose_names
    unfold evalRec
    grind
  · unfold evalRec
    split
    · grind
    · grind
  · expose_names
    unfold evalRec
    simp
    subst f
    split
    · grind
    · expose_names
      have : expr = CacheExpr.binary_op lhs rhs op := by grind
      subst this
      simp at h ⊢
      split at h
      · rw [show Option.map = Functor.map from rfl, binaryOp_isSome_iff] at h ⊢
        grind
      · rw [show Option.map = Functor.map from rfl, binaryOp_isSome_iff] at h ⊢
        grind
      · rw [show Option.map = Functor.map from rfl, binaryOp_isSome_iff] at h ⊢
        grind

@[grind =>]
lemma evalRec_eq_none_of_deref_eq_none
  (h: *e = .none)
:
  evalRec Γ e = .none
:= by
  unfold evalRec
  grind only

@[grind .]
lemma evalRec_eq_of_deref_eq_some_v
  {idx}
  (h: *e = .some (CacheExpr.v idx))
:
  evalRec Γ e = Γ[idx]?
:= by
  unfold evalRec
  grind only

@[grind .]
lemma evalRec_eq_of_deref_eq_some_add
  {lhs rhs}
  (h: *e = .some (CacheExpr.binary_op lhs rhs .add))
:
  evalRec Γ e =
  (· + ·) <$> evalRec Γ ⦃lhs, e.σ⦄ <*> evalRec Γ ⦃rhs, e.σ⦄
:= by
  conv_lhs => unfold evalRec
  grind only

@[grind .]
lemma evalRec_eq_of_deref_eq_some_sub
  {lhs rhs}
  (h: *e = .some (CacheExpr.binary_op lhs rhs .sub))
:
  evalRec Γ e =
  (· - ·) <$> evalRec Γ ⦃lhs, e.σ⦄ <*> evalRec Γ ⦃rhs, e.σ⦄
:= by
  conv_lhs => unfold evalRec
  grind only

@[grind .]
lemma evalRec_eq_of_deref_eq_some_mul
  {lhs rhs}
  (h: *e = .some (CacheExpr.binary_op lhs rhs .mul))
:
  evalRec Γ e =
  (· * ·) <$> evalRec Γ ⦃lhs, e.σ⦄ <*> evalRec Γ ⦃rhs, e.σ⦄
:= by
  conv_lhs => unfold evalRec
  grind only

@[grind .]
lemma isSome_evalRec_lhs_of_isSome_evalRec_binop
  {op lhs rhs}
  (h_deref: *e = .some (CacheExpr.binary_op lhs rhs op))
  (h : (evalRec Γ e).isSome = true)
:
  (evalRec Γ ⦃lhs, e.σ⦄).isSome = true
:= by
  unfold evalRec at h
  split at h
  . grind
  . split at h
    . grind
    . grind
    . rewrite [binaryOp_isSome_iff] at h
      grind only

@[grind .]
lemma isSome_evalRec_rhs_of_isSome_evalRec_binop
  {op lhs rhs}
  (h_deref: *e = .some (CacheExpr.binary_op lhs rhs op))
  (h : (evalRec Γ e).isSome = true)
:
  (evalRec Γ ⦃rhs, e.σ⦄).isSome = true
:= by
  unfold evalRec at h
  split at h
  . grind
  . split at h
    . grind
    . grind
    . rewrite [binaryOp_isSome_iff] at h
      grind only

@[grind .]
lemma isSome_evalRec_of_isSome_evalRec_subset {Γbig Γsmol : VarStore p}
  (h : (evalRec Γsmol e).isSome) (h₁ : Γsmol ⊆ Γbig) : (evalRec Γbig e).isSome := by
  rw [VarStore.hasSubset_def] at h₁
  fun_induction evalRec Γbig e
  . grind
  . grind
  . grind
  . grind

@[grind .]
lemma evalRec_c {c : ZMod p} (h : *e = .some (.c c)) :
  evalRec Γ e = some c := by
  unfold evalRec
  grind

@[grind .]
lemma evalRec_v {ptr : ℕ} (h : *e = .some (.v ptr)) :
  evalRec Γ e = Γ[ptr]? := by
  unfold evalRec
  grind

@[simp, grind =]
lemma evalRec_isSome_iff :
  (evalRec Γ e).isSome ↔
  (
    e.wellFormed ∧
    ∀ v ∈ (varSet e), v ∈ Γ
  )
:= by
  fun_induction varSet
  . unfold evalRec; grind
  . unfold evalRec; grind
  . unfold evalRec; grind
  . unfold evalRec; grind

section Grind

@[simp, grind ->]
lemma wellFormed_mem_varStore_of_evalRec_eq_some {x} :
  (evalRec Γ e = .some x) →
  (
    e.wellFormed ∧
    ∀ v ∈ varSet e, v ∈ Γ
  )
:= by
  intros eq
  apply Option.isSome_of_eq_some at eq
  grind

end Grind

def eval {p} (varStore : VarStore p) (e : Expr p) : Option (ZMod p) :=
  (evalWithCache varStore #[] e)[e.ref]!

notation "[" varStore "," σ "|" e "]" => eval varStore ⟨e, σ⟩

notation "[" varStore "|" e "]" => eval varStore e

section Lemmas

variable {p : ℕ} {Γ : VarStore p} {e : Expr p} {cache : ValueCache p}
         {expr : CacheExpr p}

@[simp, grind =]
lemma evalWithCache_idempotent :
  evalWithCache Γ (evalWithCache Γ cache e) e =
  evalWithCache Γ cache e := by
  fun_induction evalWithCache <;> grind [=evalWithCache]

/--
The cache is immutable.
-/
@[aesop unsafe, grind .]
lemma evalWithCache_of_mem (h : e.ref < cache.size) :
  (evalWithCache Γ cache e)[e.ref]? = cache[e.ref]? := by
  fun_induction evalWithCache <;> grind

/--
The cache never shrinks.
-/
@[mono, grind ←]
lemma size_le_size_evalWithCache :
  cache.size ≤ (evalWithCache Γ cache e).size := by
  fun_induction evalWithCache <;> grind

/--
Is this even useful?
NB: yes
-/
lemma lt_size_evalWithCache_of_lt_size (h : e.wellFormed) :
  e.ref < (evalWithCache Γ cache e).size := by
  fun_induction evalWithCache <;> grind

-- lemma evalCore_evalRec
--   (h₁ : ∀ e < cache.size, cache[e]? = evalRec varStore σ e)
--   (h₂ : σ.exprs[cache.size]? = some expr) :
--   evalCore varStore expr cache = evalRec varStore σ cache.size := by
--   unfold evalCore evalRec
--   rcases expr with e | e | ⟨lhs, rhs, binop⟩
--   · aesop
--   · aesop
--   · obtain ⟨h₃, h₄⟩ : lhs < cache.size ∧ rhs < cache.size := by
--       have := σ.wellFormed _ (show cache.size < σ.exprs.size by grind)
--       aesop
--     simp
--     sorry

lemma evalCore_evalRec
  {expr : CacheExpr p}
  (h_lookup : *e = .some expr)
  (h_cache : ∀ ref < e.ref, cache[ref]! = evalRec Γ ⟨ref, e.σ⟩)
:
  evalCore Γ expr cache =
  evalRec Γ e
:= by grind [=evalCore, =evalRec]

lemma evalWithCache_wrt_evalRec
  (he : e.wellFormed)
  (h : ∀ ref, (h : ref < cache.size) → cache[ref]'h = evalRec Γ ⟨ref, e.σ⟩)
:
  letI newCache := evalWithCache Γ cache e
  e.ref < newCache.size ∧
  (newCache[e.ref]'(lt_size_evalWithCache_of_lt_size he)) = evalRec Γ e
:= by
  fun_induction evalWithCache
  . split_ands
    . exact lt_of_lt_of_le (by assumption) size_le_size_evalWithCache
    . rewrite [←h e.ref (by assumption)]
      expose_names
      have := evalWithCache_of_mem (Γ := Γ) h_1
      grind
  . grind
  . expose_names
    split_ands
    . unfold evalWithCache
      grind
    . unfold evalWithCache
      simp [h_1, h_2]
      apply (ih1 _).2
      intro idx h_idx
      by_cases h_idx' : idx = x.size
      . simp [h_idx', val]
        unfold evalCore evalRec
        grind
      . grind

lemma eval_eq_evalRec
  (h : e.wellFormed)
:
  [Γ|e] = evalRec Γ e
:= by
  unfold eval
  have := @evalWithCache_wrt_evalRec p Γ e #[]
  grind

end Lemmas

end Eval

section EvalM

variable {p : ℕ}

abbrev toExpr (e : ExprRef) : HashConsM p (Expr p) := do
  return ⟨e, ←get⟩

abbrev deref (e : ExprRef) : HashConsM p (Option (CacheExpr p)) :=
  get <&> (*{ref := e, σ := ·})

abbrev evalM (Γ : VarStore p) (e : HashConsM p ExprRef) : HashConsM p (Option (ZMod p)) := do
  let expr ← e
  let state ← get
  return [Γ, state|expr]

notation "[" varStore "," state "|" "←" x "]" => HashConsM.run (evalM varStore x) state

end EvalM

section Prefix

lemma Array.size_eq_zero_of_isPrefixOf_size_eq_zero
  {T} [BEq T] [LawfulBEq T]
  (a b: Array T)
  (h_prefix : a.isPrefixOf b = true)
  (h_size : b.size = 0)
:
  a.size = 0
:= by
  rewrite [←Array.isPrefixOf_toList] at h_prefix
  grind

open Expr in
@[grind! .]
lemma evalCache_of_lt_prefix
  {p : ℕ}
  {Γ : VarStore p}
  {e : ExprRef}
  {cache : ValueCache p}
  {σ σ' : HashConsSt p}
  (h_prefix : σ.exprs.isPrefixOf σ'.exprs)
  (h_lt_prefix : (Expr.mk e σ).wellFormed)
:
  evalWithCache Γ cache ⟨e, σ⟩ =
  evalWithCache Γ cache ⟨e, σ'⟩
:= by
  unfold ExprRef at *
  induction h : e + 1 - cache.size generalizing cache with
  | zero =>
    unfold evalWithCache
    grind
  | succ n ih =>
    unfold evalWithCache
    split_ifs
    . rfl
    . have : cache.size < σ.size := by grind
      have : σ[cache.size]? = σ'[cache.size]? := by
        simp
        rewrite [←Array.getElem?_toList, ←Array.getElem?_toList]
        have : σ.exprs.toList.isPrefixOf σ'.exprs.toList = true := by grind
        grind [List.prefix_iff_getElem?]
      grind

open Expr in
@[grind =>]
lemma evalCache_of_lt_prefix'
  {p : ℕ}
  {Γ : VarStore p}
  {e₁ e₂ : Expr p}
  {cache : ValueCache p}
  (h_ref : e₁.ref = e₂.ref)
  (h_prefix : e₁.σ.exprs.isPrefixOf e₂.σ.exprs)
  (h_lt_prefix : e₁.wellFormed)
:
  evalWithCache Γ cache e₁ =
  evalWithCache Γ cache e₂
:= by
  unfold ExprRef at *
  induction h : e₁.ref + 1 - cache.size generalizing cache with
  | zero =>
    unfold evalWithCache
    grind
  | succ n ih =>
    unfold evalWithCache
    split_ifs
    . rfl
    . have : cache.size < e₁.σ.size := by grind
      have : e₁.σ[cache.size]? = e₂.σ[cache.size]? := by grind
      grind
    · grind
    · split
      · grind
      · have : e₁.σ.exprs.toList.isPrefixOf e₂.σ.exprs.toList = true := by grind
        rw [ih (by grind)]
        grind [List.prefix_iff_getElem?]

end Prefix

@[aesop simp, grind .]
lemma isSome_eval_of_isSome_eval_subset
  {p : ℕ}
  {varStoreBig varStoreSmol : VarStore p}
  {σ : HashConsSt p}
  {e : ExprRef}
  (h : [varStoreSmol, σ|e].isSome = true)
  (h₁ : e < σ.size)
  (h₂ : varStoreSmol ⊆ varStoreBig)
:
  [varStoreBig, σ|e].isSome = true
:= by
  grind [=eval_eq_evalRec]

@[aesop simp, grind →]
lemma isSome_eval_of_isSome_eval_subset'
  {p : ℕ}
  {varStoreBig varStoreSmol : VarStore p}
  {e : Expr p}
  (h : [varStoreSmol|e].isSome = true)
  (h₁ : e.wellFormed)
  (h₂ : varStoreSmol ⊆ varStoreBig)
:
  [varStoreBig|e].isSome = true
:= by
  grind

section Precedes

open Expr

variable {p : ℕ} {Γ Γ₁ Γ₂ Γ₃ : VarStore p} {σ : HashConsSt p}

@[grind =]
def precedes {p : ℕ} (Γ₁ Γ₂ : VarStore p) (σ : HashConsSt p) :=
  ∀ e < σ.size, [Γ₁, σ|e].isSome → [Γ₂, σ|e].isSome

notation "[" σ "|" Γ₁ " ⊑ " Γ₂ "]" => precedes Γ₁ Γ₂ σ

@[grind →]
lemma precedes_trans (h₁ : [σ|Γ₁ ⊑ Γ₂]) (h₂ : [σ|Γ₂ ⊑ Γ₃]) : [σ|Γ₁ ⊑ Γ₃] := by grind

@[grind .]
lemma precedes_rfl : [σ|Γ ⊑ Γ] := by grind

@[grind .]
lemma precedes_insert
  {k : ℕ}
  {v : ZMod p}
:
  [σ|Γ ⊑ Γ.insert k v]
:= by grind [=eval_eq_evalRec]

@[grind =>]
lemma insert_precedes_of_mem
  {k : ℕ}
  {v : ZMod p}
  (h: k ∈ Γ)
:
  [σ|Γ.insert k v ⊑ Γ]
:= by
  unfold precedes
  intro e h_e h_eval
  rewrite [eval_eq_evalRec (by grind)] at ⊢ h_eval
  set x := Expr.mk e σ
  induction eq: x using evalRec.induct_unfolding Γ generalizing e
  . grind
  . grind
  . grind
  . expose_names
    specialize ih2 lhs (by grind)
    specialize ih1 rhs (by grind)
    rewrite [binaryOp_isSome_iff]
    unfold evalRec at h_eval
    split at h_eval
    . grind
    . split at h_eval
      . grind
      . grind
      . rewrite [binaryOp_isSome_iff] at h_eval
        grind

open Expr in
@[grind =>]
lemma evalRec_of_wellFormed_of_prefix
  {p : ℕ}
  {Γ : VarStore p}
  {e : ExprRef}
  {σ σ' : HashConsSt p}
  (h_prefix : σ.exprs.isPrefixOf σ'.exprs)
  (h_lt_prefix : (Expr.mk e σ).wellFormed)
:
  evalRec Γ ⟨e, σ⟩ =
  evalRec Γ ⟨e, σ'⟩ := by
  rw [←Clap.eval_eq_evalRec (by grind), ←Clap.eval_eq_evalRec]
  grind [=eval]
  grind

@[grind .]
lemma precedes_insertMany
  {k}
  {xs : Vector (ℕ × ZMod p) k}
:
  [σ|Γ ⊑ Γ.insertMany xs]
:= by
  simp [Std.ExtTreeMap.insertMany, Std.ExtDTreeMap.Const.insertMany]
  obtain ⟨⟨xs⟩, h_len⟩ := xs
  simp
  induction' h_len: xs.length with len ih generalizing xs k
  . aesop (add safe (by grind))
  . have := @ih len (xs.take len) (by grind) (by grind)
    apply precedes_trans this
    rewrite [←List.take_append_drop len xs]
    simp [-List.take_append_drop]
    simp
    simp [List.drop_eq_singleton_getList_of_length h_len]
    exact precedes_insert

@[grind .]
lemma isSome_evalRec_of_isSome_evalRec_precedes
  {e : Expr p}
  (h : (evalRec Γ₁ e).isSome = true)
  (h_wf : e.wellFormed)
  (h_precedes : [e.σ|Γ₁ ⊑ Γ₂])
:
  (evalRec Γ₂ e).isSome = true
:= by
  fun_induction evalRec Γ₂ e
  <;> grind [=eval_eq_evalRec]

@[grind .]
lemma isSome_eval_of_isSome_eval_precedes
  {e : Expr p}
  (h : [Γ₁|e].isSome = true)
  (h_wf : e.wellFormed)
  (h_precedes : [e.σ|Γ₁ ⊑ Γ₂])
:
  [Γ₂|e].isSome = true
:= by
  rewrite [eval_eq_evalRec h_wf] at ⊢ h
  exact isSome_evalRec_of_isSome_evalRec_precedes h h_wf h_precedes

-- @[grind! .]
lemma isSome_eval_of_prefix {e₁ e₂ : Expr p}
        (hwf : e₁.wellFormed) (h : [Γ|e₁].isSome)
        (h₁ : e₁.ref = e₂.ref) (h₂ : e₁.σ.exprs.isPrefixOf e₂.σ.exprs) :
  [Γ|e₂].isSome := by
  grind [eval_eq_evalRec]

-- grind_pattern isSome_eval_of_prefix => [Γ|e₂].isSome, e₁.σ.exprs.isPrefixOf e₂.σ.exprs

-- TODO is this the right grindage?
@[grind! .]
lemma isSome_prefix_eval_of_isSome_of_lt
  {e₁ e₂ : Expr p}
  (h_lt : e₁.wellFormed)
  (h_ref : e₁.ref = e₂.ref)
  (h_prefix : e₁.σ.exprs.isPrefixOf e₂.σ.exprs)
  (h_eval : [Γ|e₂].isSome)
:
  [Γ|e₁].isSome
:= by
  grind [eval_eq_evalRec]

@[simp, grind =]
lemma eval_mkConstant {c : ZMod p}
:
  [Γ|⟨(HashConsM.mkConstant c).getResult σ, (HashConsM.mkConstant c).getHashConsState σ⟩] =
  .some c
:= by
  rewrite [eval_eq_evalRec]
  . unfold evalRec
    simp [HashConsM.mkConstant]
    grind
  . grind

end Precedes

lemma eval_eq_of_varStore_eq_at_varSet
  {e : Expr p}
  (h_wf : e.wellFormed)
  {Γ1 Γ2 : VarStore p}
  (h : ∀ v ∈ e.varSet, Γ1[v]? = Γ2[v]?)
:
  [Γ1|e] = [Γ2|e]
:= by
  simp [eval_eq_evalRec h_wf]
  fun_induction Expr.evalRec Γ1 e
  . aesop (add safe (by grind [=Expr.varSet]))
  . aesop (add safe (by grind [=Expr.varSet]))
  . aesop (add safe (by grind [=Expr.varSet]))
  . expose_names
    conv_rhs => unfold Expr.evalRec
    split
    . grind
    . split <;> grind

@[grind =>]
lemma eval_eq_some_of_wellFormed_of_isPrefixOf
  {result : ExprRef}
  {σ σ' : HashConsSt p}
  {varStore : VarStore p}
  (h₁ : ⦃result, σ⦄.wellFormed)
  (h₂ : σ.exprs.isPrefixOf σ'.exprs = true)
:
  [varStore, σ'|result] = [varStore, σ|result]
:= by
  grind [eval_eq_evalRec]

end Clap
