import Clap.eDSLState.HashCons.HashConsM

namespace Clap.HashConsM

abbrev ValueCache (p : ℕ) := Array (Option (ZMod p))

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

def evalWithCache {p}
  (varStore : VarStore p) (e : ExprRef) (cache : ValueCache p) (σ : HashConsSt p) : ValueCache p :=
  if e < cache.size
  then cache
  else
    match σ[cache.size]? with
    | .none => cache
    | .some expr =>
      let val := evalCore varStore expr cache
      evalWithCache varStore e (cache.push val) σ
  termination_by e + 1 - cache.size
  decreasing_by grind

def evalRec {p} (Γ : VarStore p) (σ : HashConsSt p) (e : ExprRef) : Option (ZMod p) :=
  match h : σ.exprs[e]? with
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
      f <$> evalRec Γ σ lhs <*> evalRec Γ σ rhs
  termination_by e
  decreasing_by all_goals grind

def state : HashConsSt 37 where
  exprs := #[
    .c 3,
    .c 2,
    .binary_op 0 1 .add
  ]
  wellFormed := by decide

def eval {p} (varStore : VarStore p) (e : ExprRef) (σ : HashConsSt p) : Option (ZMod p) :=
  (evalWithCache varStore e #[] σ)[e]!

notation "[" varStore "," state "|" x "]" => eval varStore x state

section Lemmas

variable {p : ℕ} {varStore : VarStore p} {e : ExprRef} {σ} {cache : ValueCache p}
         {expr : CacheExpr p}

@[simp, grind =]
lemma evalWithCache_idempotent :
  evalWithCache varStore e (evalWithCache varStore e cache σ) σ =
  evalWithCache varStore e cache σ := by
  fun_induction evalWithCache <;> grind [=evalWithCache]

/--
The cache is immutable.
-/
@[aesop unsafe, grind .]
lemma evalWithCache_of_mem (h : e < cache.size) :
  (evalWithCache varStore e cache σ)[e]? = cache[e]? := by
  fun_induction evalWithCache <;> grind

/--
The cache never shrinks.
-/
@[mono, grind ←]
lemma size_le_size_evalWithCache :
  cache.size ≤ (evalWithCache varStore e cache σ).size := by
  fun_induction evalWithCache <;> grind

/--
Is this even useful?
NB: yes
-/
lemma lt_size_evalWithCache_of_lt_size (h : e < σ.size) :
  e < (evalWithCache varStore e cache σ).size := by
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
  {exprRef : ExprRef}
  (h_lookup : σ.exprs[exprRef]? = .some expr)
  (h_cache : ∀ ref < exprRef, cache[ref]! = evalRec varStore σ ref)
:
  evalCore varStore expr cache =
  evalRec varStore σ exprRef
:= by
  unfold evalCore
  unfold evalRec
  grind

lemma evalWithCache_wrt_evalRec
  (he : e < σ.size)
  (h : ∀ e, (h : e < cache.size) → cache[e]'h = evalRec varStore σ e)
:
  letI newCache := evalWithCache varStore e cache σ
  e < newCache.size ∧
  (newCache[e]'(lt_size_evalWithCache_of_lt_size he)) = evalRec varStore σ e
:= by
  fun_induction evalWithCache
  . split_ands
    . exact lt_of_lt_of_le (by assumption) size_le_size_evalWithCache
    . rewrite [←h e (by assumption)]
      expose_names
      have := evalWithCache_of_mem (σ := σ) (varStore := varStore) h_1
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

end Lemmas

abbrev evalM {p} (varStore : VarStore p) (e : HashConsM p ExprRef) : HashConsM p (Option (ZMod p)) := do
  let expr ← e
  let state ← get
  return [varStore,state|expr]

notation "[" varStore "," state "|" "←" x "]" => HashConsM.run (evalM varStore x) state

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

lemma evalCache_of_lt_prefix
  {p : ℕ}
  {varStore : VarStore p}
  {e : ExprRef}
  {cache : ValueCache p}
  {σ σ' : HashConsSt p}
  (h_prefix : σ.exprs.isPrefixOf σ'.exprs)
  (h_lt_prefix : e < σ.exprs.size)
:
  evalWithCache varStore e cache σ =
  evalWithCache varStore e cache σ'
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
    . have : cache.size < σ.exprs.size := by grind
      have : σ[cache.size]? = σ'[cache.size]? := by
        simp
        rewrite [←Array.getElem?_toList, ←Array.getElem?_toList]
        have : σ.exprs.toList.isPrefixOf σ'.exprs.toList = true := by grind
        have : σ.exprs.toList <+: σ'.exprs.toList := by grind
        have := List.prefix_iff_getElem?.mp this cache.size (by grind)
        grind
      rewrite [this]
      split
      . rfl
      . simp
        apply ih
        grind



end Prefix

end Clap.HashConsM
