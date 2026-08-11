import Mathlib.Tactic

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

@[grind cases]
structure Expr (p : ℕ) where
  ref : ExprRef
  σ : HashConsSt p

namespace Expr

section Expr

variable {p : ℕ} {e : Expr p}

@[grind =]
def deref (e : Expr p) : Option (CacheExpr p) := e.σ.exprs[e.ref]?

/--
Dereference is valid.
-/
@[grind =]
def wellFormed (e : Expr p) : Prop := e.ref < e.σ.size

instance : Decidable (wellFormed e) := inferInstanceAs <| Decidable (e.ref < e.σ.size)

prefix:max "*" => deref

@[grind _=_]
lemma wellFormed_iff_isSome : e.wellFormed ↔ (*e).isSome := by grind

@[grind →]
lemma wellFormed_frame {e' : Expr p}
  (h₁ : e.wellFormed) (h₂ : e.σ.exprs.isPrefixOf e'.σ.exprs) (h₃ : e.ref = e'.ref) : e'.wellFormed := by
  have : e.σ.exprs.toList.isPrefixOf e'.σ.exprs.toList = true := by grind
  grind [List.prefix_iff_getElem?]

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

def evalRec {p} (Γ : VarStore p) (e : Expr p) : Option (ZMod p) :=
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

section Eval

variable {Γ : VarStore p}

@[simp, grind .]
lemma binaryOp_isSome_iff {p} {f : ZMod p → ZMod p → ZMod p} {a b : Option (ZMod p)} :
  (f <$> a <*> b).isSome ↔ (a.isSome ∧ b.isSome) := by
  unfold_projs at *
  aesop (add simp Option.map)

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

@[grind .]
lemma isSome_evalRec_of_isSome_evalRec_subset {Γbig Γsmol : VarStore p}
  (h : (evalRec Γsmol e).isSome) (h₁ : Γsmol ⊆ Γbig) : (evalRec Γbig e).isSome := by
  rw [VarStore.hasSubset_def] at h₁
  fun_induction evalRec Γbig e <;> grind [=evalRec]

@[grind .]
lemma evalRec_c {c : ZMod p} (h : *e = .some (.c c)) :
  evalRec Γ e = some c := by
  grind [=evalRec]

@[grind .]
lemma evalRec_v {ptr : ℕ} (h : *e = .some (.v ptr)) :
  evalRec Γ e = Γ[ptr]? := by
  grind [=evalRec]

@[grind .]
lemma evalRec_add {lhs rhs} (h : *e = .some (.binary_op lhs rhs .add)) :
  evalRec Γ e =
  (·+·) <$> evalRec Γ { ref := lhs, σ := e.σ } <*> evalRec Γ { ref := rhs, σ := e.σ } := by
  unfold evalRec
  split
  · grind
  next e' h₁ =>
    have : e' = .binary_op lhs rhs .add := by grind
    rw! [this]
    simp
    congr 2
    cbv -- I DID IT!
    conv_lhs => unfold evalRec
    simp

@[grind .]
lemma evalRec_sub {lhs rhs} (h : *e = .some (.binary_op lhs rhs .sub)) :
  evalRec Γ e =
  (·-·) <$> evalRec Γ {ref := lhs, σ := e.σ} <*> evalRec Γ {ref := rhs, σ := e.σ} := by
  unfold evalRec
  split
  · grind
  next e' h₁ =>
    have : e' = .binary_op lhs rhs .sub := by grind
    rw! [this]
    simp
    congr 2
    cbv -- I DID IT!
    conv_lhs => unfold evalRec
    simp

@[grind .]
lemma evalRec_mul {lhs rhs} (h : *e = .some (.binary_op lhs rhs .mul)) :
  evalRec Γ e =
  (·*·) <$> evalRec Γ {ref := lhs, σ := e.σ} <*> evalRec Γ {ref := rhs, σ := e.σ} := by
  unfold evalRec
  split
  · grind
  next e' h₁ =>
    have : e' = .binary_op lhs rhs .mul := by grind
    rw! [this]
    simp
    congr 2
    cbv -- I DID IT!
    conv_lhs => unfold evalRec
    simp

lemma missing_hyp {k} {v} (h : e.wellFormed) (h₁ : (evalRec (Γ.insert k v) e).isSome) :
  (evalRec Γ e).isSome := sorry


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

@[grind _=_]
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

end Expr

end Expr

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
lemma evalCache_of_lt_prefix
  {p : ℕ}
  {Γ : VarStore p}
  {e : ExprRef}
  {cache : ValueCache p}
  {σ σ' : HashConsSt p}
  (h_prefix : σ.exprs.isPrefixOf σ'.exprs)
  (h_lt_prefix : e < σ.exprs.size)
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
    . have : cache.size < σ.exprs.size := by grind
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
    . have : cache.size < e₁.σ.exprs.size := by grind
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
  grind

@[aesop simp, grind .]
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
:= by grind

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
    have : xs.drop len = [xs.getLast (by grind)] := by aesop (add safe (by grind))
    simp [this]; clear this
    exact precedes_insert

@[grind .]
lemma isSome_eval_of_isSome_eval_precedes
  {e : Expr p}
  (h : [Γ₁|e].isSome = true)
  (h_wf : e.wellFormed)
  (h_precedes : [e.σ|Γ₁ ⊑ Γ₂])
:
  [Γ₂|e].isSome = true
:= by
  rewrite [Expr.eval_eq_evalRec h_wf]
  fun_induction Expr.evalRec
  . grind
  . grind
  . expose_names
    unfold precedes at h_precedes
    specialize h_precedes x.ref (by grind) (by grind)
    simp [Expr.eval_eq_evalRec h_wf] at h_precedes
    unfold Expr.evalRec at h_precedes
    grind
  . expose_names
    unfold precedes at h_precedes
    specialize h_precedes x.ref (by grind) (by grind)
    simp [Expr.eval_eq_evalRec h_wf] at h_precedes
    unfold Expr.evalRec at h_precedes
    grind

end Precedes

end Clap.HashConsM
