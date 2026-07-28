import Clap.eDSLState.HashCons.HashConsM

namespace Clap.HashConsM

abbrev ValueCache (p : ℕ) := Std.ExtHashMap ExprRef (Option (ZMod p))

-- Given a cache mapping exprRefs to their value in a given varstore,
-- add an entry for e
def evalAux {p}
  (Γ : VarStore p)
  (e : ExprRef)
  (cache : ValueCache p)
  (state : HashConsSt p)
:
  ValueCache p
:=
  -- if e already has a cached value, no modification needed
  match cache[e]? with
  | .some result => cache
  | .none =>
    -- if e is not a reference into the Hash Cons State, no modification needed
    match h : state[e]? with
    | .none => cache
    | .some expr =>
      match expr with
      -- for leaves, insert their value, looking at the varstore if needed
      | .c value => cache.insert e (.some value)
      | .v idx => cache.insert e (Γ.get? idx)
      -- for branch nodes, recurse, adding the childrens' values if needed
      | .binary_op lhs rhs op =>
        have lhs_precedes_your_index : lhs < e := by
          grind [HashConsSt.wellFormed, CacheExpr.wellFormed]
        letI lhs_cache := evalAux Γ lhs cache state
        letI lhs_val := lhs_cache[lhs]?.join
        have rhs_precedes_your_index : rhs < e := by
          grind [HashConsSt.wellFormed, CacheExpr.wellFormed]
        letI rhs_cache := evalAux Γ rhs lhs_cache state
        letI rhs_val := rhs_cache[rhs]?.join
        rhs_cache.insert e ((match op with
          | .add => (· + ·)
          | .sub => (· - ·)
          | .mul => (· * ·)
        ) <$> rhs_cache[lhs]?.join <*> rhs_cache[rhs]?.join)
termination_by e

-- TODO some form of wellFormedness to say that cached values came from evalAux?

variable {p : ℕ} {ref : ExprRef} {cache : ValueCache p} {σ : HashConsSt p} {varStore : VarStore p}

@[aesop unsafe, grind .]
lemma evalAux_of_mem_cache (h : ref ∈ cache) :
  evalAux varStore ref cache σ = cache := by grind [=evalAux]

def eval (varStore : VarStore p) (e : HashConsM p ExprRef) : HashConsM p (Option (ZMod p)) := do
  let expr ← e
  letI post_cache := evalAux varStore expr {} (←get)
  return (post_cache.get? expr).join

notation "[" varStore "|" x "]" => (eval varStore x)

notation "[" varStore "," state "|" x "]" => run [varStore|x] state

notation "[" varStore "," state "|" x " =Γ " y "]" => [varStore,state|x] = [varStore,state|y]

variable {p : ℕ} {e : CacheExpr p} {σ : HashConsSt p}

section

variable {varStore : VarStore p} {k : ZMod p} {cache : Std.ExtHashMap ExprRef (Option (ZMod p))}
         {ref : ExprRef}

@[aesop unsafe, grind .]
lemma evalAux_of_not_mem_cache_not_mem_state (h₁ : ref ∉ cache) (h₂ : ref ∉ σ) :
  evalAux varStore ref cache σ = cache := by
  grind [=evalAux]

@[aesop unsafe, grind =>]
lemma evalAux_of_not_mem_cache_mem_state_some_c (h₁ : ref ∉ cache) (h₂ : σ[ref]? = .some (.c k)) :
  evalAux varStore ref cache σ = cache.insert ref (.some k) := by
  grind [=evalAux]

@[simp, grind =]
lemma get_eq : (get (m := HashConsM p) σ) = (σ, σ) := rfl

/--
TODO Obviously we can't be writing these proofs like this.
-/
@[aesop unsafe, grind .]
lemma eval_eq_some_of_mem_eq_const (h : σ[ref]? = .some (.c k)) :
  eval varStore (pure ref) σ = (.some k, σ) := by
  unfold eval
  simp
  unfold Functor.map
  unfold_projs
  simp
  unfold StateT.map
  simp
  unfold Functor.map
  unfold_projs
  grind

def f (ref : ExprRef) : HashConsM p (Option (CacheExpr p)) := fun σ ↦ (σ[ref]?, σ)

end


section

variable {varStore : VarStore p} {k : ZMod p} {cache : Std.ExtHashMap ExprRef (Option (ZMod p))}
         {σ : HashConsSt p} {ref : ExprRef}

@[grind _=_]
lemma runGet?_def {ref : HashConsM p ExprRef} :
  ref.runGet? σ = (StateT.run ref σ).2[(StateT.run ref σ).1]? := rfl

@[simp, grind =]
lemma runGet?_pure {x : ExprRef}:
  HashConsM.runGet? (StateT.pure x) σ =
  σ[x]?
:= rfl

@[simp, grind =]
lemma runGet?_bind {α} {a : HashConsM p α} {f : α → HashConsM p ExprRef} :
  (a >>= f).runGet? σ =
  (f (a.run σ).1).runGet? (a.run σ).2
:= rfl

@[grind =]
lemma runGet_saveExpr_of_wellFormed {e : CacheExpr p} (h: e.wellFormed σ.exprs.size):
  (HashConsM.saveExpr e).runGet? σ = .some e
:= by
  unfold HashConsM.saveExpr
  aesop (add simp [pure, Id.run]) (add safe (by grind))

@[simp, grind =]
lemma runGet_mkConstant :
  (mkConstant k).runGet? σ = .some (.c k)
:= by
  unfold mkConstant
  grind

@[grind =]
lemma runGet_mkAdd {l r : ExprRef} (h: (CacheExpr.binary_op (p := p) l r BinaryOp.add).wellFormed σ.exprs.size) :
  (mkAdd l r).runGet? σ = .some (.binary_op l r BinaryOp.add)
:= by
  unfold mkAdd
  grind

@[grind =]
lemma runGet_mkSub {l r : ExprRef} (h: (CacheExpr.binary_op (p := p) l r BinaryOp.sub).wellFormed σ.exprs.size) :
  (mkSub l r).runGet? σ = .some (.binary_op l r BinaryOp.sub)
:= by
  unfold mkSub
  grind

@[grind =]
lemma runGet_mkMul {l r : ExprRef} (h: (CacheExpr.binary_op (p := p) l r BinaryOp.mul).wellFormed σ.exprs.size) :
  (mkMul l r).runGet? σ = .some (.binary_op l r BinaryOp.mul)
:= by
  unfold mkMul
  grind

attribute [local grind ext]
  Option.ext Prod.ext Id.ext

abbrev val {α} (a : HashConsM p α) (σ : HashConsSt p) := (a.run σ).1

abbrev st {α} (a : HashConsM p α) (σ : HashConsSt p) := (a.run σ).2

lemma eval_run_of_runGet?_eq_some_c {ref : HashConsM p ExprRef}
        (h : ref.runGet? σ = .some (.c k)) :
  [varStore,σ|ref] = (.some k, ref.st σ) := by
  simp [eval]
  grind [=Id.run, Functor.map]

def ValueCache.wellFormed {p} (Γ : VarStore p) (σ : HashConsSt p) (cache : ValueCache p) : Prop :=
  ∀ (e : ExprRef) (r : Option (ZMod p)),
    cache[e]? = .some r → (evalAux Γ e ∅ σ)[e]? = r

theorem ValueCahcke.wellFormed_evalAux_of_wellFormed {Γ : VarStore p} {e}
  (h : ValueCache.wellFormed Γ σ cache) : ValueCache.wellFormed Γ σ (evalAux Γ e cache σ) := by
  sorry    

-- TODO move evalAux into hypothesis?
-- TODO generalise to wellFormed cache
lemma eval_run_pure {k : ExprRef} {cache : ValueCache p} (h : cache.wellFormed varStore σ) :
  [varStore,σ|pure k] = ((evalAux varStore k cache σ)[k]?.join, σ)
:= by
  unfold eval
  suffices (evalAux varStore k ∅ σ)[k]?.join = (evalAux varStore k cache σ)[k]?.join by simpa
  
  

lemma eval_run_bind {α} {a : HashConsM p α} {f : α → HashConsM p ExprRef} :
  [varStore, σ|a >>= f] =
  [varStore, a.st σ|f (a.val σ)]
:= rfl

-- TODO, this is really just idxOf∧contains=>get?=.some, and get?=runGet?
lemma run_eval_idxOf_c_of_contains {ref : HashConsM p ExprRef} {e : CacheExpr p}
  (h₁ : e ∈ (ref.st σ).exprs)
  (h₂ : ref.val σ = (ref.st σ).exprs.idxOf e)
:
  ref.runGet? σ = .some e
:= by
  grind [HashConsM.runGet?]

@[grind .]
lemma run_eval_idxOf_c_of_contains' {ref : HashConsM p ExprRef} {e : CacheExpr p}
  (h : e ∈ (ref.st σ).exprs)
  (h': ref.val σ = (ref.st σ).exprs.idxOf e)
:
  ref.runGet? σ = .some e
:= run_eval_idxOf_c_of_contains h h'

@[aesop unsafe, grind .]
lemma HashConsSt.exprs_mem_pushExpr {e : CacheExpr p} (h : e.wellFormed σ.exprs.size) :
  e ∈ (σ.pushExpr e h).exprs := by
  simp [HashConsSt.pushExpr]

lemma eval_pushExpr {ref : HashConsM p ExprRef}
  (h : ref.val (σ.pushExpr (.c k) wellFormed_c) = σ.exprs.size)
:
  [varStore, σ.pushExpr (.c k) wellFormed_c|ref] = (.some k, ref.st σ)
:= by
  sorry
  
-- @[simp, grind =]
-- lemma run_mkConstant_eval_c_of_mem
--   {p : ℕ}
--   {k : ZMod p}
--   {varStore : VarStore p}
--   {σ : HashConsSt p}
--   (h : .c k ∈ σ.exprs)
-- :
--   (mkConstant k >>= ([varStore|·])).run σ = (.some k, σ)
-- := by
--   simp
--   simp [StateT.run, h]
--   unfold_projs
--   grind

-- @[simp, grind =]
-- lemma run_mkConstant_eval_c_of_notMem
--   {p : ℕ}
--   {k : ZMod p}
--   {varStore : VarStore p}
--   {σ : HashConsSt p}
--   (h : .c k ∉ σ.exprs)
-- :
--   (mkConstant k >>= ([varStore|·])).run σ = (.some k, σ.pushExpr (.c k) sorry)
-- := by
--   simp
--   simp [StateT.run, h]
--   unfold_projs
--   simp


end

@[simp, grind =]
lemma eval_c
  {p : ℕ}
  {k : ZMod p}
  {varStore : VarStore p}
  {σ : HashConsSt p}
:
  [varStore,σ|mkConstant k] =
  (
    .some k,
    if CacheExpr.c k ∈ σ.exprs
    then σ
    else HashConsSt.pushExpr (CacheExpr.c k) σ wellFormed_c
  )
:= by
  unfold eval
  simp
  
  -- aesop (add simp [Functor.map]) (add safe (by grind))

-- @[simp, grind .]
-- lemma eval_ofNat {p n : ℕ} {varStore : VarStore p} :
--   [varStore|no_index (OfNat.ofNat n)] = .some n := by
--   simp [FixedExp.eval]

-- @[simp, grind =]
-- lemma eval_v
--   {p : ℕ}
--   {varIdx : ℕ}
--   {varStore : VarStore p}
-- :
--   [varStore|Exp.v varIdx] = varStore[varIdx]?
-- := by
--   simp [FixedExp.eval]

-- @[simp, grind =]
-- lemma add_def
--   {p : ℕ}
--   {a b : FixedExp p}
-- :
--   a + b =
--   Exp.add a b
-- := by
--   simp [HAdd.hAdd, Add.add]

-- -- @[simp, grind =]
-- @[grind =]
-- lemma sub_def
--   {p : ℕ}
--   {a b : FixedExp p}
-- :
--   a - b =
--   Exp.sub a b
-- := by
--   simp [HSub.hSub, Sub.sub]

-- @[simp, grind =]
-- lemma mul_def
--   {p : ℕ}
--   {a b : FixedExp p}
-- :
--   a * b =
--   Exp.mul a b
-- := by
--   simp [HMul.hMul, Mul.mul]

-- @[simp, grind =]
-- lemma eval_add
--   {p : ℕ}
--   {varStore : VarStore p}
--   {a b : FixedExp p}
-- :
--   [varStore|Exp.add a b] =
--   (do (←eval varStore a) + (←eval varStore b))
-- := rfl

-- @[grind .]
-- lemma eval_none_add
--   {p : ℕ}
--   {varStore : VarStore p}
--   {a b : FixedExp p}
--   (h : [varStore|a] = .none)
-- :
--   [varStore|Exp.add a b] =
--   .none
-- := by
--   simp [FixedExp.eval, h]

-- @[grind .]
-- lemma eval_add_none
--   {p : ℕ}
--   {varStore : VarStore p}
--   {a b : FixedExp p}
--   (h : [varStore|b] = .none)
-- :
--   [varStore|Exp.add a b] =
--   .none
-- := by
--   simp [FixedExp.eval, h]

-- @[simp, grind =]
-- lemma eval_sub
--   {p : ℕ}
--   {varStore : VarStore p}
--   {a b : FixedExp p}
-- :
--   [varStore|Exp.sub a b] =
--   (do (←eval varStore a) - (←eval varStore b))
-- := rfl

-- @[grind .]
-- lemma eval_none_sub
--   {p : ℕ}
--   {varStore : VarStore p}
--   {a b : FixedExp p}
--   (h : [varStore|a] = .none)
-- :
--   [varStore|Exp.sub a b] =
--   .none
-- := by
--   simp [FixedExp.eval, h]

-- @[grind .]
-- lemma eval_sub_none
--   {p : ℕ}
--   {varStore : VarStore p}
--   {a b : FixedExp p}
--   (h : [varStore|b] = .none)
-- :
--   [varStore|Exp.sub a b] =
--   .none
-- := by
--   simp [FixedExp.eval, h]

-- @[simp, grind =]
-- lemma eval_mul
--   {p : ℕ}
--   {varStore : VarStore p}
--   {a b : FixedExp p}
-- :
--   [varStore|Exp.mul a b] =
--   (do (←eval varStore a) * (←eval varStore b))
-- := rfl

-- @[grind .]
-- lemma eval_none_mul
--   {p : ℕ}
--   {varStore : VarStore p}
--   {a b : FixedExp p}
--   (h : [varStore|a] = .none)
-- :
--   [varStore|Exp.mul a b] =
--   .none
-- := by
--   simp [FixedExp.eval, h]

-- @[grind .]
-- lemma eval_mul_none
--   {p : ℕ}
--   {varStore : VarStore p}
--   {a b : FixedExp p}
--   (h : [varStore|b] = .none)
-- :
--   [varStore|Exp.mul a b] =
--   .none
-- := by
--   simp [FixedExp.eval, h]

end Clap.HashConsM
