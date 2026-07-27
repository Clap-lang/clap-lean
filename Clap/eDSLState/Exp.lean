import Clap.Circuit

import Clap.eDSLState.Varstore
import Clap.eDSLState.Wheels

namespace Clap

-- abbrev FixedExp (p : ℕ) := Clap.Exp p ℕ

-- def FixedExp.size {p : ℕ} (exp : FixedExp p) : ℕ :=
--   match exp with
--   | .v _ => 1
--   | .c _ => 1
--   | .add l r => size l + size r + 1
--   | .mul l r => size l + size r + 1
--   | .sub l r => size l + size r + 1

-- abbrev FixedCircuit (p : ℕ) := Clap.Circuit p ℕ

-- def FixedExp.eval {p : ℕ} (varStore : VarStore p) (x : FixedExp p) : Option (ZMod p) :=
--   match x with
--   | .c x => .some x
--   | .v x => varStore[x]?
--   | .add l r => do (←eval varStore l) + (←eval varStore r)
--   | .sub l r => do (←eval varStore l) - (←eval varStore r)
--   | .mul l r => do (←eval varStore l) * (←eval varStore r)

def VarStore.ofArray {p : ℕ} (elem : Array (ℕ × ZMod p)) : VarStore p :=
  Std.ExtTreeMap.ofArray elem (cmp := compare)

-- def mkBigExpr : FixedExp 57 :=
--   go 1_000_00 (.c 4)
--   where
--     go (n : ℕ) (res : FixedExp 57) : FixedExp 57 :=
--       match n with
--       | 0 => res
--       | n + 1 => go n (res.add (.v 0))

-- def sigma {p} (x : FixedExp p) : FixedExp p :=
--   let x2 := x * x
--   let x4 := x2 * x2
--   x4 * x

-- def mkSigmaExpr (n : ℕ) : FixedExp 21888242871839275222246405745257275088696311157297823662689037894645226208583 :=
--   Array.range n |>.foldl (init := .c 2) fun acc _ ↦ sigma acc

abbrev ExprRef := ℕ

inductive BinaryOp
  | add
  | sub
  | mul
deriving BEq, Hashable

instance : LawfulBEq BinaryOp where
  rfl {a} := by unfold_projs
                unfold instBEqBinaryOp.beq
                aesop
  eq_of_beq {a b} (h) := by
    unfold_projs at h
    unfold instBEqBinaryOp.beq at h
    grind [cases BinaryOp]

inductive CacheExpr (p : ℕ)
  | c (_ : ZMod p)
  | v (idx : ℕ)
  | binary_op (lhs rhs : ExprRef) (op : BinaryOp)
deriving BEq, Hashable

instance {p} : LawfulBEq (CacheExpr p) where
  rfl {a} := by
    unfold_projs
    unfold instBEqCacheExpr.beq
    aesop (add safe cases [BinaryOp, CacheExpr])
  eq_of_beq {a b} (h) := by
    unfold_projs at h
    unfold instBEqCacheExpr.beq at h
    aesop (add safe cases [BinaryOp, CacheExpr])

-- structure Exprs (p : ℕ) where
--   exprs : Array (Expr' p)

-- #eval mkSigmaExpr 5

def CacheExpr.wellFormed {p : ℕ} (e : CacheExpr p) (idx : ExprRef) : Prop :=
  match e with
    | c _ => True
    | v _ => True
    | binary_op lhs rhs _ =>
      lhs < idx ∧
      rhs < idx

instance {p} {e : CacheExpr p} {idx : ExprRef} : Decidable (CacheExpr.wellFormed e idx) := by
  unfold CacheExpr.wellFormed
  split <;> infer_instance

/-
 options
1a. pushExpr can fail if references are not extant, and store a proof that they are
1b. wrap pushExpr with the check, take proof?
2. child references are jumps (1+stored value backwards)
-/

structure HashConsSt (p : ℕ) where
  exprs : Array (CacheExpr p) -- ℕ → Expr
  wellFormed : ∀ i < exprs.size, exprs[i]?.any (·.wellFormed i)

def HashConsSt.empty (p : ℕ) : HashConsSt p where
  exprs := #[]
  wellFormed := by simp

instance {p} : EmptyCollection (HashConsSt p) := ⟨HashConsSt.empty p⟩

def HashConsSt.pushExpr {p : ℕ}
  (e : CacheExpr p)
  (σ : HashConsSt p)
  (h_wellFormed : e.wellFormed σ.exprs.size)
: HashConsSt p where
  exprs := σ.exprs.push e
  wellFormed := by
    intro i h_i
    simp at h_i
    obtain ⟨exprs, exprs_wellformed⟩ := σ
    simp_all only [CacheExpr.wellFormed.eq_def]
    by_cases h_eq : i = exprs.size
    . aesop
    . have h_lt : i < exprs.size := by omega
      specialize exprs_wellformed i h_lt
      convert exprs_wellformed using 2
      . grind

abbrev HashConsM (p : ℕ) := StateM (HashConsSt p)

def HashConsM.getExprs {p : ℕ} : HashConsM p (Array (CacheExpr p)) :=
  return (←get).exprs

def HashConsM.saveExpr {p : ℕ} (e : CacheExpr p) : HashConsM p (ExprRef) := do
  let state ← get
  if state.exprs.contains e then
    return state.exprs.idxOf e
  else if h : e.wellFormed state.exprs.size then
    let post_state := state.pushExpr e h
    set post_state
    return state.exprs.size
  else pure 42

def mkConstant {p : ℕ} (x : ZMod p) : HashConsM p ExprRef := do
  HashConsM.saveExpr (.c x)

def mkAdd {p : ℕ} (l r : ExprRef) : HashConsM p ExprRef := do
  HashConsM.saveExpr (.binary_op l r .add)

def mkSub {p : ℕ} (l r : ExprRef) : HashConsM p ExprRef := do
  HashConsM.saveExpr (.binary_op l r .sub)

def mkMul {p : ℕ} (l r : ExprRef) : HashConsM p ExprRef := do
  HashConsM.saveExpr (.binary_op l r .mul)

variable {p} {varStore : VarStore p} {k : ZMod p} {cache : Std.ExtHashMap ExprRef (Option (ZMod p))}
         {σ : HashConsSt p} {ref : ExprRef}

instance : Membership ExprRef (HashConsSt p) where
  mem coll ref := ref < coll.exprs.size

@[simp, grind _=_]
lemma mem_exprs_iff {σ : HashConsSt p} : ref ∈ σ ↔ ref < σ.exprs.size := by
  rfl

instance : GetElem (HashConsSt p) ExprRef (CacheExpr p) (fun σ ref ↦ ref ∈ σ) where
  getElem coll idx h := coll.exprs[idx]'h

instance : GetElem? (HashConsSt p) ExprRef (CacheExpr p) (fun σ ref ↦ ref ∈ σ) where
  getElem? coll idx := coll.exprs[idx]?

@[simp, grind _=_]
lemma getElem?_eq {σ : HashConsSt p} : σ[ref]? = σ.exprs[ref]? := by
  rfl

def evalAux {p}
  (Γ : VarStore p)
  (e : ExprRef)
  (cache : Std.ExtHashMap ExprRef (Option (ZMod p)))
  (state : HashConsSt p)
:
  Std.ExtHashMap ExprRef (Option (ZMod p))
:=
  match cache[e]? with
  | .some result => cache
  | .none =>
    match h : state[e]? with
    | .none => cache
    | .some expr =>
      match expr with
      | .c value => cache.insert e (.some value)
      | .v idx => cache.insert e (Γ.get? idx)
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

@[aesop unsafe, grind .]
lemma evalAux_of_mem_cache (h : ref ∈ cache) :
  evalAux varStore ref cache σ = cache := by grind [=evalAux]

-- def eval {p} (Γ : VarStore p) (e : ExprRef) : HashConsM p (Option (ZMod p)) := do
--   letI cache : Std.ExtHashMap ExprRef (Option (ZMod p)) := {}
--   letI post_cache := evalAux Γ e cache (←get)
--   return (post_cache.get? e).join

def eval {p} (Γ : VarStore p) (e : HashConsM p ExprRef) : HashConsM p (Option (ZMod p)) := do
  let expr ← e
  letI post_cache := evalAux Γ expr {} (←get)
  return (post_cache.get? expr).join

notation "[" varStore "|" x "]" => eval varStore x

/--
NB:
  This is a poor man's monad-style thing that doesn't introduce abstraction layers.

  Another option is something that says `x =ΓvarStore y` but that would be too much clutter
  unless we use the symbol `Γ` consistently instead of `varStore`.
-/
notation "[" varStore "|" x " =Γ " y "]" => [varStore|x] = [varStore|y]

-- def evalSigma (p : ℕ) : HashConsM p (Option (ZMod p)) := do
--   let x ← mkSigmaExpr p 1028
--   let val ← eval {} x
--   return val

-- instance {p} : Membership (FixedExp p) (VarStore p) := ⟨fun Γ x ↦ [Γ|x].isSome⟩

namespace FixedExp

variable {p : ℕ} {e : CacheExpr p} {σ : HashConsSt p}

lemma HashConsM.run_saveExpr_of_wellFormed (h : e.wellFormed σ.exprs.size) :
  (HashConsM.saveExpr e).run σ =
  if σ.exprs.contains e
  then (σ.exprs.idxOf e, σ)
  else (σ.exprs.size, HashConsSt.pushExpr e σ h) := by
  unfold HashConsM.saveExpr
  aesop

@[simp, grind .]
lemma wellFormed_c {p} {k : ZMod p} {n : ℕ} : (CacheExpr.c k).wellFormed n := trivial

@[simp, grind =]
lemma HashConsM.run_mkConstant {p} {k : ZMod p} {σ : HashConsSt p} :
  (mkConstant k).run σ =
  if σ.exprs.contains (.c k)
  then (σ.exprs.idxOf (.c k), σ) 
  else (σ.exprs.size, σ.pushExpr (.c k) (by simp)) :=
  run_saveExpr_of_wellFormed wellFormed_c

@[simp, grind =]
lemma HashConsM.bind_mkConstant_of_contains {p} {σ} {α} {k : ZMod p} {f : ExprRef → HashConsM p α}
  (h : σ.exprs.contains (.c k)) :
  (mkConstant k >>= f).run σ = f (σ.exprs.idxOf (.c k)) σ := by aesop

@[simp, grind =]
lemma HashConsM.bind_mkConstant_of_contains' {p} {σ} {α} {k : ZMod p} {f : ExprRef → HashConsM p α}
  (h : σ.exprs.contains (.c k)) :
  ((mkConstant k).bind f).run σ = f (σ.exprs.idxOf (.c k)) σ :=
  HashConsM.bind_mkConstant_of_contains h

section

variable {varStore : VarStore p} {k : ZMod p} {cache : Std.ExtHashMap ExprRef (Option (ZMod p))}
         {σ : HashConsSt p} {ref : ExprRef}

@[aesop unsafe, grind .]
lemma evalAux_of_mem_cache (h : ref ∈ cache) :
  evalAux varStore ref cache σ = cache := by grind [=evalAux]

@[aesop unsafe, grind .]
lemma evalAux_of_not_mem_cache_not_mem_state (h₁ : ref ∉ cache) (h₂ : ref ∉ σ) :
  evalAux varStore ref cache σ = cache := by
  grind [=evalAux]

@[aesop unsafe, grind =>]
lemma evalAux_of_not_mem_cache_mem_state_some_c (h₁ : ref ∉ cache) (h₂ : σ[ref]? = .some (.c k)) :
  evalAux varStore ref cache σ = cache.insert ref (.some k) := by
  grind [=evalAux]

@[simp, grind =]
lemma HashConsM.get_eq : (get (m := HashConsM p) σ) = (σ, σ) := rfl

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

end FixedExp

def HashConsM.runGet? (ref : HashConsM p ExprRef) (σ : HashConsSt p) : Option (CacheExpr p) :=
  let (ref', σ') := ref.run σ
  σ'[ref']?

namespace FixedExp

section

variable {varStore : VarStore p} {k : ZMod p} {cache : Std.ExtHashMap ExprRef (Option (ZMod p))}
         {σ : HashConsSt p} {ref : ExprRef}

@[grind _=_]
lemma runGet_def {ref : HashConsM p ExprRef} :
  ref.runGet? σ = (StateT.run ref σ).2[(StateT.run ref σ).1]? := rfl

attribute [local grind ext]
  Option.ext Prod.ext Id.ext

lemma blah {ref : HashConsM p ExprRef}
           (h : ref.runGet? σ = .some (.c k)) :
  [varStore|ref].run σ = (.some k, (ref.run σ).2) := by
  simp [eval]
  grind [=Id.run, Functor.map]

@[simp, grind =]
lemma _root_.Array.getElem_idxOf {α : Type} {a : Array α} {x : α} [BEq α] [LawfulBEq α] (h : a.idxOf x < a.size) :
  a[a.idxOf x]'h = x := by
  rcases a with ⟨a⟩
  simp

@[grind =]
lemma _root_.Id.pure_eq {α : Type} {x : α} : pure (f := Id) x = x := by rfl

@[grind .]
lemma run_eval_idxOf_c_of_contains {varStore : VarStore p} {k : ZMod p}
  (h : σ.exprs.contains (.c k)) :
  [varStore|σ.exprs.idxOf (.c k)].run σ = (some k, σ) := by
  simp [eval]
  rw [evalAux_of_not_mem_cache_mem_state_some_c (k := k)] <;> grind

@[grind .]
lemma run_eval_idxOf_c_of_contains' {varStore : VarStore p} {k : ZMod p}
  (h : σ.exprs.contains (.c k)) :
  [varStore|σ.exprs.idxOf (.c k)] σ = (some k, σ) :=
  run_eval_idxOf_c_of_contains h

@[aesop unsafe, grind .]
lemma HashConsSt.exprs_mem_pushExpr (h : e.wellFormed σ.exprs.size) :
  e ∈ (σ.pushExpr e h).exprs := by
  simp [HashConsSt.pushExpr]

lemma eval_pushExpr (h : (CacheExpr.c k).wellFormed σ.exprs.size) :
  [varStore|σ.exprs.size] (σ.pushExpr (.c k) h) = (_, _) := by
  sorry

@[simp, grind =]
lemma run_mkConstant_eval_c_of_mem
  {p : ℕ}
  {k : ZMod p}
  {varStore : VarStore p}
  {σ : HashConsSt p}
  (h : .c k ∈ σ.exprs)
:
  (mkConstant k >>= ([varStore|·])).run σ = (.some k, σ)
:= by  
  simp
  simp [StateT.run, h]
  unfold_projs
  grind

@[simp, grind =]
lemma run_mkConstant_eval_c_of_notMem
  {p : ℕ}
  {k : ZMod p}
  {varStore : VarStore p}
  {σ : HashConsSt p}
  (h : .c k ∉ σ.exprs)
:
  (mkConstant k >>= ([varStore|·])).run σ = (.some k, σ.pushExpr (.c k) sorry)
:= by  
  simp
  simp [StateT.run, h]
  unfold_projs
  simp


end

@[simp, grind =]
lemma eval_c
  {p : ℕ}
  {k : ZMod p}
  {varStore : VarStore p}
:
  [varStore|mkConstant k] = .some k
:= by
  simp [FixedExp.eval]

@[simp, grind .]
lemma eval_ofNat {p n : ℕ} {varStore : VarStore p} :
  [varStore|no_index (OfNat.ofNat n)] = .some n := by
  simp [FixedExp.eval]

@[simp, grind =]
lemma eval_v
  {p : ℕ}
  {varIdx : ℕ}
  {varStore : VarStore p}
:
  [varStore|Exp.v varIdx] = varStore[varIdx]?
:= by
  simp [FixedExp.eval]

@[simp, grind =]
lemma add_def
  {p : ℕ}
  {a b : FixedExp p}
:
  a + b =
  Exp.add a b
:= by
  simp [HAdd.hAdd, Add.add]

-- @[simp, grind =]
@[grind =]
lemma sub_def
  {p : ℕ}
  {a b : FixedExp p}
:
  a - b =
  Exp.sub a b
:= by
  simp [HSub.hSub, Sub.sub]

@[simp, grind =]
lemma mul_def
  {p : ℕ}
  {a b : FixedExp p}
:
  a * b =
  Exp.mul a b
:= by
  simp [HMul.hMul, Mul.mul]

@[simp, grind =]
lemma eval_add
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
:
  [varStore|Exp.add a b] =
  (do (←eval varStore a) + (←eval varStore b))
:= rfl

@[grind .]
lemma eval_none_add
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
  (h : [varStore|a] = .none)
:
  [varStore|Exp.add a b] =
  .none
:= by
  simp [FixedExp.eval, h]

@[grind .]
lemma eval_add_none
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
  (h : [varStore|b] = .none)
:
  [varStore|Exp.add a b] =
  .none
:= by
  simp [FixedExp.eval, h]

@[simp, grind =]
lemma eval_sub
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
:
  [varStore|Exp.sub a b] =
  (do (←eval varStore a) - (←eval varStore b))
:= rfl

@[grind .]
lemma eval_none_sub
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
  (h : [varStore|a] = .none)
:
  [varStore|Exp.sub a b] =
  .none
:= by
  simp [FixedExp.eval, h]

@[grind .]
lemma eval_sub_none
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
  (h : [varStore|b] = .none)
:
  [varStore|Exp.sub a b] =
  .none
:= by
  simp [FixedExp.eval, h]

@[simp, grind =]
lemma eval_mul
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
:
  [varStore|Exp.mul a b] =
  (do (←eval varStore a) * (←eval varStore b))
:= rfl

@[grind .]
lemma eval_none_mul
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
  (h : [varStore|a] = .none)
:
  [varStore|Exp.mul a b] =
  .none
:= by
  simp [FixedExp.eval, h]

@[grind .]
lemma eval_mul_none
  {p : ℕ}
  {varStore : VarStore p}
  {a b : FixedExp p}
  (h : [varStore|b] = .none)
:
  [varStore|Exp.mul a b] =
  .none
:= by
  simp [FixedExp.eval, h]

end FixedExp

end Clap
