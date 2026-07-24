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

inductive CacheExpr (p : ℕ)
  | c (_ : ZMod p)
  | v (idx : ℕ)
  | binary_op (lhs rhs : ExprRef) (op : BinaryOp)
deriving BEq, Hashable

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
  exprs : Array (CacheExpr p)
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
  exprs :=  σ.exprs.push e
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
  else if h: e.wellFormed state.exprs.size then
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

def eval_impl {p}
  (Γ : VarStore p)
  (e : ExprRef)
  (cache : Std.ExtHashMap ExprRef (Option (ZMod p)))
  (state : HashConsSt p)
:
  Std.ExtHashMap ExprRef (Option (ZMod p))
:=
  let cached_result := cache.get? e
  match cached_result with
  | .some result => cache
  | .none =>
    match h: state.exprs[e]? with
    | .none => cache
    | .some expr =>
      match expr with
      | .c value => cache.insert e (.some value)
      | .v idx => cache.insert e (Γ.get? idx)
      | .binary_op lhs rhs op =>
        have lhs_precedes_your_index : lhs < e := by
          grind [HashConsSt.wellFormed, CacheExpr.wellFormed]
        let lhs_cache := eval_impl Γ lhs cache state
        let lhs_val := (lhs_cache.get? lhs).join
        have rhs_precedes_your_index : rhs < e := by
          grind [HashConsSt.wellFormed, CacheExpr.wellFormed]
        let rhs_cache := eval_impl Γ rhs lhs_cache state
        let rhs_val := (rhs_cache.get? rhs).join
        rhs_cache.insert e ((match op with
          | .add => (· + ·)
          | .sub => (· - ·)
          | .mul => (· * ·)
        ) <$> (rhs_cache.get? lhs).join <*> (rhs_cache.get? rhs).join)
termination_by e

def eval {p} (Γ : VarStore p) (e : ExprRef) : HashConsM p (Option (ZMod p)) := do
  let cache : Std.ExtHashMap ExprRef (Option (ZMod p)) := {}
  let post_cache := eval_impl Γ e cache (←get)
  return (post_cache.get? e).join

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
  (h : σ.exprs.constains (.c k)):
  ((mkConstant k) >>= f).run σ = _ := by
  unfold_projs
  unfold StateT.bind
  ext1 x
  unfold mkConstant HashConsM.saveExpr


@[simp, grind =]
lemma eval_c
  {p : ℕ}
  {k : ZMod p}
  {varStore : VarStore p}
:
  (mkConstant k >>= fun constant ↦ eval varStore constant) =
  pure (.some k)
:= by
  unfold_projs
  ext1 σ
  

  unfold mkConstant

  apply Iff.intro
  · intros h
    rw [←h]
    have : (((StateT.pure (some k)).run σ) : Id (Option (ZMod p) × HashConsSt p)).run.1 = k := by rfl
    rw [this]
    unfold mkConstant
    unfold HashConsM.saveExpr
    simp
    done
  

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
