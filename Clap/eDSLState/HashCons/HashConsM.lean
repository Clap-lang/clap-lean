import Clap.eDSLState.HashCons.HashConsSt

namespace Clap

abbrev HashConsM (p : ℕ) := StateM (HashConsSt p)

namespace HashConsM

variable {p : ℕ}

def getExprs : HashConsM p (Array (CacheExpr p)) :=
  return (←get).exprs

section SaveExpr

def saveExpr (e : CacheExpr p) : HashConsM p ExprRef := do
  let state ← get
  if e ∈ state.exprs then
    return state.exprs.idxOf e
  else if h : e.wellFormed state.size then
    let post_state := state.pushExpr e h
    set post_state
    return state.exprs.size
  else pure 42

variable {e : CacheExpr p} {σ : HashConsSt p}

@[grind =]
def run {α} (cmd : HashConsM p α) (state : HashConsSt p) : α × (HashConsSt p) :=
  StateT.run cmd state

def getResult {α} (action : HashConsM p α) (σ : HashConsSt p) : α :=
  (action.run σ).1

def getHashConsState {α} (action : HashConsM p α) (σ : HashConsSt p) : HashConsSt p :=
  (action.run σ).2

def wellFormed
  {p : ℕ}
  {α}
  (σ : HashConsSt p)
  (action : HashConsM p α)
: Prop :=
  σ.exprs.isPrefixOf (action.getHashConsState σ).exprs

@[grind .]
lemma run_saveExpr_of_wellFormed (h : e.wellFormed σ.exprs.size) :
  (HashConsM.saveExpr e).run σ =
  if e ∈ σ.exprs
  then (σ.exprs.idxOf e, σ)
  else (σ.exprs.size, HashConsSt.pushExpr e σ h)
:= by
  unfold HashConsM.saveExpr run
  grind

lemma run_saveExpr_of_mem (h : e ∈ σ) :
  (saveExpr e).run σ =
  (σ.exprs.idxOf e, σ)
:= by
  unfold saveExpr run
  aesop (add simp HashConsSt.mem_def)

@[grind =]
lemma size_saveExpr_of_mem (h : e ∈ σ) : ((saveExpr e).run σ).2.size = σ.size := by
  rw [run_saveExpr_of_mem (by grind)]

end SaveExpr

section Membership

instance : Membership ExprRef (HashConsSt p) where
  mem coll ref := ref < coll.exprs.size

variable {σ : HashConsSt p} {ref : ExprRef}

@[simp, grind _=_]
lemma mem_exprs_iff {σ : HashConsSt p} : ref ∈ σ ↔ ref < σ.size := by
  rfl

instance : GetElem (HashConsSt p) ExprRef (CacheExpr p) (fun σ ref ↦ ref ∈ σ) where
  getElem coll idx h := coll.exprs[idx]'h

instance : GetElem? (HashConsSt p) ExprRef (CacheExpr p) (fun σ ref ↦ ref ∈ σ) where
  getElem? coll idx := coll.exprs[idx]?

@[simp, grind _=_]
lemma getElem?_eq {σ : HashConsSt p} : σ[ref]? = σ.exprs[ref]? := by
  rfl

end Membership

section Run

def runGet? (ref : HashConsM p ExprRef) (σ : HashConsSt p) : Option (CacheExpr p) :=
  let (ref', σ') := ref.run σ
  σ'[ref']?

@[simp, grind =]
lemma run_bind {α β} (x : HashConsM p α) (f : α → HashConsM p β) (s : HashConsSt p)
  : run (x >>= f) s = letI res := run x s; run (f res.1) res.2  := rfl

end Run

section MkExpr

def mkConstant (x : ZMod p) : HashConsM p ExprRef := do
  HashConsM.saveExpr (.c x)

def mkVar (x : ℕ) : HashConsM p ExprRef := do
  HashConsM.saveExpr (.v x)

def mkAdd (l r : ExprRef) : HashConsM p ExprRef := do
  HashConsM.saveExpr (.binary_op l r .add)

def mkSub (l r : ExprRef) : HashConsM p ExprRef := do
  HashConsM.saveExpr (.binary_op l r .sub)

def mkMul (l r : ExprRef) : HashConsM p ExprRef := do
  HashConsM.saveExpr (.binary_op l r .mul)

section Lemmas

variable {k : ZMod p} {σ : HashConsSt p} {e! : ExprRef}

@[simp, grind =]
lemma run_mkConstant:
  (mkConstant k).run σ =
  if .c k ∈ σ.exprs
  then (σ.exprs.idxOf (.c k), σ)
  else (σ.size, σ.pushExpr (.c k) (by simp)) :=
  run_saveExpr_of_wellFormed wellFormed_c

@[simp, grind =]
lemma run_mkVar :
  (mkVar e!).run σ =
  if (.v e!) ∈ σ.exprs
  then (σ.exprs.idxOf (.v e!), σ)
  else (σ.exprs.size, σ.pushExpr (.v e!) (by simp)) :=
  run_saveExpr_of_wellFormed wellFormed_v

@[simp, grind =]
lemma bind_mkConstant_of_contains {α} {f : ExprRef → HashConsM p α}
  (h : .c k ∈ σ.exprs) :
  (mkConstant k >>= f).run σ = (f (σ.exprs.idxOf (.c k))).run σ := by aesop

@[simp, grind =]
lemma bind_mkConstant_of_contains' {α} {k : ZMod p} {f : ExprRef → HashConsM p α}
  (h : .c k ∈ σ.exprs) :
  ((mkConstant k).bind f).run σ = (f (σ.exprs.idxOf (.c k))).run σ :=
  HashConsM.bind_mkConstant_of_contains h

@[simp, grind =]
lemma bind_mkVar_of_contains {α} {k : ℕ} {f : ExprRef → HashConsM p α}
  (h : σ.exprs.contains (.v k)) :
  (mkVar k >>= f).run σ = (f (σ.exprs.idxOf (.v k))).run σ := by aesop

@[simp, grind =]
lemma bind_mkVar_of_contains' {α} {k : ℕ} {f : ExprRef → HashConsM p α}
  (h : σ.exprs.contains (.v k)) :
  ((mkVar k).bind f).run σ = (f (σ.exprs.idxOf (.v k))).run σ :=
  HashConsM.bind_mkVar_of_contains h

end Lemmas

end MkExpr

end Clap.HashConsM
