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
  if state.exprs.contains e then
    return state.exprs.idxOf e
  else if h : e.wellFormed state.exprs.size then
    let post_state := state.pushExpr e h
    set post_state
    return state.exprs.size
  else pure 42

variable {e : CacheExpr p} {σ : HashConsSt p}

lemma run_saveExpr_of_wellFormed (h : e.wellFormed σ.exprs.size) :
  (HashConsM.saveExpr e).run σ =
  if σ.exprs.contains e
  then (σ.exprs.idxOf e, σ)
  else (σ.exprs.size, HashConsSt.pushExpr e σ h)
:= by
  unfold HashConsM.saveExpr
  aesop

lemma run_saveExpr_of_contains (h : σ.exprs.contains e) :
  (HashConsM.saveExpr e).run σ =
  (σ.exprs.idxOf e, σ)
:= by
  unfold HashConsM.saveExpr
  aesop

end SaveExpr


section Membership

instance : Membership ExprRef (HashConsSt p) where
  mem coll ref := ref < coll.exprs.size

variable {σ : HashConsSt p} {ref : ExprRef}

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

end Membership

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

@[simp, grind =]
lemma run_mkConstant {p} {k : ZMod p} {σ : HashConsSt p} :
  (mkConstant k).run σ =
  if σ.exprs.contains (.c k)
  then (σ.exprs.idxOf (.c k), σ)
  else (σ.exprs.size, σ.pushExpr (.c k) (by simp)) :=
  run_saveExpr_of_wellFormed wellFormed_c

@[simp, grind =]
lemma run_mkVar {p} {k : ℕ} {σ : HashConsSt p} :
  (mkVar k).run σ =
  if σ.exprs.contains (.v k)
  then (σ.exprs.idxOf (.v k), σ)
  else (σ.exprs.size, σ.pushExpr (.v k) (by simp)) :=
  run_saveExpr_of_wellFormed wellFormed_v

@[simp, grind =]
lemma bind_mkConstant_of_contains {p} {σ} {α} {k : ZMod p} {f : ExprRef → HashConsM p α}
  (h : σ.exprs.contains (.c k)) :
  (mkConstant k >>= f).run σ = (f (σ.exprs.idxOf (.c k))).run σ := by aesop

@[simp, grind =]
lemma bind_mkConstant_of_contains' {p} {σ} {α} {k : ZMod p} {f : ExprRef → HashConsM p α}
  (h : σ.exprs.contains (.c k)) :
  ((mkConstant k).bind f).run σ = (f (σ.exprs.idxOf (.c k))).run σ :=
  HashConsM.bind_mkConstant_of_contains h

@[simp, grind =]
lemma bind_mkVar_of_contains {p} {σ} {α} {k : ℕ} {f : ExprRef → HashConsM p α}
  (h : σ.exprs.contains (.v k)) :
  (mkVar k >>= f).run σ = (f (σ.exprs.idxOf (.v k))).run σ := by aesop

@[simp, grind =]
lemma bind_mkVar_of_contains' {p} {σ} {α} {k : ℕ} {f : ExprRef → HashConsM p α}
  (h : σ.exprs.contains (.v k)) :
  ((mkVar k).bind f).run σ = (f (σ.exprs.idxOf (.v k))).run σ :=
  HashConsM.bind_mkVar_of_contains h

end MkExpr


section Run

@[grind =]
def run {α} (cmd : HashConsM p α) (state : HashConsSt p) : α × (HashConsSt p) :=
  (StateT.run cmd state).run

def runGet? (ref : HashConsM p ExprRef) (σ : HashConsSt p) : Option (CacheExpr p) :=
  let (ref', σ') := ref.run σ
  σ'[ref']?

end Run

end Clap.HashConsM
