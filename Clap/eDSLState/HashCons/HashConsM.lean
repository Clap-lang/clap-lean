import Clap.eDSLState.HashCons.HashConsSt
import Mathlib.Tactic

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
    return state.size
  else pure 42

variable {e : CacheExpr p} {σ : HashConsSt p}

@[grind =]
def run {α} (cmd : HashConsM p α) (state : HashConsSt p) : α × (HashConsSt p) :=
  StateT.run cmd state

def getResult {α} (action : HashConsM p α) (σ : HashConsSt p) : α :=
  (action.run σ).1

def getHashConsState {α} (action : HashConsM p α) (σ : HashConsSt p) : HashConsSt p :=
  (action.run σ).2

@[grind .]
def wellFormed
  {p : ℕ}
  {α}
  (σ : HashConsSt p)
  (action : HashConsM p α)
: Prop :=
  σ.exprs.isPrefixOf (action.getHashConsState σ).exprs

@[grind =]
lemma run_saveExpr_of_wellFormed (h : e.wellFormed σ.size) :
  (HashConsM.saveExpr e).run σ =
  if e ∈ σ.exprs
  then (σ.exprs.idxOf e, σ)
  else (σ.size, HashConsSt.pushExpr e σ h)
:= by
  unfold HashConsM.saveExpr run
  grind

@[grind =]
lemma getResult_saveExpr_of_wellFormed (h : e.wellFormed σ.size) :
  (HashConsM.saveExpr e).getResult σ =
  if e ∈ σ.exprs
  then σ.exprs.idxOf e
  else σ.size
:= by
  unfold getResult
  grind

@[grind =]
lemma getHashConsState_saveExpr_of_wellFormed (h : e.wellFormed σ.size) :
  (HashConsM.saveExpr e).getHashConsState σ =
  if e ∈ σ.exprs
  then σ
  else HashConsSt.pushExpr e σ h
:= by
  unfold getHashConsState
  grind

@[grind =]
lemma run_saveExpr_of_mem (h : e ∈ σ) :
  (saveExpr e).run σ =
  (σ.exprs.idxOf e, σ)
:= by
  unfold saveExpr run
  aesop (add simp HashConsSt.mem_def)

@[grind =]
lemma run_saveExpr_of_notMem_wellFormed (h : e ∉ σ) (h₁ : e.wellFormed σ.size) :
  (saveExpr e).run σ =
  (σ.size, HashConsSt.pushExpr e σ h₁)
:= by
  unfold saveExpr run
  grind

@[grind =]
lemma size_getHashConsState_saveExpr_of_mem (h : e ∈ σ) :
  ((saveExpr e).getHashConsState σ).size = σ.size := by
  change ((saveExpr e).run σ).2.size = σ.size
  rw [run_saveExpr_of_mem (by grind)]

@[grind =]
lemma getResult_saveExpr_of_mem {e : CacheExpr p} (h : e ∈ σ) :
  (HashConsM.saveExpr e).getResult σ = σ.exprs.idxOf e := by
  unfold getResult
  rw [run_saveExpr_of_mem h]

@[grind =]
lemma getResult_saveExpr_of_notMem_wellFormed {e : CacheExpr p} (h : e ∉ σ) (h₁ : e.wellFormed σ.size) :
  (HashConsM.saveExpr e).getResult σ = σ.exprs.idxOf e := by
  unfold getResult
  grind

end SaveExpr

section Membership

instance : Membership ExprRef (HashConsSt p) where
  mem coll ref := ref < coll.size

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

variable {k : ZMod p} {σ : HashConsSt p} {e! e!₁ e!₂ : ExprRef}

@[grind =]
lemma getResult_of_mkSub_of_wellFormed
  (h₁ : (CacheExpr.binary_op (p := p) e!₁ e!₂ .sub).wellFormed σ.size) :
  (HashConsM.mkSub e!₁ e!₂).getResult σ = σ.exprs.idxOf (.binary_op (p := p) e!₁ e!₂ .sub) := by
  grind [=mkSub]

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
  else (σ.size, σ.pushExpr (.v e!) (by simp)) :=
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

@[simp, grind .]
lemma wellFormed_saveExpr {e} : (saveExpr e).wellFormed σ := by
  unfold wellFormed
  simp [getHashConsState]
  simp_all only [saveExpr, bind_pure_comp, run_bind]
  split
  next h => grind
  next h =>
    split
    next h_1 => change σ.exprs.isPrefixOf (σ.pushExpr e h_1).exprs = true
                unfold HashConsSt.pushExpr
                grind
    next h_1 => grind

@[simp, grind .]
lemma wellFormed_mkConstant : (mkConstant e!).wellFormed σ := by
  unfold mkConstant
  grind

@[simp, grind .]
lemma wellFormed_mkVar : (mkVar e!).wellFormed σ := by
  unfold mkVar
  grind

@[simp, grind .]
lemma wellFormed_mkAdd {l r} : (mkAdd l r).wellFormed σ := by
  unfold mkAdd
  grind

@[simp, grind .]
lemma wellFormed_mkSub {l r} : (mkSub l r).wellFormed σ := by
  unfold mkSub
  grind

@[simp, grind .]
lemma wellFormed_mkMul {l r} : (mkMul l r).wellFormed σ := by
  unfold mkMul
  grind

@[grind .]
lemma getResult_mkConstant {c}
:
  (mkConstant c).getResult σ =
  if (.c c) ∈ σ.exprs
  then σ.exprs.idxOf (.c c)
  else σ.size
:= by
  unfold getResult mkConstant
  grind

@[grind .]
lemma getHashConsState_mkConstant {c}
:
  (mkConstant c).getHashConsState σ =
  if (.c c) ∈ σ.exprs
  then σ
  else σ.pushExpr (.c c) (by grind)
:= by
  unfold getHashConsState mkConstant
  grind

@[grind .]
lemma getResult_lt_getHashConsState_size_mkConstant {c}
:
  (mkConstant c).getResult σ < ((mkConstant c).getHashConsState σ).size
:= by
  unfold mkConstant
  grind

@[grind .]
lemma getResult_mkVar {c}
:
  (mkConstant c).getResult σ =
  if (.c c) ∈ σ.exprs
  then σ.exprs.idxOf (.c c)
  else σ.size
:= by
  unfold getResult mkConstant
  grind

@[grind .]
lemma getHashConsState_mkVar {v}
:
  (mkVar v).getHashConsState σ =
  if (.v v) ∈ σ.exprs
  then σ
  else σ.pushExpr (.v v) (by grind)
:= by
  unfold getHashConsState mkVar
  grind

@[grind .]
lemma getResult_lt_getHashConsState_size_mkVar {v}
:
  (mkVar v).getResult σ < ((mkVar v).getHashConsState σ).size
:= by
  unfold mkVar
  grind

@[grind .]
lemma getResult_mkAdd_of_wellFormed {l r}
  (h_l : l < σ.size)
  (h_r : r < σ.size)
:
  (mkAdd l r).getResult σ =
  if (.binary_op l r .add) ∈ σ.exprs
  then σ.exprs.idxOf (.binary_op l r .add)
  else σ.size
:= by
  unfold getResult mkAdd
  grind

@[grind .]
lemma getHashConsState_mkAdd_of_wellFormed {l r}
  (h_l : l < σ.size)
  (h_r : r < σ.size)
:
  (mkAdd l r).getHashConsState σ =
  if (.binary_op l r .add) ∈ σ.exprs
  then σ
  else HashConsSt.pushExpr (.binary_op l r .add) σ (by grind)
:= by
  unfold mkAdd
  grind

@[grind .]
lemma getResult_lt_getHashConsState_size_mkAdd {l r}
  (h_l : l < σ.size)
  (h_r : r < σ.size)
:
  (mkAdd l r).getResult σ < ((mkAdd l r).getHashConsState σ).size
:= by
  unfold mkAdd
  grind

@[grind .]
lemma getResult_mkSub_of_wellFormed {l r}
  (h_l : l < σ.size)
  (h_r : r < σ.size)
:
  (mkSub l r).getResult σ =
  if (.binary_op l r .sub) ∈ σ.exprs
  then σ.exprs.idxOf (.binary_op l r .sub)
  else σ.size
:= by
  unfold getResult mkSub
  grind

@[grind .]
lemma getHashConsState_mkSub_of_wellFormed {l r}
  (h_l : l < σ.size)
  (h_r : r < σ.size)
:
  (mkSub l r).getHashConsState σ =
  if (.binary_op l r .sub) ∈ σ.exprs
  then σ
  else HashConsSt.pushExpr (.binary_op l r .sub) σ (by grind)
:= by
  unfold mkSub
  grind

@[grind .]
lemma getResult_lt_getHashConsState_size_mkSub {l r}
  (h_l : l < σ.size)
  (h_r : r < σ.size)
:
  (mkSub l r).getResult σ < ((mkSub l r).getHashConsState σ).size
:= by
  unfold mkSub
  grind

@[grind .]
lemma getResult_mkMul_of_wellFormed {l r}
  (h_l : l < σ.size)
  (h_r : r < σ.size)
:
  (mkMul l r).getResult σ =
  if (.binary_op l r .mul) ∈ σ.exprs
  then σ.exprs.idxOf (.binary_op l r .mul)
  else σ.size
:= by
  unfold getResult mkMul
  grind

@[grind .]
lemma getHashConsState_mkMul_of_wellFormed {l r}
  (h_l : l < σ.size)
  (h_r : r < σ.size)
:
  (mkMul l r).getHashConsState σ =
  if (.binary_op l r .mul) ∈ σ.exprs
  then σ
  else HashConsSt.pushExpr (.binary_op l r .mul) σ (by grind)
:= by
  unfold mkMul
  grind

@[grind .]
lemma getResult_lt_getHashConsState_size_mkMul {l r}
  (h_l : l < σ.size)
  (h_r : r < σ.size)
:
  (mkMul l r).getResult σ < ((mkMul l r).getHashConsState σ).size
:= by
  unfold mkMul
  grind

end Lemmas

end MkExpr

end Clap.HashConsM
