import Clap.eDSLState.HashCons.CacheExpr
import Clap.eDSLState.HashCons.HashConsM
import Clap.eDSLState.HashCons.HashConsSt

namespace Clap

abbrev ValueCache (p : ℕ) := Array (Option (ZMod p))

@[grind cases]
structure Expr (p : ℕ) where
  ref : ExprRef
  σ : HashConsSt p

namespace Expr

notation "⦃" ref ", " σ "⦄" => Expr.mk ref σ

section Expr

variable {p : ℕ} {e : Expr p}

@[grind =]
def deref (e : Expr p) : Option (CacheExpr p) := e.σ.exprs[e.ref]?

/--
Dereference is valid.
-/
def wellFormed (e : Expr p) : Prop := e.ref < e.σ.size

instance : Decidable (wellFormed e) := inferInstanceAs <| Decidable (e.ref < e.σ.size)

prefix:max "*" => deref

@[grind _=_]
lemma wellFormed_iff_isSome : e.wellFormed ↔ (*e).isSome := by grind [=wellFormed]

@[grind →]
lemma wellFormed_frame {e' : Expr p}
  (h₁ : e.wellFormed) (h₂ : e.σ.exprs.isPrefixOf e'.σ.exprs) (h₃ : e.ref = e'.ref) : e'.wellFormed := by
  have : e.σ.exprs.toList.isPrefixOf e'.σ.exprs.toList = true := by grind
  grind [List.prefix_iff_getElem?]

@[grind =]
lemma deref_mk_size_push
  {e}
  {σ : HashConsSt p}
  {h: e.wellFormed σ.size}
:
  *(Expr.mk σ.size (σ.pushExpr e h)) =
  .some e
:= by
  grind

@[grind =]
lemma deref_idxOf_of_mem
  {cacheExpr : CacheExpr p}
  {σ : HashConsSt p}
  (h_mem : cacheExpr ∈ σ.exprs)
:
  *⦃σ.exprs.idxOf cacheExpr, σ⦄ = cacheExpr
:= by
  grind

@[simp, grind =]
lemma deref_mkConstant_eq_some
  {c : ZMod p}
  {σ : HashConsSt p}
:
  *⦃(HashConsM.mkConstant c).getResult σ, (HashConsM.mkConstant c).getHashConsState σ⦄ =
  .some (CacheExpr.c c)
:= by
  grind

@[simp, grind =]
lemma deref_mkVar_eq_some
  {idx : ℕ}
  {σ : HashConsSt p}
:
  *⦃(HashConsM.mkVar idx).getResult σ, (HashConsM.mkVar idx).getHashConsState σ⦄ =
  .some (CacheExpr.v idx)
:= by
  grind [=HashConsM.mkVar]

@[grind =]
lemma deref_mkAdd_eq_some
  {l r : ExprRef}
  {σ : HashConsSt p}
  (h_l : ⦃l,σ⦄.wellFormed)
  (h_r : ⦃r,σ⦄.wellFormed)
:
  *⦃(HashConsM.mkAdd l r).getResult σ, (HashConsM.mkAdd l r).getHashConsState σ⦄ =
  .some (CacheExpr.binary_op l r .add)
:= by
  unfold HashConsM.mkAdd
  grind

@[grind =]
lemma deref_mkSub_eq_some
  {l r : ExprRef}
  {σ : HashConsSt p}
  (h_l : ⦃l,σ⦄.wellFormed)
  (h_r : ⦃r,σ⦄.wellFormed)
:
  *⦃(HashConsM.mkSub l r).getResult σ, (HashConsM.mkSub l r).getHashConsState σ⦄ =
  .some (CacheExpr.binary_op l r .sub)
:= by
  unfold HashConsM.mkSub
  grind

@[grind =]
lemma deref_mkMul_eq_some
  {l r : ExprRef}
  {σ : HashConsSt p}
  (h_l : ⦃l,σ⦄.wellFormed)
  (h_r : ⦃r,σ⦄.wellFormed)
:
  *⦃(HashConsM.mkMul l r).getResult σ, (HashConsM.mkMul l r).getHashConsState σ⦄ =
  .some (CacheExpr.binary_op l r .mul)
:= by
  unfold HashConsM.mkMul
  grind

end Expr

end Expr

end Clap
