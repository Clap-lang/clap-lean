import Clap.eDSLState.HashCons.CacheExpr

namespace Clap

@[grind]
structure HashConsSt (p : ℕ) where
  exprs : Array (CacheExpr p) -- ℕ → Expr
  wellFormed : ∀ i < exprs.size, exprs[i]?.any (·.wellFormed i)

namespace HashConsSt

def empty (p : ℕ) : HashConsSt p where
  exprs := #[]
  wellFormed := by simp

@[simp, grind =]
def size {p} (σ : HashConsSt p) : ℕ :=
  σ.exprs.size

instance {p} : EmptyCollection (HashConsSt p) := ⟨HashConsSt.empty p⟩

variable {p : ℕ}

def pushExpr
  (e : CacheExpr p)
  (σ : HashConsSt p)
  (h_wellFormed : e.wellFormed σ.exprs.size)
: HashConsSt p where
  exprs := σ.exprs.push e
  wellFormed := by
    intro i h_i
    obtain ⟨exprs, exprs_wellformed⟩ := σ
    simp at h_i
    by_cases h_eq : i = exprs.size
    all_goals aesop (add simp CacheExpr.wellFormed.eq_def) (add safe (by grind))

@[simp, grind =]
lemma getElem?_pushExpr {e} {σ : HashConsSt p} {h_wellFormed} :
  (pushExpr e σ h_wellFormed).exprs[σ.exprs.size]? =
  .some e
:= by
  unfold HashConsSt.pushExpr
  simp

end Clap.HashConsSt
