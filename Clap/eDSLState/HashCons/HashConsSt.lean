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

instance {p} : Membership (CacheExpr p) (HashConsSt p) where
  mem σ x := x ∈ σ.exprs

variable {p : ℕ}

@[grind =]
lemma mem_def {x} {σ : HashConsSt p} : x ∈ σ ↔ x ∈ σ.exprs := by rfl

def pushExpr
  (e : CacheExpr p)
  (σ : HashConsSt p)
  (h_wellFormed : e.wellFormed σ.size)
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
  (pushExpr e σ h_wellFormed).exprs[σ.size]? =
  .some e
:= by
  unfold HashConsSt.pushExpr
  simp

@[simp, grind =]
lemma size_exprs_pushExpr {e} {σ : HashConsSt p} {h} :
  (σ.pushExpr (p := p) e h).size = σ.size + 1 := by
  simp [pushExpr]

end Clap.HashConsSt
