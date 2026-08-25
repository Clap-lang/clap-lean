import Clap.eDSLState.HashCons.CacheExpr

namespace Clap

@[grind]
structure HashConsSt (p : ℕ) where
  exprs : Array (CacheExpr p) -- ℕ → Expr
  wellFormed : ∀ i < exprs.size, exprs[i]?.any (·.wellFormed i)

def HashConsSt.empty (p : ℕ) : HashConsSt p where
  exprs := #[]
  wellFormed := by simp

instance {p} : EmptyCollection (HashConsSt p) := ⟨HashConsSt.empty p⟩

instance {p} : Membership (CacheExpr p) (HashConsSt p) where
  mem σ x := x ∈ σ.exprs

namespace HashConsSt

@[grind =]
def size {p} (σ : HashConsSt p) : ℕ :=
  σ.exprs.size

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
  grind

@[simp, grind =]
lemma size_exprs_pushExpr {e : CacheExpr p} {σ : HashConsSt p} {h : e.wellFormed σ.size} :
  (σ.pushExpr (p := p) e h).size = σ.size + 1 := by
  grind [=pushExpr]

@[grind =]
lemma isPrefixOf_pushExpr
  {σ : HashConsSt p}
  {e : CacheExpr p}
  {h : e.wellFormed σ.size}
:
  σ.exprs.isPrefixOf (σ.pushExpr e h).exprs = true
:= by
  aesop (add simp HashConsSt.pushExpr) (add safe (by grind))

@[aesop safe, grind .]
lemma size_le_size_of_prefixOf {σ σ' : HashConsSt p} (h : σ.exprs.isPrefixOf σ'.exprs) :
  σ.size ≤ σ'.size := by
  unfold size
  set l := σ.exprs with eq_l
  set l' := σ'.exprs with eq_l'
  rcases l with ⟨l⟩
  rcases l' with ⟨l'⟩
  simp at *
  grind

end Clap.HashConsSt
