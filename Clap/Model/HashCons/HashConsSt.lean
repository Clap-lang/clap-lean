import Clap.Model.HashCons.CacheExpr
import Std.Data.ExtHashMap

namespace Clap

/-- The expression heap. `index` gives each node's position in `exprs` (the first one, as
`Array.idxOf`), so that compiled code finds a node without searching `exprs`: see
`HashConsM.saveExpr_eq_saveExprFast`. -/
@[grind]
structure HashConsSt (p : ℕ) where
  exprs : Array (CacheExpr p) -- ℕ → Expr
  wellFormed : ∀ i < exprs.size, exprs[i]?.any (·.wellFormed i)
  index : Std.ExtHashMap (CacheExpr p) ExprRef
  index_spec : ∀ e, index[e]? = if e ∈ exprs then some (exprs.idxOf e) else none

def HashConsSt.empty (p : ℕ) : HashConsSt p where
  exprs := #[]
  wellFormed := by simp
  index := ∅
  index_spec := by simp

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

theorem ext_exprs {σ σ' : HashConsSt p} (h : σ.exprs = σ'.exprs) : σ = σ' := by
  obtain ⟨exprs, wf, index, spec⟩ := σ
  obtain ⟨exprs', wf', index', spec'⟩ := σ'
  simp only at h
  subst h
  obtain rfl : index = index' := Std.ExtHashMap.ext_getElem? fun e ↦ by rw [spec, spec']
  rfl

/-- The positions of `l`'s nodes, numbered from `start`, added to `m` for nodes it lacks. -/
def indexFrom (m : Std.ExtHashMap (CacheExpr p) ExprRef) (start : ℕ) :
    List (CacheExpr p) → Std.ExtHashMap (CacheExpr p) ExprRef
  | [] => m
  | e :: l => indexFrom (m.insertIfNew e start) (start + 1) l

theorem getElem?_indexFrom (m : Std.ExtHashMap (CacheExpr p) ExprRef) (start : ℕ)
    (l : List (CacheExpr p)) (e : CacheExpr p) :
    (indexFrom m start l)[e]? =
      match m[e]? with
      | some v => some v
      | none => if e ∈ l then some (start + l.idxOf e) else none := by
  induction l generalizing m start with
  | nil => cases h : m[e]? <;> simp [indexFrom, h]
  | cons a l ih =>
    rw [indexFrom, ih, Std.ExtHashMap.getElem?_insertIfNew]
    by_cases hae : a = e
    · subst hae
      cases h : m[a]? <;> simp [h, Std.ExtHashMap.mem_iff_isSome_getElem?]
    · have hne : (a == e) = false := by simpa using hae
      have hmem : e ∈ a :: l ↔ e ∈ l := by simp [Ne.symm hae]
      have hidx : start + (a :: l).idxOf e = start + 1 + l.idxOf e := by
        simp only [List.idxOf_cons, hne, cond_false]
        omega
      simp only [hne, Bool.false_eq_true, false_and, if_false, hmem, hidx]

/-- A heap from its nodes, with the index computed. -/
def ofExprs (exprs : Array (CacheExpr p))
    (wellFormed : ∀ i < exprs.size, exprs[i]?.any (·.wellFormed i)) : HashConsSt p where
  exprs
  wellFormed
  index := indexFrom ∅ 0 exprs.toList
  index_spec e := by
    rcases exprs with ⟨l⟩
    simp [getElem?_indexFrom]

def pushExpr
  (e : CacheExpr p)
  (σ : HashConsSt p)
  (h_wellFormed : e.wellFormed σ.size)
: HashConsSt p where
  exprs := σ.exprs.push e
  wellFormed := by
    intro i h_i
    obtain ⟨exprs, exprs_wellformed, _, _⟩ := σ
    simp at h_i
    by_cases h_eq : i = exprs.size
    all_goals aesop (add simp CacheExpr.wellFormed.eq_def) (add safe (by grind))
  index := σ.index.insertIfNew e σ.size
  index_spec e' := by
    have hmem : e ∈ σ.index ↔ e ∈ σ.exprs := by
      rw [Std.ExtHashMap.mem_iff_isSome_getElem?, σ.index_spec]
      split <;> simp_all
    simp only [Std.ExtHashMap.getElem?_insertIfNew, hmem, σ.index_spec, Array.push_eq_append,
      Array.idxOf_append, Array.mem_append]
    by_cases h : e = e'
    · subst h
      by_cases hm : e ∈ σ.exprs <;> simp [hm, size]
    · have hne : (e == e') = false := by simpa using h
      by_cases hm : e' ∈ σ.exprs <;> simp [hm, hne, Ne.symm h]

/-- `pushExpr` with the new node's index read before the push. `pushExpr` reads `σ.size` after `σ.exprs.push e`, which keeps the
array shared at the push, so the push copied the whole heap -/
def pushExprFast (e : CacheExpr p) (σ : HashConsSt p) (h_wellFormed : e.wellFormed σ.size) : HashConsSt p :=
  let n := σ.size
  { exprs := σ.exprs.push e
    wellFormed := (pushExpr e σ h_wellFormed).wellFormed
    index := σ.index.insertIfNew e n
    index_spec := (pushExpr e σ h_wellFormed).index_spec }

@[csimp]
theorem pushExpr_eq_pushExprFast : @pushExpr = @pushExprFast := rfl

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
