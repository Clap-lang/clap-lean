import Clap.Model.Ref.ToCs

/-!
A proof that the old HashConsSt (now called HashConsStRef) and the new HashConsSt with an index are "the same"

* forgetting the index is a bijection, `HashConsSt.equivRef : HashConsSt p ≃ HashConsStRef p`
  (the index is determined by `exprs`: `HashConsSt.ext_exprs`);
* every changed definition commutes with it: `toRef_empty`, `toRef_pushExpr`, `toRef_ofExprs`,
  `run_saveExpr_toRef`, `toRef_remapVars`, `toRef_offsetHashConsStateRef`;
* so does the code that compiled code runs in their place (`@[csimp]`): `run_saveExprFast_toRef`,
  `toRef_pushExprFast`.

Every other heap definition reads only `exprs` (and `wellFormed`), and none of them changed: only
`empty`, `ofExprs`, `pushExpr`, `pushExprFast` and `saveExprFast` mention `index`.
-/

namespace Clap

@[grind]
structure HashConsStRef (p : ℕ) where
  exprs : Array (CacheExpr p) -- ℕ → Expr
  wellFormed : ∀ i < exprs.size, exprs[i]?.any (·.wellFormed i)

namespace HashConsStRef

variable {p : ℕ}

/-- `HashConsSt.empty` at d155481. -/
def empty (p : ℕ) : HashConsStRef p where
  exprs := #[]
  wellFormed := by simp

/-- `HashConsSt.size` (unchanged). -/
@[grind =]
def size (σ : HashConsStRef p) : ℕ :=
  σ.exprs.size

/-- `HashConsSt.pushExpr` at d155481. -/
def pushExpr
  (e : CacheExpr p)
  (σ : HashConsStRef p)
  (h_wellFormed : e.wellFormed σ.size)
: HashConsStRef p where
  exprs := σ.exprs.push e
  wellFormed := by
    intro i h_i
    obtain ⟨exprs, exprs_wellformed⟩ := σ
    simp at h_i
    by_cases h_eq : i = exprs.size
    all_goals aesop (add simp CacheExpr.wellFormed.eq_def) (add safe (by grind))

/-- `HashConsM.saveExpr` at d155481, on the heap without the index. -/
def saveExpr (e : CacheExpr p) : StateM (HashConsStRef p) ExprRef := do
  let state ← get
  if e ∈ state.exprs then
    return state.exprs.idxOf e
  else if h : e.wellFormed state.size then
    let post_state := state.pushExpr e h
    set post_state
    return state.size
  else pure 42

/-- `ConstraintSystem.offsetHashConsState` at d155481, with its offsets `offsetIdx circuit` taken
as an argument. -/
def remapVars (offsets : ℕ → ℕ) (numPublicInputs : ℕ) (σ : HashConsStRef p) : HashConsStRef p :=
  let exprs := σ.exprs.map (λ cacheExpr => match cacheExpr with
    | .c x=> .c x
    | .v x => .v (if x < numPublicInputs then x else numPublicInputs + offsets (x - numPublicInputs))
    | .binary_op lhs rhs op => .binary_op lhs rhs op
  )
  let wellFormed := by
    intro i h_i
    obtain ⟨_, h_wellFormed⟩ := σ
    specialize h_wellFormed i (by grind)
    grind
  ⟨exprs, wellFormed⟩

/-- `ConstraintSystem.offsetHashConsState` at d155481. Its `offsetIdx` is
`ConstraintSystem.offsetIdxRef` now. -/
def offsetHashConsState (numPublicInputs : ℕ) (σ : HashConsStRef p) (circuit : Circuit) :
    HashConsStRef p :=
  remapVars (ConstraintSystem.offsetIdxRef circuit) numPublicInputs σ

/-- The heap with its index. -/
def toSt (σ : HashConsStRef p) : HashConsSt p :=
  HashConsSt.ofExprs σ.exprs σ.wellFormed

end HashConsStRef

namespace HashConsSt

variable {p : ℕ}

/-- The heap without its index. -/
def toRef (σ : HashConsSt p) : HashConsStRef p :=
  ⟨σ.exprs, σ.wellFormed⟩

/-- The index adds nothing: heaps with an index are heaps without one. -/
def equivRef : HashConsSt p ≃ HashConsStRef p where
  toFun := toRef
  invFun := HashConsStRef.toSt
  left_inv _ := ext_exprs rfl
  right_inv _ := rfl

theorem toRef_injective : Function.Injective (toRef (p := p)) :=
  equivRef.injective

@[simp]
theorem toRef_exprs (σ : HashConsSt p) : σ.toRef.exprs = σ.exprs := rfl

@[simp]
theorem toRef_size (σ : HashConsSt p) : σ.toRef.size = σ.size := rfl

@[simp]
theorem toRef_toSt (σ : HashConsStRef p) : σ.toSt.toRef = σ := rfl

@[simp]
theorem toSt_toRef (σ : HashConsSt p) : σ.toRef.toSt = σ :=
  equivRef.left_inv σ

theorem toRef_empty : (HashConsSt.empty p).toRef = HashConsStRef.empty p := rfl

theorem toRef_emptyCollection : (∅ : HashConsSt p).toRef = HashConsStRef.empty p := rfl

/-- `ofExprs` replaced the anonymous constructor `⟨exprs, wellFormed⟩`. -/
theorem toRef_ofExprs (exprs : Array (CacheExpr p))
    (wellFormed : ∀ i < exprs.size, exprs[i]?.any (·.wellFormed i)) :
    (ofExprs exprs wellFormed).toRef = ⟨exprs, wellFormed⟩ := rfl

theorem toRef_pushExpr (e : CacheExpr p) (σ : HashConsSt p) (h : e.wellFormed σ.size) :
    (σ.pushExpr e h).toRef = σ.toRef.pushExpr e h := rfl

/-- The compiled `pushExpr` (`pushExpr_eq_pushExprFast`). -/
theorem toRef_pushExprFast (e : CacheExpr p) (σ : HashConsSt p) (h : e.wellFormed σ.size) :
    (σ.pushExprFast e h).toRef = σ.toRef.pushExpr e h := by
  rw [← pushExpr_eq_pushExprFast]
  rfl

end HashConsSt

namespace HashConsStRef

variable {p : ℕ}

/-- `saveExpr` on the indexed heap is `saveExpr` at d155481: same reference, same heap. -/
theorem run_saveExpr_toRef (e : CacheExpr p) (σ : HashConsSt p) :
    Prod.map id HashConsSt.toRef (HashConsM.run (HashConsM.saveExpr e) σ) =
      (saveExpr e).run σ.toRef := by
  by_cases h₁ : e ∈ σ.exprs
  · rw [HashConsM.run_saveExpr_of_mem (σ := σ) h₁]
    simp [saveExpr, h₁]
    rfl
  · by_cases h₂ : e.wellFormed σ.size
    · rw [HashConsM.run_saveExpr_of_notMem_wellFormed (σ := σ) h₁ h₂]
      simp [saveExpr, h₁, h₂]
      rfl
    · have h : HashConsM.run (HashConsM.saveExpr e) σ = (42, σ) := by
        unfold HashConsM.saveExpr HashConsM.run
        grind
      rw [h]
      simp [saveExpr, h₁, h₂]
      rfl

/-- The compiled `saveExpr` (`saveExpr_eq_saveExprFast`) is `saveExpr` at d155481. -/
theorem run_saveExprFast_toRef (e : CacheExpr p) (σ : HashConsSt p) :
    Prod.map id HashConsSt.toRef (HashConsM.run (HashConsM.saveExprFast e) σ) =
      (saveExpr e).run σ.toRef := by
  rw [← HashConsM.saveExpr_eq_saveExprFast]
  exact run_saveExpr_toRef e σ

/-- The remap with `ofExprs` is the remap at d155481. -/
theorem toRef_remapVars (offsets : ℕ → ℕ) (numPublicInputs : ℕ) (σ : HashConsSt p) :
    (ConstraintSystem.remapVars offsets numPublicInputs σ).toRef =
      remapVars offsets numPublicInputs σ.toRef := rfl

/-- `offsetHashConsStateRef` (the closure-chain remap) is `offsetHashConsState` at d155481. -/
theorem toRef_offsetHashConsStateRef (numPublicInputs : ℕ) (σ : HashConsSt p)
    (circuit : Circuit) :
    (ConstraintSystem.offsetHashConsStateRef numPublicInputs σ circuit).toRef =
      offsetHashConsState numPublicInputs σ.toRef circuit := rfl

/-- The current remap is `offsetHashConsState` at d155481 on circuits without fpmul (with fpmul
the old remap was wrong: see `ConstraintSystem.offsetIdx_eq_offsetIdxRef`). -/
theorem toRef_offsetHashConsState (numPublicInputs : ℕ) (σ : HashConsSt p) (circuit : Circuit)
    (h : ∀ gate ∈ circuit, (gate matches .fpmul ..) = false) :
    (ConstraintSystem.offsetHashConsState numPublicInputs σ circuit).toRef =
      offsetHashConsState numPublicInputs σ.toRef circuit := by
  rw [ConstraintSystem.offsetHashConsState_eq_offsetHashConsStateRef numPublicInputs σ circuit h]
  rfl

end HashConsStRef

end Clap
