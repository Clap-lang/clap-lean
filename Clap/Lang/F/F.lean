import Clap.eDSLState.eDSL
import Clap.eDSLState.Convert

import Clap.Lang.Wheels

namespace Clap.Lang

abbrev F := ExprRef
abbrev FB := F
abbrev FArray (k) := Vector FB k

namespace F

variable {p : ℕ}

open HashConsM in
def eq {p : ℕ} [p.AtLeastTwo] (a b : F) : ClapM p FB := do
  isZero (←mkSub (p := p) a b)

open HashConsM in
def oneHotRaw [p.AtLeastTwo] (len : ℕ) (idx : F) : ClapM p (Vector FB len) :=
  (Vector.range len).mapM (fun (i:ℕ) ↦ do
    let idx_val ← mkConstant (p := p) i
    F.eq idx idx_val
  )

def matches_spec
  (varStore : VarStore p)
  (numAlloc : ℕ)
  (σ : HashConsSt p)
  {α}
  (cmd : ClapM p α)
  {β : Type}
  (spec : β)
  (toIdeal : VarStore p → HashConsSt p → α → Option β)
:= toIdeal
    (cmd.getVarStore varStore numAlloc σ)
    (cmd.getHashConsState numAlloc σ)
    (cmd.getResult numAlloc σ) =
    .some spec

def Converts := Clap.Converts 1 (fun x : ZMod p ↦ #v[x])
def _root_.Clap.Lang.FB.Converts := Clap.Converts 1 (fun x : Bool ↦ #v[if x then (1 : ZMod p) else 0])
def _root_.Clap.Lang.FArray.Converts (k : ℕ) := Clap.Converts k fun vec : Vector Bool k ↦
                                                  vec.map fun x ↦ if x then (1 : ZMod p) else 0

namespace eq

opaque spec {p} (a b : ZMod p) : Bool :=
  a == b

-- @[simp, grind =]
-- lemma getHashConsState_isZero_of_mem {e! : ExprRef} {numAlloc} {σ : HashConsSt p}
--   (h : .v numAlloc ∈ σ.exprs) :
--   (isZero e!).getHashConsState numAlloc σ =
--   σ := by grind

-- @[simp, grind =]
-- lemma getHashConsState_isZero_of_notMem {e! : ExprRef} {numAlloc} {σ : HashConsSt p}
--   (h : .v numAlloc ∉ σ.exprs) :
--   (isZero e!).getHashConsState numAlloc σ =
--   σ.pushExpr (.v numAlloc) (by simp) := by grind

@[aesop safe, grind .]
lemma _root_.Clap.isZero.wellFormed {e! : ExprRef} {Γ : VarStore p} {σ : HashConsSt p} {numAlloc : ℕ} {value : ZMod p}
  (h : F.Converts Γ σ numAlloc #v[e!] value)
:
  (isZero e!).wellFormed numAlloc Γ σ
:= by
  obtain ⟨h_varSet, h_wellFormed, h_result⟩ := h
  simp at *
  apply wellFormed_isZero
  . grind
  . have : [Γ|⦃e!, σ⦄].isSome = true := by grind
    grind
  . grind

@[grind =]
lemma deref_idxOf_of_mem
  {cacheExpr : CacheExpr p}
  {σ : HashConsSt p}
  (h_mem : cacheExpr ∈ σ.exprs)
:
  *⦃σ.exprs.idxOf cacheExpr, σ⦄ = cacheExpr
:= by
  grind

lemma Converts_mkSub
   {Γ : VarStore p} {σ : HashConsSt p} {numAlloc : ℕ}
   {a b : ExprRef}
   {a_val b_val : ZMod p}
   (h_a : F.Converts Γ σ numAlloc #v[a] a_val)
   (h_b : F.Converts Γ σ numAlloc #v[b] b_val)
:
  F.Converts
    (ClapM.getVarStore (liftM (HashConsM.mkSub (p := p) a b)) Γ numAlloc σ)
    (ClapM.getHashConsState (liftM (HashConsM.mkSub (p := p) a b)) numAlloc σ)
    (ClapM.getNumAlloc (liftM (HashConsM.mkSub (p := p) a b)) numAlloc σ)
    #v[ClapM.getResult (liftM (HashConsM.mkSub (p := p) a b)) numAlloc σ]
    (a_val - b_val)
:= by
  simp
  obtain ⟨a_varSet, a_wellFormed, a_result⟩ := h_a
  obtain ⟨b_varSet, b_wellFormed, b_result⟩ := h_b
  constructor <;>
  simp at *
  . grind [=Expr.varSet_wellFormed]
  . grind
  . simp [HashConsM.mkSub]
    rewrite [HashConsM.getResult_saveExpr_of_wellFormed]
    . rewrite [HashConsM.getHashConsState_saveExpr_of_wellFormed (by grind)]
      . split <;> rewrite [eval_eq_evalRec (by grind)]
        . rewrite [evalRec_eq_of_deref_eq_some_sub (deref_idxOf_of_mem (by assumption))]
          dsimp
          rewrite [
            ←eval_eq_evalRec (by grind),
            ←eval_eq_evalRec (by grind),
            a_result,
            b_result
          ]
          rfl
        . rewrite [evalRec_eq_of_deref_eq_some_sub (Expr.deref_mk_size_push)]
          dsimp
          rewrite [
            ←evalRec_of_wellFormed_of_prefix (σ := σ) (by grind) (by grind),
            ←evalRec_of_wellFormed_of_prefix (σ := σ) (σ' := HashConsSt.pushExpr _ _ _) (by grind) (by grind),
            ←eval_eq_evalRec (by grind),
            ←eval_eq_evalRec (by grind),
            a_result,
            b_result
          ]
          rfl
    . grind


#check evalRec_isSome_iff
#check wellFormed_mem_varStore_of_evalRec_eq_some
/--
TODO: This used to be just grind :eyes:.
-/
lemma wellFormed
  [p.AtLeastTwo]
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {a b : F} {_a' _b' : ZMod p}
  (h_a : F.Converts varStore σ numAlloc #v[a] _a')
  (h_b : F.Converts varStore σ numAlloc #v[b] _b')
:
  (eq a b).wellFormed numAlloc varStore σ
:= by
  unfold eq
  apply Clap.ClapM.bind_wellFormed
  · apply ClapM.wellFormed_liftM_of_hashConsM_wellFormed
    apply HashConsM.wellFormed_mkSub
  · apply isZero.wellFormed
    · exact Converts_mkSub h_a h_b

@[simp, grind =]
lemma deref_mkVar_eq_some
  {idx : ℕ}
  {σ : HashConsSt p}
:
  *⦃(HashConsM.mkVar idx).getResult σ, (HashConsM.mkVar idx).getHashConsState σ⦄ =
  .some (CacheExpr.v idx)
:= by
  grind [=HashConsM.mkVar]

@[simp, grind =]
lemma varSet_mkVar
  {idx : ℕ}
  {σ : HashConsSt p}
:
  ⦃(HashConsM.mkVar idx).getResult σ, (HashConsM.mkVar idx).getHashConsState σ⦄.varSet =
  {idx}
:= by
  unfold Expr.varSet
  grind

@[simp, grind! .]
lemma lt_getNumAlloc_isZero
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {a : ExprRef}
:
  numAlloc < (isZero a).getNumAlloc numAlloc σ
:= by
  simp [isZero]

lemma Converts_isZero
  [p.AtLeastTwo]
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {a : F}
  {a_val : ZMod p}
  (h_a : F.Converts varStore σ numAlloc #v[a] a_val)
:
  FB.Converts
    ((isZero a).getVarStore varStore numAlloc σ)
    ((isZero a).getHashConsState numAlloc σ)
    ((isZero a).getNumAlloc numAlloc σ)
    #v[(isZero a).getResult numAlloc σ]
    (a_val == 0)
:= by
  obtain ⟨a_varSet, a_wellFormed, a_result⟩ := h_a
  constructor <;> simp at *
  . intro i h_i
    grind [=isZero]
  . simp [isZero]
    rw [Expr.wellFormed_iff_isSome, deref_mkVar_eq_some]
    rfl
  . simp [isZero, HashConsM.mkVar]
    simp [HashConsM.getHashConsState_saveExpr_of_wellFormed,
          HashConsM.getResult_saveExpr_of_wellFormed]
    split
    · rw [eval_eq_evalRec (by grind)]
      unfold Expr.evalRec
      grind
    · rw [eval_eq_evalRec (by grind)]
      rw [evalRec_eq_of_deref_eq_some_v (idx := numAlloc)]
      · simp
        rw [eval_eq_evalRec (by grind)] at a_result ⊢ 
        rw [←evalRec_of_wellFormed_of_prefix] at ⊢
        · rw [a_result]
          grind
        · grind
        · grind
      · grind

lemma _root_.Clap.FB.converts_of_converts_eq {Γ : VarStore p} {σ : HashConsSt p} {numAlloc : ℕ}
                                             {expr : Vector FB 1} {value₁ : Bool}
                                             (value₂ : Bool) (h : value₁ = value₂) :
  FB.Converts Γ σ numAlloc expr value₁ ↔ FB.Converts Γ σ numAlloc expr value₂ := by
  grind

lemma Converts_eq
  [p.AtLeastTwo]
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {a b : F}
  {a_val b_val : ZMod p}
  (h_a : F.Converts varStore σ numAlloc #v[a] a_val)
  (h_b : F.Converts varStore σ numAlloc #v[b] b_val)
:
  FB.Converts
    ((eq a b).getVarStore varStore numAlloc σ)
    ((eq a b).getHashConsState numAlloc σ)
    ((eq a b).getNumAlloc numAlloc σ)
    #v[(eq a b).getResult numAlloc σ]
    (a_val == b_val)
:= by
  rw [FB.converts_of_converts_eq (a_val - b_val == 0) (by grind)]
  unfold eq
  simp
  rw [ClapM.getVarStore_bind_of_wellFormed]
  · aesop
      (erase simp [getResult_liftM,
                   ClapM.getResult_liftM,
                   ClapM.getVarStore_liftM,
                   ClapM.getNumAlloc_liftM,
                   ClapM.getHashConsState_liftM,
                   getVarStore_isZero])
      (add safe apply [Converts_isZero, Converts_mkSub])
    grind [!.Converts_isZero, .Converts_mkSub]
  · grind
  · apply isZero.wellFormed
    apply Converts_mkSub h_a h_b

#exit
#exit
#exot



  -- apply Clap.ClapM.bind_wellFormed
  -- · grind
  -- . rcases h_a with ⟨h₁, h₂, h₃⟩
  --   rcases h_b with ⟨h₄, h₅, h₆⟩
  --   simp
  --   apply wellFormed_isZero
  --   · simp at *
  --     grind
  --   · simp at *
  --     intros val hval
  --     rw [Std.ExtTreeMap.mem_iff_isSome_getElem?]
  --     -- rw [eval_eq_evalRec (by grind)] at h₃ h₆
  --     have : [varStore | ⦃a[0], σ⦄].isSome := by grind
  --     have : [varStore | ⦃b[0], σ⦄].isSome := by grind
  --     grind -- `Option.isSome_of_eq_some` is useless, had to go via `wellFormed_mem_varStore_of_evalRec_eq_some`... yikes?
  --   · simp at *
  --     grind [=Expr.varSet_wellFormed]

lemma matches_spec
  [p.AtLeastTwo]
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  (a b : F)
  (a_val b_val : ZMod p)
  (h_a_wf_σ : (Expr.mk a σ).wellFormed)
  (h_b_wf_σ : (Expr.mk b σ).wellFormed)
  (h_a_wf : [varStore|Expr.mk a σ].isSome = true)
  (h_a_val : [varStore,σ|a].get h_a_wf = a_val)
  (h_b_wf : [varStore|Expr.mk b σ].isSome = true)
  (h_b_val : [varStore,σ|b].get h_b_wf = b_val)
  -- (h_σ_a : Expr.varSet_wellFormed ⟨a, σ⟩ numAlloc)
  -- (h_σ_b : Expr.varSet_wellFormed ⟨b, σ⟩ numAlloc)
:
  F.matches_spec
    varStore
    numAlloc
    σ
    (eq a b)
    (a_val == b_val)
    FB.Convert.toIdeal
:= by
  dsimp [F.matches_spec]
  set aExpr : Expr _ := ⟨a, σ⟩
  have : aExpr.wellFormed := by grind

  set bExpr : Expr _ := ⟨b, σ⟩
  have : bExpr.wellFormed := by grind

  set subCExpr : CacheExpr p := .binary_op (p := p) a b .sub
  have subCExprWf : subCExpr.wellFormed σ.size := by grind

  set f := a.eq b (p := p) with hf

  have : f.getCircuit numAlloc σ = #[Gate.isZero (σ.exprs.idxOf subCExpr)] := by
    grind [eq]

  set σ₁ := (HashConsM.mkSub a b).getHashConsState σ with eq_σ₁
  have eq₁ : subCExpr ∈ σ₁.exprs := by grind
  set σ₂ := f.getHashConsState numAlloc σ with eq_σ₂
  have eq₃ : subCExpr ∈ σ₂.exprs := by grind [=eq]
  have eq₄ : .v numAlloc ∈ σ₂.exprs := by grind [=eq]
  have : f.getResult numAlloc σ = (HashConsM.mkVar numAlloc).getResult σ₁ := by
    grind [=eq]
  rw [this]
  let res₀ := (HashConsM.mkSub a b).getResult σ
  set res₁ := (HashConsM.mkVar numAlloc).getResult σ₁ with eq_res₁
  let res₀_val := [varStore| ⦃res₀, (HashConsM.mkVar numAlloc).getHashConsState σ₁⦄]
  have : f.getVarStore varStore numAlloc σ =
         varStore.insert numAlloc (if res₀_val = some 0 then 1 else 0) := by
    rw [hf]
    unfold eq
    rw [ClapM.getVarStore_bind_of_wellFormed (by simp)]
    swap
    simp
    apply wellFormed_isZero (by grind) (by grind)
    swap
    simp [res₀_val, res₀, eq_σ₁]

  sorry

end eq

namespace oneHotRaw

def spec (len : ℕ) (idx : ℕ) : Vector Bool len :=
  (Vector.range len).map (fun (i:ℕ) ↦ idx == i)

opaque Convert.toIdeal {len : ℕ} (varStore : VarStore p) (σ : HashConsSt p) (result : Vector FB len) : Option (Vector Bool len)

lemma Convert.toIdeal_push
  {len : ℕ} {vec : Vector Bool len} {extra : FB} {val : Bool}
  {varStore : VarStore p}
  {σ : HashConsSt p}
  {result : Vector FB len}
  (h_base : Convert.toIdeal varStore σ result = .some vec)
  (h_extra : FB.Convert.toIdeal varStore σ extra = .some val)
:
  Convert.toIdeal varStore σ (result.push extra) = .some (vec.push val)
:= by
  done

-- lemma Vector.mapM_append {p} {α β} {n} {n'}
--     {f : α → ClapM p β} {xs : Vector α n} :
--     xs.mapM f =
--     (λ numAlloc σ => (((), ), ))
-- := by
--   done

@[simp, grind =]
lemma _root_.Clap.ClapM.Vector.mapM_singleton
  {α}
  {len : α}
  (f : α → ClapM p FB)
:
  #v[len].mapM f =
  f len >>= fun x => pure #v[x]
:= by
  unfold Vector.mapM
  cbv
  simp [WriterT.run]
  funext
  simp [StateT.bind]
  cbv

@[grind .]
lemma getVarStore_precedes_of_wellFormed
  {α}
  {Γ : VarStore p}
  {numAlloc : ℕ}
  {σ σ': HashConsSt p}
  {action : ClapM p α}
:
  [σ'|Γ ⊑ action.getVarStore Γ numAlloc σ]
:= by
  unfold ClapM.getVarStore
  grind

lemma wellFormed
  [p.AtLeastTwo]
  {len : ℕ}
  {idx : F}
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {idx_val : ℕ}
  (h_idx_val : (F.Convert.toIdeal varStore σ idx).map ZMod.val = .some idx_val)
  (h_idx_varSet : Expr.varSet_wellFormed ⟨idx, σ⟩ numAlloc)
:
  (oneHotRaw len idx).wellFormed numAlloc varStore σ
:= by
  have h_isSome : (F.Convert.toIdeal varStore σ idx).isSome = true := by grind
  induction' len with len h_len
  . have : Vector.range 0 = #v[] := rfl
    simp [oneHotRaw, this]
  . have :
      oneHotRaw (len + 1) idx =
      do
        let vec ← oneHotRaw len idx
        let idx_val ← liftM (HashConsM.mkConstant (p := p) len)
        let elem ← F.eq (p := p) idx idx_val
        return vec.push elem
    := by
      simp [oneHotRaw, Vector.range_succ, Vector.mapM_append, -Vector.append_singleton]
      set v := Vector.mapM
          (fun i => do
            let idx_val ← liftM (HashConsM.mkConstant (i : ZMod p))
            idx.eq (p := p) idx_val)
          (Vector.range len)
      simp
    simp [this]
    apply ClapM.bind_wellFormed (by grind)
    apply ClapM.bind_wellFormed
    . grind
    . apply eq.wellFormed <;> simp
      . have h_lt: idx < σ.size := by grind [wellFormed_of_toIdeal_isSome]
        have h_le : σ.size ≤ ((oneHotRaw len idx).getHashConsState numAlloc σ).size := by grind
        apply lt_of_lt_of_le (lt_of_lt_of_le h_lt h_le)
        rewrite [HashConsM.getHashConsState_mkConstant]
        grind
      . grind [HashConsM.getResult_lt_getHashConsState_size_mkConstant] -- grind why
      . rewrite [←ClapM.getVarStore]
        have := isSome_eval_of_isSome_toIdeal h_isSome
        apply isSome_eval_of_isSome_eval_precedes (Γ₁ := varStore)
        . apply isSome_eval_of_prefix _ this
          . grind
          . grind
          . exact wellFormed_of_toIdeal_isSome h_isSome
        . have := wellFormed_of_toIdeal_isSome h_isSome
          grind
        . simp
          grind
      . unfold Expr.varSet_wellFormed
        rewrite [varSet.varSet_mk_eq_of_prefix (σ1 := σ)]
        . grind
        . grind [wellFormed_of_toIdeal_isSome]
        . apply Array.isPrefixOf_trans h_len.2.2
          apply HashConsM.wellFormed_mkConstant
      . grind [Expr.varSet_wellFormed]

--TODO prove using eq.matches_spec
--this may require adding to F.matches_spec, or defining properties about Convert.toIdeal
--in either case, the goal is to reach a fixed point where the same properties are known about the two Convert.toIdeal functions,
--and the same F.matches_spec is being used for eq and proven for oneHotRaw
lemma matches_spec
  [p.AtLeastTwo]
  {len : ℕ}
  {idx : F}
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  {idx_val : ℕ}
  (h_idx_val : F.Convert.toIdeal varStore σ idx idx_val)
  (h_idx_varSet : Expr.varSet_wellFormed ⟨idx, σ⟩ numAlloc)
:
  F.matches_spec
    varStore
    numAlloc
    σ
    (oneHotRaw len idx)
    (spec len idx_val)
    Convert.toIdeal
:= by
  unfold F.matches_spec
  set f := oneHotRaw len idx (p := p) with eq
  unfold oneHotRaw at eq
  set range_vec := Vector.range len
  induction' len with len ih
  · have : Vector.range 0 = #v[] := rfl
    simp [this, range_vec] at eq
    subst f
    simp [eq]
    unfold spec
    simp [this]
    have todoLater₁ : Convert.toIdeal varStore σ #v[] = some #v[] := sorry
    exact todoLater₁
  · simp at ih
    specialize ih (by rfl)
    have :
      oneHotRaw (len + 1) idx =
      do
        let vec ← oneHotRaw len idx
        let idx_val ← liftM (HashConsM.mkConstant (p := p) len)
        let elem ← F.eq (p := p) idx idx_val
        return vec.push elem
    := by
      simp [oneHotRaw, Vector.range_succ, Vector.mapM_append, -Vector.append_singleton]
      set v := Vector.mapM
          (fun i => do
            let idx_val ← liftM (HashConsM.mkConstant (i : ZMod p))
            idx.eq (p := p) idx_val)
          (Vector.range len)
      simp
    unfold oneHotRaw at this
    simp [range_vec, this] at eq
    rewrite [←oneHotRaw.eq_def] at eq
    have : spec (len + 1) idx_val = spec len idx_val ++ #v[idx_val == len] := by
      unfold spec
      simp [Vector.range_succ]
    rw [this]
    have :
      Convert.toIdeal
        (f.getVarStore varStore numAlloc σ)
        (f.getHashConsState numAlloc σ)
        (f.getResult numAlloc σ) =
      (Convert.toIdeal
        ((oneHotRaw len idx).getVarStore varStore numAlloc σ)
        ((oneHotRaw len idx).getHashConsState numAlloc σ)
        ((oneHotRaw len idx).getResult numAlloc σ)).get (by grind) ++
      #v[(F.Convert.toIdeal
          ((oneHotRaw len idx).getVarStore varStore numAlloc σ)
          ((oneHotRaw len idx).getHashConsState numAlloc σ)
          idx).map (ZMod.val) == .some len
      ]
    := by
      simp [ih]
      have :
        f.getResult numAlloc σ =
        ((oneHotRaw len idx).getResult numAlloc σ).push
          ((idx.eq ((HashConsM.mkConstant (len : ZMod p)).getResult ((oneHotRaw len idx).getHashConsState numAlloc σ))).getResult
          ((oneHotRaw len idx).getNumAlloc numAlloc σ)
          ((HashConsM.mkConstant (len : ZMod p)).getHashConsState ((oneHotRaw len idx).getHashConsState numAlloc σ)))
      := by
        simp [eq]
      rewrite [this]; clear this
      rewrite [Convert.toIdeal_push]
      . rfl
      . simp [eq]
        rewrite [ClapM.getVarStore_bind_of_wellFormed (wellFormed h_idx_val h_idx_varSet)]
        . done
        . apply ClapM.bind_wellFormed
          . grind
          . simp
            apply F.eq.wellFormed
            . have h_toIdeal : (F.Convert.toIdeal varStore σ idx).isSome = true := by aesop
              have := wellFormed_of_toIdeal_isSome h_toIdeal

              done
          done
        done
      done

    simp [this, ih]
    rewrite [toIdeal_eq_toIdeal_of_wellFormed, h_idx_val]
    . aesop
    . apply wellFormed_of_toIdeal_isSome (varStore := varStore)
      grind
    . grind
    . exact wellFormed h_idx_val h_idx_varSet
  done

end oneHotRaw

end F

end Clap.Lang
