import Clap.eDSLState.eDSL
import Clap.eDSLState.IsValid

import Clap.Lang.Wheels

namespace Clap.Lang

abbrev F := ExprRef -- TODO Expr or ExprRef?
abbrev FB := F

namespace F

variable {p : ℕ}

instance : IsValid p F where
  isValid Γ σ x := [Γ,σ|x].isSome = true

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
    (cmd.getResult numAlloc σ) = .some spec

opaque F.Convert.toIdeal (varStore : VarStore p) (σ : HashConsSt p) (result : F) : Option (ZMod p)

lemma wellFormed_of_toIdeal_isSome
  {varStore : VarStore p} {σ} {result}
  (h : (F.Convert.toIdeal varStore σ result).isSome = true)
:
  (Expr.mk result σ).wellFormed
:= by

  done

lemma isSome_eval_of_isSome_toIdeal
  {Γ :VarStore p} {σ : HashConsSt p} {result : F}
  (h : (F.Convert.toIdeal Γ σ result).isSome = true)
:
  [Γ, σ|result].isSome = true
:= by
  done

lemma toIdeal_eq_toIdeal_of_wellFormed
  {x : F}
  {α}
  {a : ClapM p α}
  {varStore : VarStore p}
  {numAlloc}
  {σ}
  (h_wf : (Expr.mk x σ).wellFormed)
  (h_varset : Expr.varSet_wellFormed ⟨x, σ⟩ numAlloc)
  (h_varStore : a.wellFormed numAlloc varStore σ)
:
  F.Convert.toIdeal (a.getVarStore varStore numAlloc σ) (a.getHashConsState numAlloc σ) x =
  F.Convert.toIdeal varStore σ x
:= by
  done


opaque FB.Convert.toIdeal (varStore : VarStore p) (σ : HashConsSt p) (result : FB) : Option Bool

namespace eq

opaque spec {p} (a b : ZMod p) : Bool :=
  a == b

@[simp, grind =]
lemma getCircuit_isZero {e! : ExprRef} {numAlloc} {σ : HashConsSt p} :
  (isZero e!).getCircuit numAlloc σ = #[.isZero e!] := by
  simp [isZero]

@[simp, grind =]
lemma getCircuit_eq0 {e! : ExprRef} {numAlloc} {σ : HashConsSt p} :
  (eq0 e!).getCircuit numAlloc σ = #[.eq0 e!] := by
  simp [eq0]

@[simp, grind =]
lemma getCircuit_share {e! : ExprRef} {numAlloc} {σ : HashConsSt p} :
  (share e!).getCircuit numAlloc σ = #[.share e!] := by
  simp [share]

@[simp, grind =]
lemma getCircuit_num2bits {w : ℕ} {e! : ExprRef} {numAlloc} {σ : HashConsSt p} :
  (num2bits w e!).getCircuit numAlloc σ = #[.num2bits w e!] := by
  simp [num2bits]

@[simp, grind =]
lemma getResult_liftM {α} {action : HashConsM p α} {numAlloc} {σ : HashConsSt p} :
  (liftM (m := HashConsM p) (n := ClapM p) action).getResult numAlloc σ = action.getResult σ := rfl

@[simp, grind =]
lemma getHashConsState_isZero {e! : ExprRef} {numAlloc} {σ : HashConsSt p} :
  (isZero e!).getHashConsState numAlloc σ =
  if .v numAlloc ∈ σ.exprs
  then σ
  else σ.pushExpr (.v numAlloc) (by simp) := by
  grind [isZero]

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

@[simp, grind .]
lemma wellFormed_pure {α} {action : α} {numAlloc} {varStore : VarStore p} {σ : HashConsSt p}:
  (pure (f := ClapM p) action).wellFormed numAlloc varStore σ := by
  grind

lemma wellFormed
  [p.AtLeastTwo]
  {varStore : VarStore p}
  {numAlloc : ℕ}
  {σ : HashConsSt p}
  (a b : F)
  (h_a_wf_σ : a < σ.size)
  (h_b_wf_σ : b < σ.size)
  (h_a_wf : [varStore|Expr.mk a σ].isSome = true)
  (h_a_varSet_wf : Expr.varSet_wellFormed ⟨a, σ⟩ numAlloc)
  (h_b_wf : [varStore|Expr.mk b σ].isSome = true)
  (h_b_varSet_wf : Expr.varSet_wellFormed ⟨b, σ⟩ numAlloc)
:
  (eq a b).wellFormed numAlloc varStore σ
:= by
  unfold eq
  apply Clap.ClapM.bind_wellFormed
  · simp_all only [HashConsM.wellFormed_mkSub, ClapM.wellFormed_of_hashConsM_wellFormed]
  . grind [Expr.varSet_wellFormed, Expr.wellFormed]

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

#exit

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
        aesop
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
      . grind

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
